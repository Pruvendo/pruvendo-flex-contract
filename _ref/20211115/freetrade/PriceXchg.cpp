/** \file
 *  \brief PriceXchg contract implementation.
 *  Contract for trading price for tip3/tip3 exchange.
 *  First tip3 in a pair is major and terms "sell", "buy", "amount" are related to the first tip3 in pair.
 *  Second tip3 is called "minor".
 *  \author Andrew Zhogin
 *  \copyright 2019-2021 (c) TON LABS
 */

#include "PriceXchg.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;

#ifndef TIP3_WALLET_CODE_HASH
#error "Macros TIP3_WALLET_CODE_HASH must be defined (code hash of FlexWallet)"
#endif

#ifndef TIP3_WALLET_CODE_DEPTH
#error "Macros TIP3_WALLET_CODE_DEPTH must be defined (code depth of FlexWallet)"
#endif

static constexpr unsigned ok = 0;
struct ec : tvm::error_code {
  static constexpr unsigned out_of_tons                    = 100; ///< Partially processed because out of tons
  static constexpr unsigned deals_limit                    = 101; ///< Partially processed because deals limit
  static constexpr unsigned not_enough_tons_to_process     = 102; ///< Not enough native funds to process (crystals)
  static constexpr unsigned not_enough_tokens_amount       = 103; ///< Not enough tokens amount
  static constexpr unsigned too_big_tokens_amount          = 104; ///< Too big calculated tokens amount
  static constexpr unsigned unverified_tip3_wallet         = 105; ///< Unverified tip3 token wallet
  static constexpr unsigned canceled                       = 106; ///< Order is canceled
  static constexpr unsigned expired                        = 107; ///< Order is expired
};

/// \brief Safe delay period for lend ownership.
/// For tip3 we have lend_finish_time, when wallet ownership will return back to its original owner.
/// And we need some safe period to not process orders with soon expiring tip3 ownership.
static constexpr unsigned safe_delay_period = 5 * 60;

__always_inline
bool is_active_time(uint32 order_finish_time) {
  return tvm_now() + safe_delay_period < order_finish_time.get();
}

/// Calculate cost (amount of minor tip3 tokens to match the "amount" of major tip3 tokens)
__always_inline
std::optional<uint128> minor_cost(uint128 amount, price_t price) {
  unsigned cost = __builtin_tvm_muldivr(amount.get(), price.numerator().get(), price.denominator().get());
  if ((cost >> 128) || (cost == 0))
    return {};
  return uint128{cost};
}

/// Class for processing orders queues and performing deals
class dealer {
public:
  /// Returns tuple (sell_out_of_tons, buy_out_of_tons, deal_amount).
  /// Modifies `sell` and `buy` by ref.
  __always_inline
  std::tuple<bool, bool, uint128> make_deal(OrderInfoXchg& sell, OrderInfoXchg& buy) {
    auto deal_amount = std::min(sell.amount, buy.amount);

    bool_t last_tip3_sell{sell.amount == deal_amount};
    bool_t last_tip3_buy{buy.amount == deal_amount};

    auto buy_payment = minor_cost(deal_amount, price_);
    // it is unlikely here, because (amount * price) calculation is performed before for initial order
    // so just removing both orders from queues with 'out_of_tons' reason
    if (!buy_payment)
      return {true, true, uint128(0)};

    // Smaller pays for tip3 transfer
    //  (if seller provides big sell order, he will not pay for each small transfer)
    uint128 sell_ton_costs{0};
    uint128 buy_ton_costs{0};
    uint128 transaction_costs = tons_cfg_.transfer_tip3 * 2 + tons_cfg_.send_notify;
    if (last_tip3_sell)
      sell_ton_costs += transaction_costs;
    else
      buy_ton_costs += transaction_costs;

    bool sell_out_of_tons = (sell.account < sell_ton_costs);
    bool buy_out_of_tons = (buy.account < buy_ton_costs);
    if (sell_out_of_tons || buy_out_of_tons)
      return {sell_out_of_tons, buy_out_of_tons, uint128(0)};

    sell.amount -= deal_amount;
    buy.amount -= deal_amount;

    sell.account -= sell_ton_costs;
    buy.account -= buy_ton_costs;

    ITONTokenWalletPtr(sell.tip3_wallet_provide)(Crystals(tons_cfg_.transfer_tip3.get())).
      transfer(sell.tip3_wallet_provide, buy.tip3_wallet_receive, deal_amount, uint128(0), bool_t{false});
    ITONTokenWalletPtr(buy.tip3_wallet_provide)(Crystals(tons_cfg_.transfer_tip3.get())).
      transfer(buy.tip3_wallet_provide, sell.tip3_wallet_receive, *buy_payment, uint128(0), bool_t{false});

    notify_addr_(Crystals(tons_cfg_.send_notify.get())).
      onXchgDealCompleted(tip3root_sell_, tip3root_buy_, price_.numerator(), price_.denominator(), deal_amount);

    return {false, false, deal_amount};
  }

  __attribute__((noinline))
  static std::tuple<std::optional<OrderInfoXchgWithIdx>, big_queue<OrderInfoXchg>, uint128>
  extract_active_order(std::optional<OrderInfoXchgWithIdx> cur_order,
                       big_queue<OrderInfoXchg> orders, uint128 all_amount, bool_t sell) {
    if (cur_order)
      return {cur_order, orders, all_amount};

    while (!orders.empty()) {
      cur_order = orders.front_with_idx_opt();
      auto ord = cur_order->second;
      if (!is_active_time(ord.order_finish_time)) {
        all_amount -= ord.amount;
        OrderRet ret { uint32(ec::expired), ord.original_amount - ord.amount, uint128{0} };
        IPriceCallbackPtr(ord.client_addr)(Crystals(ord.account.get())).
          onOrderFinished(ret, sell);
        orders.pop();
        cur_order.reset();
        continue;
      }
      break;
    }
    return {cur_order, orders, all_amount};
  }

  __always_inline
  void process_queue(unsigned sell_idx, unsigned buy_idx) {
    std::optional<OrderInfoXchgWithIdx> sell_opt;
    std::optional<OrderInfoXchgWithIdx> buy_opt;

    unsigned deals_count = 0;
    while (true) {
      std::tie(sell_opt, sells_, sells_amount_) =
        extract_active_order(sell_opt, sells_, sells_amount_, bool_t{true});
      std::tie(buy_opt, buys_, buys_amount_) =
        extract_active_order(buy_opt, buys_, buys_amount_, bool_t{false});
      if (!sell_opt || !buy_opt)
        break;

      auto [sell_idx_cur, sell] = *sell_opt;
      auto [buy_idx_cur, buy] = *buy_opt;

      bool sell_out_of_tons = false;
      bool buy_out_of_tons = false;

      uint128 deal_amount{0};
      // ==== if we hit deals limit ====
      if (++deals_count > deals_limit_) {
        auto half_process_queue = tons_cfg_.process_queue / 2;
        auto safe_extra = tons_cfg_.return_ownership + tons_cfg_.order_answer;
        if (sell.account < half_process_queue + safe_extra) {
          sell_out_of_tons = true;
        }
        if (buy.account < half_process_queue + safe_extra) {
          buy_out_of_tons = true;
        }
        if (!sell_out_of_tons && !buy_out_of_tons) {
          sell.account -= half_process_queue;
          buy.account -= half_process_queue;
          IPriceXchgPtr(address{tvm_myaddr()})(Crystals(tons_cfg_.process_queue.get())).
            processQueue();
          if (sell_idx == sell_idx_cur)
            ret_ = { uint32(ec::deals_limit), sell.original_amount - sell.amount, sell.amount };
          if (buy_idx == buy_idx_cur)
            ret_ = { uint32(ec::deals_limit), buy.original_amount - buy.amount, buy.amount };
          break;
        }
      }

      // ==== make deal ====
      if (!sell_out_of_tons && !buy_out_of_tons) {
        std::tie(sell_out_of_tons, buy_out_of_tons, deal_amount) = make_deal(sell, buy);
      }

      // ==== if one of sides is out of tons ====
      if (sell_out_of_tons) {
        sells_.pop();
        OrderRet ret { uint32(ec::out_of_tons), sell.original_amount - sell.amount, uint128{0} };
        if (sell_idx == sell_idx_cur)
          ret_ = ret;
        if (sell.account > tons_cfg_.return_ownership) {
          sell.account -= tons_cfg_.return_ownership;
          ITONTokenWalletPtr(sell.tip3_wallet_provide)(Crystals(tons_cfg_.return_ownership.get())).
            returnOwnership(sell.amount);
          IPriceCallbackPtr(sell.client_addr)(Crystals(sell.account.get())).
            onOrderFinished(ret, bool_t{true});
        }
        sell_opt.reset();
      }
      if (buy_out_of_tons) {
        buys_.pop();
        OrderRet ret { uint32(ec::out_of_tons), buy.original_amount - buy.amount, uint128{0} };
        if (buy_idx == buy_idx_cur)
          ret_ = ret;
        if (sell.account > tons_cfg_.return_ownership) {
          ITONTokenWalletPtr(buy.tip3_wallet_provide)(Crystals(tons_cfg_.return_ownership.get())).
            returnOwnership(buy.amount);
          IPriceCallbackPtr(buy.client_addr)(Crystals(buy.account.get())).
            onOrderFinished(ret, bool_t{false});
        }
        buy_opt.reset();
      }
      if (sell_out_of_tons || buy_out_of_tons)
        continue;

      sell_opt->second = sell;
      buy_opt->second = buy;

      sells_amount_ -= deal_amount;
      buys_amount_ -= deal_amount;
      // ==== if one of sides is out of tokens amount ====
      // Also if the order's remaining amount is less then allowed
      if ((sell.amount == 0) || (sell.amount < min_amount_) || !minor_cost(sell.amount, price_)) {
        sells_.pop();
        OrderRet ret { uint32(ok), sell.original_amount - sell.amount, uint128{0} };
        if (sell_idx == sell_idx_cur)
          ret_ = ret;
        IPriceCallbackPtr(sell.client_addr)(Crystals(sell.account.get())).
          onOrderFinished(ret, bool_t{true});
        sell_opt.reset();
      }
      if ((buy.amount == 0) || (buy.amount < min_amount_) || !minor_cost(buy.amount, price_)) {
        buys_.pop();
        OrderRet ret { uint32(ok), buy.original_amount - buy.amount, uint128{0} };
        if (buy_idx == buy_idx_cur)
          ret_ = ret;
        IPriceCallbackPtr(buy.client_addr)(Crystals(buy.account.get())).
          onOrderFinished(ret, bool_t{false});
        buy_opt.reset();
      }
    }
    if (sell_opt && sell_opt->second.amount) {
      // If the last sell order is not fully processed, modify its amount
      auto sell = sell_opt->second;
      sells_.change_front(sell);
      if (sell_idx == sell_opt->first)
        ret_ = OrderRet { uint32(ok), sell.original_amount - sell.amount, sell.amount };
    }
    if (buy_opt && buy_opt->second.amount) {
      // If the last buy order is not fully processed, modify its amount
      auto buy = buy_opt->second;
      buys_.change_front(buy);
      if (buy_idx == buy_opt->first)
        ret_ = OrderRet { uint32(ok), buy.original_amount - buy.amount, buy.amount };
    }
  }

  address tip3root_sell_;
  address tip3root_buy_;
  IFlexNotifyPtr notify_addr_;
  price_t price_;
  unsigned deals_limit_;
  TonsConfig tons_cfg_;
  uint128 sells_amount_;
  big_queue<OrderInfoXchg> sells_;
  uint128 buys_amount_;
  big_queue<OrderInfoXchg> buys_;
  uint128 min_amount_;
  std::optional<OrderRet> ret_;
};

struct process_ret {
  uint128 sells_amount;
  big_queue<OrderInfoXchg> sells_;
  uint128 buys_amount;
  big_queue<OrderInfoXchg> buys_;
  std::optional<OrderRet> ret_;
};

__attribute__((noinline))
process_ret process_queue_impl(address tip3root_sell, address tip3root_buy,
                               IFlexNotifyPtr notify_addr,
                               price_t price, uint8 deals_limit, TonsConfig tons_cfg,
                               unsigned sell_idx, unsigned buy_idx,
                               uint128 sells_amount, big_queue<OrderInfoXchg> sells,
                               uint128 buys_amount, big_queue<OrderInfoXchg> buys, uint128 min_amount) {
  dealer d{tip3root_sell, tip3root_buy, notify_addr, price, deals_limit.get(), tons_cfg,
           sells_amount, sells, buys_amount, buys, min_amount, {}};
  d.process_queue(sell_idx, buy_idx);
  return { d.sells_amount_, d.sells_, d.buys_amount_, d.buys_, d.ret_ };
}

__attribute__((noinline))
std::pair<big_queue<OrderInfoXchg>, uint128> cancel_order_impl(
    big_queue<OrderInfoXchg> orders, addr_std_fixed client_addr, uint128 all_amount, bool_t sell,
    Crystals return_ownership, Crystals process_queue, Crystals incoming_val) {
  bool is_first = true;
  for (auto it = orders.begin(); it != orders.end();) {
    auto next_it = std::next(it);
    auto ord = *it;
    if (ord.client_addr == client_addr) {
      unsigned minus_val = process_queue.get();
      ITONTokenWalletPtr(ord.tip3_wallet_provide)(return_ownership).
        returnOwnership(ord.amount);
      minus_val += return_ownership.get();

      unsigned plus_val = ord.account.get() + (is_first ? incoming_val.get() : 0);
      is_first = false;
      if (plus_val > minus_val) {
        unsigned ret_val = plus_val - minus_val;
        OrderRet ret { uint32(ec::canceled), ord.original_amount - ord.amount, uint128{0} };
        IPriceCallbackPtr(ord.client_addr)(Crystals(ret_val)).
          onOrderFinished(ret, sell);
      }

      all_amount -= ord.amount;

      orders.erase(it);
    }
    it = next_it;
  }
  return { orders, all_amount };
}

class PriceXchg final : public smart_interface<IPriceXchg>, public DPriceXchg {
public:
  __always_inline
  OrderRet onTip3LendOwnership(
    uint128     balance,
    uint32      lend_finish_time,
    uint256     pubkey,
    address_opt owner,
    cell        payload,
    address     answer_addr
  ) {
    auto [tip3_wallet, value] = int_sender_and_value();
    ITONTokenWalletPtr wallet_in(tip3_wallet);
    Crystals ret_owner_gr(tons_cfg_.return_ownership.get());

    // to send answer to the original caller (caller->tip3wallet->price->caller)
    set_int_sender(answer_addr);
    set_int_return_value(tons_cfg_.order_answer.get());

    auto min_value = onTip3LendOwnershipMinValue();

    auto args = parse<PayloadArgs>(payload.ctos());
    bool_t is_sell = args.sell;
    auto amount = args.amount;
    auto minor_amount = minor_cost(amount, price_);
    unsigned err = 0;
    if (value.get() < min_value)
      err = ec::not_enough_tons_to_process;
    else if (is_sell ? !verify_tip3_addr(major_tip3cfg_, tip3_wallet, pubkey, owner) :
                       !verify_tip3_addr(minor_tip3cfg_, tip3_wallet, pubkey, owner))
      err = ec::unverified_tip3_wallet;
    else if (!minor_amount)
      err = ec::too_big_tokens_amount;
    else if (amount < min_amount_)
      err = ec::not_enough_tokens_amount;
    else if (balance < (is_sell ? amount : *minor_amount))
      err = ec::too_big_tokens_amount;
    else if (!is_active_time(lend_finish_time))
      err = ec::expired;

    if (err)
      return on_ord_fail(err, wallet_in, amount);

    uint128 account = uint128(value.get()) - tons_cfg_.process_queue - tons_cfg_.order_answer;

    OrderInfoXchg ord {
      bool_t{true}, bool_t{true}, amount, amount, account, tip3_wallet,
      args.receive_tip3_wallet, args.client_addr, lend_finish_time
      };
    unsigned sell_idx = 0;
    unsigned buy_idx = 0;
    uint128 notify_amount;
    if (is_sell) {
      sells_.push(ord);
      sells_amount_ += ord.amount;
      sell_idx = sells_.back_with_idx().first;
      notify_amount = sells_amount_;
    } else {
      buys_.push(ord);
      buys_amount_ += ord.amount;
      buy_idx = buys_.back_with_idx().first;
      notify_amount = buys_amount_;
    }

    notify_addr_(Crystals(tons_cfg_.send_notify.get())).
      onXchgOrderAdded(is_sell, major_tip3cfg_.root_address, minor_tip3cfg_.root_address,
                       price_.numerator(), price_.denominator(), ord.amount, notify_amount);

    auto [sells_amount, sells, buys_amount, buys, ret] =
      process_queue_impl(major_tip3cfg_.root_address, minor_tip3cfg_.root_address,
                         notify_addr_, price_, deals_limit_, tons_cfg_,
                         sell_idx, buy_idx,
                         sells_amount_, sells_, buys_amount_, buys_, min_amount_);
    sells_ = sells;
    buys_ = buys;
    sells_amount_ = sells_amount;
    buys_amount_ = buys_amount;

    if (sells_.empty() && buys_.empty())
      suicide(flex_);
    if (ret) return *ret;
    return { uint32(ok), uint128(0), ord.amount };
  }

  __always_inline
  void processQueue() {
    if (sells_.empty() || buys_.empty())
      return;
    auto [sells_amount, sells, buys_amount, buys, ret] =
      process_queue_impl(major_tip3cfg_.root_address, minor_tip3cfg_.root_address,
                         notify_addr_, price_, deals_limit_, tons_cfg_, 0, 0,
                         sells_amount_, sells_, buys_amount_, buys_, min_amount_);
    sells_ = sells;
    buys_ = buys;
    sells_amount_ = sells_amount;
    buys_amount_ = buys_amount;
    if (sells_.empty() && buys_.empty())
      suicide(flex_);
  }

  __always_inline
  void cancelSell() {
    auto canceled_amount = sells_amount_;
    addr_std_fixed client_addr = int_sender();
    auto value = int_value();
    auto [sells, sells_amount] =
      cancel_order_impl(sells_, client_addr, sells_amount_, bool_t{true},
                        Crystals(tons_cfg_.return_ownership.get()),
                        Crystals(tons_cfg_.process_queue.get()), value);
    sells_ = sells;
    sells_amount_ = sells_amount;
    canceled_amount -= sells_amount_;

    notify_addr_(Crystals(tons_cfg_.send_notify.get())).
      onXchgOrderCanceled(bool_t{true}, major_tip3cfg_.root_address, minor_tip3cfg_.root_address,
                          price_.numerator(), price_.denominator(), canceled_amount, sells_amount_);

    if (sells_.empty() && buys_.empty())
      suicide(flex_);
  }

  __always_inline
  void cancelBuy() {
    auto canceled_amount = buys_amount_;
    addr_std_fixed client_addr = int_sender();
    auto value = int_value();
    auto [buys, buys_amount] =
      cancel_order_impl(buys_, client_addr, buys_amount_, bool_t{false},
                        Crystals(tons_cfg_.return_ownership.get()),
                        Crystals(tons_cfg_.process_queue.get()), value);
    buys_ = buys;
    buys_amount_ = buys_amount;
    canceled_amount -= buys_amount_;

    notify_addr_(Crystals(tons_cfg_.send_notify.get())).
      onXchgOrderCanceled(bool_t{false}, major_tip3cfg_.root_address, minor_tip3cfg_.root_address,
                          price_.numerator(), price_.denominator(), canceled_amount, buys_amount_);

    if (sells_.empty() && buys_.empty())
      suicide(flex_);
  }

  // ========== getters ==========

  __always_inline
  uint128 getPriceNum() {
    return price_.numerator();
  }

  __always_inline
  uint128 getPriceDenum() {
    return price_.denominator();
  }

  __always_inline
  uint128 getMinimumAmount() {
    return min_amount_;
  }

  __always_inline
  TonsConfig getTonsCfg() {
    return tons_cfg_;
  }

  __always_inline
  dict_array<OrderInfoXchg> getSells() {
    return dict_array<OrderInfoXchg>(sells_.begin(), sells_.end());
  }

  __always_inline
  dict_array<OrderInfoXchg> getBuys() {
    return dict_array<OrderInfoXchg>(buys_.begin(), buys_.end());
  }

  __always_inline
  uint128 getSellAmount() {
    return sells_amount_;
  }

  __always_inline
  uint128 getBuyAmount() {
    return buys_amount_;
  }

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }
  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IPriceXchg, void)
private:
  __always_inline
  uint128 onTip3LendOwnershipMinValue() const {
    // we need funds for processing:
    // * execute this function
    // * execute transfer from seller's tip3 wallet to buyer tip3 wallet
    // * execute returnOwnership of tip3 wallet to return ownership to the original owner
    // * send answer message
    return tons_cfg_.process_queue + tons_cfg_.transfer_tip3 + tons_cfg_.send_notify +
      tons_cfg_.return_ownership + tons_cfg_.order_answer;
  }

  __always_inline
  bool verify_tip3_addr(
    Tip3Config cfg,
    address tip3_wallet,
    uint256 wallet_pubkey,
    std::optional<address> wallet_internal_owner
  ) {
    auto expected_address = expected_wallet_address(cfg, wallet_pubkey, wallet_internal_owner);
    return std::get<addr_std>(tip3_wallet()).address == expected_address;
  }

  /// Optimized expected tip3 address calculation using code hash instead of full code cell.
  /// Macroses should be defined: TIP3_WALLET_CODE_HASH, TIP3_WALLET_CODE_DEPTH
  __always_inline
  uint256 expected_wallet_address(
    Tip3Config  cfg,
    uint256     wallet_pubkey,
    address_opt wallet_owner
  ) {
    return calc_int_wallet_init_hash(
      cfg.name, cfg.symbol, cfg.decimals, cfg.root_public_key, cfg.root_address,
      wallet_pubkey, wallet_owner,
      uint256(TIP3_WALLET_CODE_HASH), uint16(TIP3_WALLET_CODE_DEPTH), workchain_id_
      );
  }

  __always_inline
  OrderRet on_ord_fail(unsigned ec, ITONTokenWalletPtr wallet_in, uint128 amount) {
    wallet_in(Crystals(tons_cfg_.return_ownership.get())).returnOwnership(amount);
    if (sells_.empty() && buys_.empty()) {
      set_int_return_flag(SEND_ALL_GAS | DELETE_ME_IF_I_AM_EMPTY);
    } else {
      auto incoming_value = int_value().get();
      tvm_rawreserve(tvm_balance() - incoming_value, rawreserve_flag::up_to);
      set_int_return_flag(SEND_ALL_GAS);
    }
    return { uint32(ec), {}, {} };
  }
};

DEFINE_JSON_ABI(IPriceXchg, DPriceXchg, EPriceXchg);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(PriceXchg, IPriceXchg, DPriceXchg)

