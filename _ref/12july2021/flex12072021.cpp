#include "FlexClient.hpp"
#include "TradingPair.hpp"
#include "XchgPair.hpp"

#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/replay_attack_protection/timestamp.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

static constexpr unsigned TIMESTAMP_DELAY = 1800;

class FLeXClient final : public smart_interface<IFLeXClient>, public DFLeXClient {
  using replay_protection_t = replay_attack_protection::timestamp<TIMESTAMP_DELAY>;
public:
  struct error_code : tvm::error_code {
    static constexpr unsigned message_sender_is_not_my_owner = 100;
  };

  __always_inline
  void constructor(uint256 pubkey, cell trading_pair_code, cell xchg_pair_code) {
    owner_ = pubkey;
    trading_pair_code_ = trading_pair_code;
    xchg_pair_code_ = xchg_pair_code;
    workchain_id_ = std::get<addr_std>(address{tvm_myaddr()}.val()).workchain_id;
    flex_ = address::make_std(int8(0), uint256(0));
    notify_addr_ = address::make_std(int8(0), uint256(0));
  }

  __always_inline
  void setFLeXCfg(TonsConfig tons_cfg, address flex, address notify_addr) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    tons_cfg_ = tons_cfg;
    flex_ = flex;
    notify_addr_ = notify_addr;
  }

  __always_inline
  address deployTradingPair(address tip3_root, uint128 deploy_min_value, uint128 deploy_value) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    DTradingPair pair_data {
      .flex_addr_ = flex_,
      .tip3_root_ = tip3_root,
      .deploy_value_ = deploy_min_value
    };

    auto [state_init, std_addr] = prepare_trading_pair_state_init_and_addr(pair_data, trading_pair_code_);
    auto trade_pair = ITradingPairPtr(address::make_std(workchain_id_, std_addr));
    trade_pair.deploy(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS, false).onDeploy();

    return trade_pair.get();
  }

  __always_inline
  address deployXchgPair(address tip3_major_root, address tip3_minor_root,
                         uint128 deploy_min_value, uint128 deploy_value) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    DXchgPair pair_data {
      .flex_addr_ = flex_,
      .tip3_major_root_ = tip3_major_root,
      .tip3_minor_root_ = tip3_minor_root,
      .deploy_value_ = deploy_min_value
    };

    auto [state_init, std_addr] = prepare_xchg_pair_state_init_and_addr(pair_data, xchg_pair_code_);
    auto trade_pair = IXchgPairPtr(address::make_std(workchain_id_, std_addr));
    trade_pair.deploy(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS, false).onDeploy();

    return trade_pair.get();
  }

  __always_inline
  address deployPriceWithSell(cell args_cl) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    auto args = parse<FLeXSellArgs>(args_cl.ctos());

    auto [state_init, addr, std_addr] =
      preparePrice(args.price, args.min_amount, args.deals_limit, args.tip3_code, args.tip3cfg(), args.price_code);
    auto price_addr = IPricePtr(addr);
    cell deploy_init_cl = build(state_init).endc();
    SellArgs sell_args = {
      .amount = args.amount,
      .receive_wallet = args.addrs().receive_wallet
    };
    cell payload = build(sell_args).endc();

    ITONTokenWalletPtr my_tip3(args.addrs().my_tip3_addr);
    my_tip3(Grams(args.tons_value.get()), DEFAULT_MSG_FLAGS, false).
      lendOwnership(std_addr, args.amount, args.lend_finish_time, deploy_init_cl, payload);

    return price_addr.get();
  }

  __always_inline
  address deployPriceWithBuy(cell args_cl) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    auto args = parse<FLeXBuyArgs>(args_cl.ctos());

    auto [state_init, addr, std_addr] =
      preparePrice(args.price, args.min_amount, args.deals_limit, args.tip3_code, args.tip3cfg(), args.price_code);
    IPricePtr price_addr(addr);
    price_addr.deploy(state_init, Grams(args.deploy_value.get()), DEFAULT_MSG_FLAGS, false).
      buyTip3(args.amount, args.my_tip3_addr, args.order_finish_time);
    return price_addr.get();
  }

  __always_inline
  void cancelSellOrder(cell args_cl) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    auto args = parse<FLeXCancelArgs>(args_cl.ctos());
    auto [state_init, addr, std_addr] =
      preparePrice(args.price, args.min_amount, args.deals_limit, args.tip3_code, args.tip3cfg(), args.price_code);
    IPricePtr price_addr(addr);
    price_addr(Grams(args.value.get()), DEFAULT_MSG_FLAGS, false).cancelSell();
  }

  __always_inline
  void cancelBuyOrder(cell args_cl) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    auto args = parse<FLeXCancelArgs>(args_cl.ctos());
    auto [state_init, addr, std_addr] =
      preparePrice(args.price, args.min_amount, args.deals_limit, args.tip3_code, args.tip3cfg(), args.price_code);
    IPricePtr price_addr(addr);
    price_addr(Grams(args.value.get()), DEFAULT_MSG_FLAGS, false).cancelBuy();
  }

  __always_inline
  void cancelXchgOrder(cell args_cl) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    auto args = parse<FLeXXchgCancelArgs>(args_cl.ctos());
    auto [state_init, addr, std_addr] =
      preparePriceXchg(args.price_num, args.price_denum, args.min_amount, args.deals_limit,
                       args.tip3_code, args.tip3cfgs().major_tip3cfg(), args.tip3cfgs().minor_tip3cfg(),
                       args.xchg_price_code);
    IPriceXchgPtr price_addr(addr);
    if (args.sell)
      price_addr(Grams(args.value.get()), DEFAULT_MSG_FLAGS, false).cancelSell();
    else
      price_addr(Grams(args.value.get()), DEFAULT_MSG_FLAGS, false).cancelBuy();
  }

  __always_inline
  void transfer(address dest, uint128 value, bool_t bounce) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    tvm_transfer(dest, value.get(), bounce.get());
  }

  __always_inline
  address deployPriceXchg(cell args_cl) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    auto args = parse<FLeXXchgArgs>(args_cl.ctos());

    auto [state_init, addr, std_addr] =
      preparePriceXchg(args.price_num, args.price_denum, args.min_amount, args.deals_limit,
                       args.tip3_code, args.tip3cfgs().major_tip3cfg(), args.tip3cfgs().minor_tip3cfg(),
                       args.xchg_price_code);
    auto price_addr = IPriceXchgPtr(addr);
    cell deploy_init_cl = build(state_init).endc();
    PayloadArgs payload_args = {
      .sell = args.sell,
      .amount = args.amount,
      .receive_tip3_wallet = args.addrs().receive_wallet,
      .client_addr = address{tvm_myaddr()}
    };
    cell payload = build(payload_args).endc();

    ITONTokenWalletPtr my_tip3(args.addrs().my_tip3_addr);
    my_tip3(Grams(args.tons_value.get()), DEFAULT_MSG_FLAGS, false).
      lendOwnership(std_addr, args.lend_amount, args.lend_finish_time, deploy_init_cl, payload);

    return price_addr.get();
  }

  __always_inline
  uint256 getOwner() {
    return owner_;
  }

  __always_inline
  address getFLeX() {
    return flex_;
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IFLeXClient, replay_protection_t)

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }

private:
  __always_inline
  std::tuple<StateInit, address, uint256> preparePrice(
      uint128 price, uint128 min_amount, uint8 deals_limit, cell tip3_code, Tip3Config tip3cfg, cell price_code) const {
    DPrice price_data {
      .price_ = price,
      .sells_amount_ = uint128(0),
      .buys_amount_ = uint128(0),
      .flex_ = flex_,
      .min_amount_ = min_amount,
      .deals_limit_ = deals_limit,
      .notify_addr_ = notify_addr_,
      .workchain_id_ = workchain_id_,
      .tons_cfg_ = tons_cfg_,
      .tip3_code_ = tip3_code,
      .tip3cfg_ = tip3cfg,
      .sells_ = {},
      .buys_ = {}
    };
    auto [state_init, std_addr] = prepare_price_state_init_and_addr(price_data, price_code);
    auto addr = address::make_std(workchain_id_, std_addr);
    return { state_init, addr, std_addr };
  }
  __always_inline
  std::tuple<StateInit, address, uint256> preparePriceXchg(
      uint128 price_num, uint128 price_denum, uint128 min_amount, uint8 deals_limit, cell tip3_code,
      Tip3Config major_tip3cfg, Tip3Config minor_tip3cfg, cell price_code) const {

    DPriceXchg price_data {
      .price_ = { price_num, price_denum },
      .sells_amount_ = uint128(0),
      .buys_amount_ = uint128(0),
      .flex_ = flex_,
      .min_amount_ = min_amount,
      .deals_limit_ = deals_limit,
      .notify_addr_ = notify_addr_,
      .workchain_id_ = workchain_id_,
      .tons_cfg_ = tons_cfg_,
      .tip3_code_ = tip3_code,
      .major_tip3cfg_ = major_tip3cfg,
      .minor_tip3cfg_ = minor_tip3cfg,
      .sells_ = {},
      .buys_ = {}
    };
    auto [state_init, std_addr] = prepare_price_xchg_state_init_and_addr(price_data, price_code);
    auto addr = address::make_std(workchain_id_, std_addr);
    return { state_init, addr, std_addr };
  }
};

DEFINE_JSON_ABI(IFLeXClient, DFLeXClient, EFLeXClient);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS(FLeXClient, IFLeXClient, , TIMESTAMP_DELAY)

#pragma once

#include <tvm/schema/message.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>

#include "Price.hpp"
#include "PriceXchg.hpp"

namespace tvm { namespace schema {

struct FLeXSellArgsAddrs {
  address my_tip3_addr;
  address receive_wallet;
};

struct FLeXSellArgs {
  uint128 price;
  uint128 amount;
  uint32 lend_finish_time;
  uint128 min_amount;
  uint8 deals_limit;
  uint128 tons_value;
  cell price_code;
  ref<FLeXSellArgsAddrs> addrs;
  cell tip3_code;
  ref<Tip3Config> tip3cfg;
};

struct FLeXBuyArgs {
  uint128 price;
  uint128 amount;
  uint32 order_finish_time;
  uint128 min_amount;
  uint8 deals_limit;
  uint128 deploy_value;
  cell price_code;
  address my_tip3_addr;
  cell tip3_code;
  ref<Tip3Config> tip3cfg;
};

struct FLeXXchgCfgs {
  ref<Tip3Config> major_tip3cfg;
  ref<Tip3Config> minor_tip3cfg;
};

struct FLeXXchgArgs {
  bool_t  sell;
  uint128 price_num;
  uint128 price_denum;
  uint128 amount;
  uint128 lend_amount;
  uint32  lend_finish_time;
  uint128 min_amount;
  uint8   deals_limit;
  uint128 tons_value;
  cell    xchg_price_code;
  ref<FLeXSellArgsAddrs> addrs;
  cell    tip3_code;
  ref<FLeXXchgCfgs> tip3cfgs;
};

struct FLeXCancelArgs {
  uint128 price;
  uint128 min_amount;
  uint8   deals_limit;
  uint128 value;
  cell    price_code;
  cell    tip3_code;
  ref<Tip3Config> tip3cfg;
};

struct FLeXXchgCancelArgs {
  bool_t  sell;
  uint128 price_num;
  uint128 price_denum;
  uint128 min_amount;
  uint8   deals_limit;
  uint128 value;
  cell    xchg_price_code;
  cell    tip3_code;
  ref<FLeXXchgCfgs> tip3cfgs;
};

__interface IFLeXClient {

  [[external, dyn_chain_parse]]
  void constructor(uint256 pubkey, cell trading_pair_code, cell xchg_pair_code);

  [[external, noaccept, dyn_chain_parse]]
  void setFLeXCfg(TonsConfig tons_cfg, address flex, address notify_addr);

  [[external, noaccept, dyn_chain_parse]]
  address deployTradingPair(address tip3_root, uint128 deploy_min_value, uint128 deploy_value);

  [[external, noaccept, dyn_chain_parse]]
  address deployXchgPair(address tip3_major_root, address tip3_minor_root,
                         uint128 deploy_min_value, uint128 deploy_value);

  // args must be FLeXSellArgs
  [[external, noaccept]]
  address deployPriceWithSell(cell args);

  // args must be FLeXBuyArgs
  [[external, noaccept]]
  address deployPriceWithBuy(cell args);

  // args must be FLeXXchgArgs
  [[external, noaccept]]
  address deployPriceXchg(cell args_cl);

  [[external, noaccept]]
  void cancelSellOrder(cell args);

  [[external, noaccept]]
  void cancelBuyOrder(cell args);

  [[external, noaccept]]
  void cancelXchgOrder(cell args);

  [[external, noaccept, dyn_chain_parse]]
  void transfer(address dest, uint128 value, bool_t bounce);

  [[getter]]
  uint256 getOwner();

  [[getter]]
  address getFLeX();
};
using IFLeXClientPtr = handle<IFLeXClient>;

struct DFLeXClient {
  uint256 owner_;
  cell trading_pair_code_;
  cell xchg_pair_code_;
  int8 workchain_id_;
  TonsConfig tons_cfg_;
  address flex_;
  address notify_addr_;
};

__interface EFLeXClient {
};

}} // namespace tvm::schema

#include "Flex.hpp"
#include "TradingPair.hpp"
#include "XchgPair.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

static constexpr unsigned TIMESTAMP_DELAY = 1800;

class FLeX final : public smart_interface<IFLeX>, public DFLeX {
  using replay_protection_t = replay_attack_protection::timestamp<TIMESTAMP_DELAY>;
public:
  struct error_code : tvm::error_code {
    static constexpr unsigned sender_is_not_deployer        = 100;
    static constexpr unsigned unexpected_refs_count_in_code = 101;
    static constexpr unsigned cant_override_code            = 102;
  };

  __always_inline
  void constructor(uint256 deployer_pubkey,
      uint128 transfer_tip3, uint128 return_ownership, uint128 trading_pair_deploy,
      uint128 order_answer, uint128 process_queue, uint128 send_notify,
      uint128 min_amount, uint8 deals_limit, address notify_addr) {
    deployer_pubkey_ = deployer_pubkey;
    min_amount_ = min_amount;
    deals_limit_ = deals_limit;
    notify_addr_ = notify_addr;
    tons_cfg_ = {
      transfer_tip3, return_ownership, trading_pair_deploy, order_answer, process_queue, send_notify
    };
  }

  __always_inline
  void setPairCode(cell code) {
    require(!isFullyInitialized().get(), error_code::cant_override_code);
    require(msg_pubkey() == deployer_pubkey_, error_code::sender_is_not_deployer);
    tvm_accept();
    require(!pair_code_, error_code::cant_override_code);
    // adding flex address to ref#2 in this code cell
    require(code.ctos().srefs() == 2, error_code::unexpected_refs_count_in_code);
    pair_code_ = builder().stslice(code.ctos()).stref(build(address{tvm_myaddr()}).endc()).endc();
  }

  __always_inline
  void setXchgPairCode(cell code) {
    require(!isFullyInitialized().get(), error_code::cant_override_code);
    require(msg_pubkey() == deployer_pubkey_, error_code::sender_is_not_deployer);
    tvm_accept();
    require(!xchg_pair_code_, error_code::cant_override_code);
    // adding flex address to ref#2 in this code cell
    require(code.ctos().srefs() == 2, error_code::unexpected_refs_count_in_code);
    xchg_pair_code_ = builder().stslice(code.ctos()).stref(build(address{tvm_myaddr()}).endc()).endc();
  }

  __always_inline
  void setPriceCode(cell code) {
    require(!isFullyInitialized().get(), error_code::cant_override_code);
    require(msg_pubkey() == deployer_pubkey_, error_code::sender_is_not_deployer);
    tvm_accept();
    require(!price_code_, error_code::cant_override_code);
    price_code_ = code;
  }

  __always_inline
  void setXchgPriceCode(cell code) {
    require(!isFullyInitialized().get(), error_code::cant_override_code);
    require(msg_pubkey() == deployer_pubkey_, error_code::sender_is_not_deployer);
    tvm_accept();
    require(!xchg_price_code_, error_code::cant_override_code);
    xchg_price_code_ = code;
  }

  __always_inline
  bool_t isFullyInitialized() {
    return bool_t(pair_code_ && price_code_ && xchg_pair_code_ && xchg_price_code_);
  }

  __always_inline
  TonsConfig getTonsCfg() {
    return tons_cfg_;
  }

  __always_inline
  cell getTradingPairCode() {
    return *pair_code_;
  }

  __always_inline
  cell getXchgPairCode() {
    return *xchg_pair_code_;
  }

  __always_inline
  cell getSellPriceCode(address tip3_addr) {
    // adding tip3 root address to ref#3 in this code cell
    require(price_code_->ctos().srefs() == 2, error_code::unexpected_refs_count_in_code);
    cell salt = builder().stslice(tvm_myaddr()).stslice(tip3_addr.sl()).endc();
    return builder().stslice(price_code_->ctos()).stref(salt).endc();
  }

  __always_inline
  cell getXchgPriceCode(address tip3_addr1, address tip3_addr2) {
    require(price_code_->ctos().srefs() == 2, error_code::unexpected_refs_count_in_code);
    auto keys = std::make_tuple(tip3_addr1, tip3_addr2);
    return builder().stslice(xchg_price_code_->ctos()).stref(build(keys).endc()).endc();
  }

  __always_inline
  address getSellTradingPair(address tip3_root) {
    address myaddr{tvm_myaddr()};
    DTradingPair pair_data {
      .flex_addr_ = myaddr,
      .tip3_root_ = tip3_root,
      .deploy_value_ = tons_cfg_.trading_pair_deploy
    };
    auto std_addr = prepare_trading_pair_state_init_and_addr(pair_data, *pair_code_).second;
    auto workchain_id = std::get<addr_std>(myaddr.val()).workchain_id;
    return address::make_std(workchain_id, std_addr);
  }

  __always_inline
  address getXchgTradingPair(address tip3_major_root, address tip3_minor_root) {
    address myaddr{tvm_myaddr()};
    DXchgPair pair_data {
      .flex_addr_ = myaddr,
      .tip3_major_root_ = tip3_major_root,
      .tip3_minor_root_ = tip3_minor_root,
      .deploy_value_ = tons_cfg_.trading_pair_deploy
    };
    auto std_addr = prepare_xchg_pair_state_init_and_addr(pair_data, *xchg_pair_code_).second;
    auto workchain_id = std::get<addr_std>(myaddr.val()).workchain_id;
    return address::make_std(workchain_id, std_addr);
  }

  __always_inline
  uint128 getMinAmount() {
    return min_amount_;
  }

  __always_inline
  uint8 getDealsLimit() {
    return deals_limit_;
  }

  __always_inline
  address getNotifyAddr() {
    return notify_addr_;
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IFLeX, replay_protection_t)

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }
};

DEFINE_JSON_ABI(IFLeX, DFLeX, EFLeX);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS(FLeX, IFLeX, DFLeX, TIMESTAMP_DELAY)

#pragma once

#include <tvm/schema/message.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>

namespace tvm { namespace schema {

// Processing native funds value ...
struct TonsConfig {
  // ... for executing tip3 transfer
  uint128 transfer_tip3;
  // ... to return tip3 ownership
  uint128 return_ownership;
  // ... to deploy tip3 trading pair
  uint128 trading_pair_deploy;
  // .. to send answer message from Price
  uint128 order_answer;
  // ... to process processQueue function
  //  (also is used for buyTip3/onTip3LendOwnership/cancelSell/cancelBuy estimations)
  uint128 process_queue;
  // ... to send notification about completed deal (IFLeXNotify)
  uint128 send_notify;
};

__interface IFLeXNotify {
  [[internal, noaccept]]
  void onDealCompleted(address tip3root, uint128 price, uint128 amount);
  [[internal, noaccept]]
  void onXchgDealCompleted(address tip3root_sell, address tip3root_buy,
                           uint128 price_num, uint128 price_denum, uint128 amount);
};
using IFLeXNotifyPtr = handle<IFLeXNotify>;

__interface IFLeX {

  [[external, dyn_chain_parse]]
  void constructor(uint256 deployer_pubkey,
    uint128 transfer_tip3, uint128 return_ownership, uint128 trading_pair_deploy,
    uint128 order_answer, uint128 process_queue, uint128 send_notify,
    uint128 min_amount, uint8 deals_limit, address notify_addr);

  // To fit message size limit, setPairCode/setPriceCode in separate functions
  //  (not in constructor)
  [[external, noaccept]]
  void setPairCode(cell code);

  [[external, noaccept]]
  void setXchgPairCode(cell code);

  [[external, noaccept]]
  void setPriceCode(cell code);

  [[external, noaccept]]
  void setXchgPriceCode(cell code);

  // ========== getters ==========

  // means setPairCode/setPriceCode executed
  [[getter]]
  bool_t isFullyInitialized();

  [[getter]]
  TonsConfig getTonsCfg();

  [[getter]]
  cell getTradingPairCode();

  [[getter]]
  cell getXchgPairCode();

  [[getter, dyn_chain_parse]]
  cell getSellPriceCode(address tip3_addr);

  [[getter, dyn_chain_parse]]
  cell getXchgPriceCode(address tip3_addr1, address tip3_addr2);

  [[getter, dyn_chain_parse]]
  address getSellTradingPair(address tip3_root);

  [[getter, dyn_chain_parse]]
  address getXchgTradingPair(address tip3_major_root, address tip3_minor_root);

  [[getter]]
  uint128 getMinAmount();

  [[getter]]
  uint8 getDealsLimit();

  [[getter]]
  address getNotifyAddr();
};
using IFLeXPtr = handle<IFLeX>;

struct DFLeX {
  uint256 deployer_pubkey_;
  TonsConfig tons_cfg_;
  std::optional<cell> pair_code_;
  std::optional<cell> xchg_pair_code_;
  std::optional<cell> price_code_;
  std::optional<cell> xchg_price_code_;
  uint128 min_amount_; // minimum amount to buy/sell
  uint8 deals_limit_; // deals limit in one processing in Price
  address notify_addr_;
};

__interface EFLeX {
};

}} // namespace tvm::schema

#pragma once

namespace tvm { namespace schema {

struct Tip3Config {
  string name;
  string symbol;
  uint8 decimals;
  uint256 root_public_key;
  address root_address;
};

struct OrderRet {
  uint32 err_code;
  uint128 processed;
  uint128 enqueued;
};

__interface IPriceCallback {
  [[internal, noaccept]]
  void onOrderFinished(OrderRet ret, bool_t sell);
};
using IPriceCallbackPtr = handle<IPriceCallback>;

}} // namespace tvm::schema
#include "Price.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

static constexpr unsigned ok = 0;
struct ec : tvm::error_code {
  static constexpr unsigned out_of_tons                    = 100; // partially processed because out of tons
  static constexpr unsigned deals_limit                    = 101; // partially processed because deals limit
  static constexpr unsigned not_enough_tons_to_process     = 102;
  static constexpr unsigned not_enough_tokens_amount       = 103;
  static constexpr unsigned too_big_tokens_amount          = 104;
  static constexpr unsigned different_workchain_id         = 105;
  static constexpr unsigned unverified_tip3_wallet         = 106;
  static constexpr unsigned canceled                       = 107;
  static constexpr unsigned expired                        = 108;
};

// For tip3 we have lend_finish_time, when ownership will return back to its original owner.
// And we need some safe period to not process orders with soon expiring tip3 ownership
static constexpr unsigned safe_delay_period = 5 * 60;

__always_inline
bool is_active_time(uint32 order_finish_time) {
  return tvm_now() + safe_delay_period < order_finish_time.get();
}

__always_inline
std::optional<uint128> calc_cost(uint128 amount, uint128 price) {
  unsigned tons_cost = amount.get() * price.get();
  if (tons_cost >> 128)
    return {};
  return uint128(tons_cost);
}

class dealer {
public:
  // returns (sell_out_of_tons, buy_out_of_tons, deal_amount)
  __always_inline
  std::tuple<bool, bool, uint128> make_deal(OrderInfo& sell, OrderInfo& buy) {
    auto deal_amount = std::min(sell.amount, buy.amount);
    bool_t last_tip3_sell{sell.amount == deal_amount};
    sell.amount -= deal_amount;
    buy.amount -= deal_amount;
    auto cost = calc_cost(deal_amount, price_);

    // Smaller pays for tip3 transfer
    //  (if seller provides big sell order, he will not pay for each small transfer)
    uint128 sell_costs{0};
    uint128 buy_costs = *cost;
    if (last_tip3_sell)
      sell_costs += (tons_cfg_.transfer_tip3 + tons_cfg_.send_notify);
    else
      buy_costs += (tons_cfg_.transfer_tip3 + tons_cfg_.send_notify);

    bool sell_out_of_tons = (sell.account < sell_costs);
    bool buy_out_of_tons = (buy.account < buy_costs);
    if (sell_out_of_tons || buy_out_of_tons)
      return {sell_out_of_tons, buy_out_of_tons, uint128(0)};
    sell.account -= sell_costs;
    buy.account -= buy_costs;

    ITONTokenWalletPtr(sell.tip3_wallet)(Grams(tons_cfg_.transfer_tip3.get()), IGNORE_ACTION_ERRORS).
      transfer(buy.tip3_wallet, deal_amount, last_tip3_sell, sell.tip3_wallet);
    tvm_transfer(sell.client_addr, cost->get(), /*bounce*/true);

    notify_addr_(Grams(tons_cfg_.send_notify.get()), IGNORE_ACTION_ERRORS).
      onDealCompleted(tip3root_, price_, deal_amount);

    return {false, false, deal_amount};
  }

  __attribute__((noinline))
  static std::tuple<std::optional<OrderInfoWithIdx>, queue<OrderInfo>, uint128>
  extract_active_order(std::optional<OrderInfoWithIdx> cur_order,
                       queue<OrderInfo> orders, uint128 all_amount, bool_t sell) {
    if (cur_order)
      return {cur_order, orders, all_amount};

    while (!orders.empty()) {
      cur_order = orders.front_with_idx_opt();
      auto ord = cur_order->second;
      if (!is_active_time(ord.order_finish_time)) {
        all_amount -= ord.amount;
        OrderRet ret { uint32(ec::expired), ord.original_amount - ord.amount, uint128{0} };
        IPriceCallbackPtr(ord.client_addr)(Grams(ord.account.get()), IGNORE_ACTION_ERRORS).
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
    std::optional<OrderInfoWithIdx> sell_opt;
    std::optional<OrderInfoWithIdx> buy_opt;
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
          IPricePtr(address{tvm_myaddr()})(Grams(tons_cfg_.process_queue.get()), IGNORE_ACTION_ERRORS).
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
          ITONTokenWalletPtr(sell.tip3_wallet)(Grams(tons_cfg_.return_ownership.get()), IGNORE_ACTION_ERRORS).
            returnOwnership();
          IPriceCallbackPtr(sell.client_addr)(Grams(sell.account.get()), IGNORE_ACTION_ERRORS).
            onOrderFinished(ret, bool_t{true});
        }
        sell_opt.reset();
      }
      if (buy_out_of_tons) {
        buys_.pop();
        OrderRet ret { uint32(ec::out_of_tons), buy.original_amount - buy.amount, uint128{0} };
        if (buy_idx == buy_idx_cur)
          ret_ = ret;
        IPriceCallbackPtr(buy.client_addr)(Grams(buy.account.get()), IGNORE_ACTION_ERRORS).
          onOrderFinished(ret, bool_t{false});
        buy_opt.reset();
      }
      if (sell_out_of_tons || buy_out_of_tons)
        continue;

      sell_opt->second = sell;
      buy_opt->second = buy;

      sells_amount_ -= deal_amount;
      buys_amount_ -= deal_amount;
      // ==== if one of sides is out of tokens amount ====
      if (!sell.amount) {
        sells_.pop();
        OrderRet ret { uint32(ok), sell.original_amount, uint128{0} };
        if (sell_idx == sell_idx_cur)
          ret_ = ret;
        IPriceCallbackPtr(sell.client_addr)(Grams(sell.account.get()), IGNORE_ACTION_ERRORS).
          onOrderFinished(ret, bool_t{true});
        sell_opt.reset();
      }
      if (!buy.amount) {
        buys_.pop();
        OrderRet ret { uint32(ok), buy.original_amount, uint128{0} };
        if (buy_idx == buy_idx_cur)
          ret_ = ret;
        IPriceCallbackPtr(buy.client_addr)(Grams(buy.account.get()), IGNORE_ACTION_ERRORS).
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

  address tip3root_;
  IFLeXNotifyPtr notify_addr_;
  uint128 price_;
  unsigned deals_limit_;
  TonsConfig tons_cfg_;
  uint128 sells_amount_;
  queue<OrderInfo> sells_;
  uint128 buys_amount_;
  queue<OrderInfo> buys_;
  std::optional<OrderRet> ret_;
};

struct process_ret {
  uint128 sells_amount;
  queue<OrderInfo> sells_;
  uint128 buys_amount;
  queue<OrderInfo> buys_;
  std::optional<OrderRet> ret_;
};

__attribute__((noinline))
process_ret process_queue_impl(address tip3root, IFLeXNotifyPtr notify_addr,
                               uint128 price, uint8 deals_limit, TonsConfig tons_cfg,
                               unsigned sell_idx, unsigned buy_idx,
                               uint128 sells_amount, queue<OrderInfo> sells,
                               uint128 buys_amount, queue<OrderInfo> buys) {
  dealer d{tip3root, notify_addr, price, deals_limit.get(), tons_cfg,
           sells_amount, sells, buys_amount, buys, {}};
  d.process_queue(sell_idx, buy_idx);
  return { d.sells_amount_, d.sells_, d.buys_amount_, d.buys_, d.ret_ };
}

__attribute__((noinline))
std::pair<queue<OrderInfo>, uint128> cancel_order_impl(
    queue<OrderInfo> orders, addr_std_fixed client_addr, uint128 all_amount, bool_t sell,
    Grams return_ownership, Grams process_queue, Grams incoming_val) {
  bool is_first = true;
  for (auto it = orders.begin(); it != orders.end();) {
    auto next_it = std::next(it);
    auto ord = *it;
    if (ord.client_addr == client_addr) {
      unsigned minus_val = process_queue.get();
      if (sell) {
        ITONTokenWalletPtr(ord.tip3_wallet)(return_ownership, IGNORE_ACTION_ERRORS).
          returnOwnership();
        minus_val += return_ownership.get();
      }
      unsigned plus_val = ord.account.get() + (is_first ? incoming_val.get() : 0);
      is_first = false;
      if (plus_val > minus_val) {
        unsigned ret_val = plus_val - minus_val;
        OrderRet ret { uint32(ec::canceled), ord.original_amount - ord.amount, uint128{0} };
        IPriceCallbackPtr(ord.client_addr)(Grams(ret_val), IGNORE_ACTION_ERRORS).
          onOrderFinished(ret, sell);
      }

      all_amount -= ord.amount;

      orders.erase(it);
    }
    it = next_it;
  }
  return { orders, all_amount };
}

class Price final : public smart_interface<IPrice>, public DPrice {
public:
  __always_inline
  OrderRet onTip3LendOwnership(
      uint128 balance, uint32 lend_finish_time, uint256 pubkey, uint256 internal_owner,
      cell payload_cl, address answer_addr) {
    auto [tip3_wallet, value] = int_sender_and_value();
    ITONTokenWalletPtr wallet_in(tip3_wallet);
    Grams ret_owner_gr(tons_cfg_.return_ownership.get());

    // to send answer to the original caller (caller->tip3wallet->price->caller)
    set_int_sender(answer_addr);
    set_int_return_value(tons_cfg_.order_answer.get());
    set_int_return_flag(IGNORE_ACTION_ERRORS);

    auto min_value = onTip3LendOwnershipMinValue();

    auto args = parse<SellArgs>(payload_cl.ctos());
    auto amount = args.amount;
    unsigned err = 0;
    if (value.get() < min_value)
      err = ec::not_enough_tons_to_process;
    else if (!verify_tip3_addr(tip3_wallet, pubkey, internal_owner))
      err = ec::unverified_tip3_wallet;
    else if (amount < min_amount_)
      err = ec::not_enough_tokens_amount;
    else if (balance < amount)
      err = ec::too_big_tokens_amount;
    else if (!calc_cost(amount, price_))
      err = ec::too_big_tokens_amount;

    if (err)
      return on_sell_fail(err, wallet_in);

    uint128 account = uint128(value.get()) - tons_cfg_.process_queue - tons_cfg_.order_answer;

    OrderInfo sell{amount, amount, account, tip3_wallet, args.receive_wallet, lend_finish_time};
    sells_.push(sell);
    sells_amount_ += sell.amount;

    auto [sells_amount, sells, buys_amount, buys, ret] =
      process_queue_impl(tip3cfg_.root_address, notify_addr_, price_, deals_limit_, tons_cfg_,
                         sells_.back_with_idx().first, 0,
                         sells_amount_, sells_, buys_amount_, buys_);
    sells_ = sells;
    buys_ = buys;
    sells_amount_ = sells_amount;
    buys_amount_ = buys_amount;

    if (sells_.empty() && buys_.empty())
      suicide(flex_);
    if (ret) return *ret;
    return { uint32(ok), uint128(0), sell.amount };
  }

  __always_inline
  OrderRet buyTip3(uint128 amount, address receive_tip3_wallet, uint32 order_finish_time) {
    auto [sender, value_gr] = int_sender_and_value();
    require(amount >= min_amount_, ec::not_enough_tokens_amount);
    auto cost = calc_cost(amount, price_);
    require(!!cost, ec::too_big_tokens_amount);
    require(value_gr.get() > buyTip3MinValue( *cost),
            ec::not_enough_tons_to_process);

    set_int_return_value(tons_cfg_.order_answer.get());
    set_int_return_flag(IGNORE_ACTION_ERRORS);

    uint128 account = uint128(value_gr.get()) - tons_cfg_.process_queue - tons_cfg_.order_answer;

    OrderInfo buy{amount, amount, account, receive_tip3_wallet, sender, order_finish_time};
    buys_.push(buy);
    buys_amount_ += buy.amount;

    auto [sells_amount, sells, buys_amount, buys, ret] =
      process_queue_impl(tip3cfg_.root_address, notify_addr_, price_, deals_limit_, tons_cfg_,
                         0, buys_.back_with_idx().first,
                         sells_amount_, sells_, buys_amount_, buys_);
    sells_ = sells;
    buys_ = buys;
    sells_amount_ = sells_amount;
    buys_amount_ = buys_amount;
    if (sells_.empty() && buys_.empty())
      suicide(flex_);
    if (ret) return *ret;
    return { uint32(ok), uint128(0), buy.amount };
  }

  __always_inline
  void processQueue() {
    if (sells_.empty() || buys_.empty())
      return;
    auto [sells_amount, sells, buys_amount, buys, ret] =
      process_queue_impl(tip3cfg_.root_address, notify_addr_, price_, deals_limit_, tons_cfg_, 0, 0,
                         sells_amount_, sells_, buys_amount_, buys_);
    sells_ = sells;
    buys_ = buys;
    sells_amount_ = sells_amount;
    buys_amount_ = buys_amount;
    if (sells_.empty() && buys_.empty())
      suicide(flex_);
  }

  __always_inline
  void cancelSell() {
    addr_std_fixed client_addr = int_sender();
    auto value = int_value();
    auto [sells, sells_amount] =
      cancel_order_impl(sells_, client_addr, sells_amount_, bool_t{true},
                        Grams(tons_cfg_.return_ownership.get()),
                        Grams(tons_cfg_.process_queue.get()), value);
    sells_ = sells;
    sells_amount_ = sells_amount;

    if (sells_.empty() && buys_.empty())
      suicide(flex_);
  }

  __always_inline
  void cancelBuy() {
    addr_std_fixed client_addr = int_sender();
    auto value = int_value();
    auto [buys, buys_amount] =
      cancel_order_impl(buys_, client_addr, buys_amount_, bool_t{false},
                        Grams(tons_cfg_.return_ownership.get()),
                        Grams(tons_cfg_.process_queue.get()), value);
    buys_ = buys;
    buys_amount_ = buys_amount;

    if (sells_.empty() && buys_.empty())
      suicide(flex_);
  }

  // ========== getters ==========
  __always_inline
  DetailsInfo getDetails() {
    return { getPrice(), getMinimumAmount(), getSellAmount(), getBuyAmount() };
  }

  __always_inline
  uint128 getPrice() {
    return price_;
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
  dict_array<OrderInfo> getSells() {
    return dict_array<OrderInfo>(sells_.begin(), sells_.end());
  }

  __always_inline
  dict_array<OrderInfo> getBuys() {
    return dict_array<OrderInfo>(buys_.begin(), buys_.end());
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
  DEFAULT_SUPPORT_FUNCTIONS(IPrice, void)
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
  uint128 buyTip3MinValue(uint128 buy_cost) const {
    return buy_cost + tons_cfg_.process_queue + tons_cfg_.transfer_tip3 + tons_cfg_.send_notify +
      tons_cfg_.order_answer;
  }
  __always_inline
  bool verify_tip3_addr(address tip3_wallet, uint256 wallet_pubkey, uint256 internal_owner) {
    auto expected_address = expected_wallet_address(wallet_pubkey, internal_owner);
    return std::get<addr_std>(tip3_wallet()).address == expected_address;
  }
  __always_inline
  uint256 expected_wallet_address(uint256 wallet_pubkey, uint256 internal_owner) {
    std::optional<address> owner_addr;
    if (internal_owner)
      owner_addr = address::make_std(workchain_id_, internal_owner);
    DTONTokenWallet wallet_data {
      tip3cfg_.name, tip3cfg_.symbol, tip3cfg_.decimals,
      TokensType(0), tip3cfg_.root_public_key, wallet_pubkey,
      tip3cfg_.root_address, owner_addr, {}, tip3_code_, {}, workchain_id_
    };
    return prepare_wallet_state_init_and_addr(wallet_data).second;
  }

  __always_inline
  OrderRet on_sell_fail(unsigned ec, ITONTokenWalletPtr wallet_in) {
    auto incoming_value = int_value().get();
    tvm_rawreserve(tvm_balance() - incoming_value, rawreserve_flag::up_to);
    set_int_return_flag(SEND_ALL_GAS);
    wallet_in(Grams(tons_cfg_.return_ownership.get()), IGNORE_ACTION_ERRORS).returnOwnership();
    return { uint32(ec), {}, {} };
  }
};

DEFINE_JSON_ABI(IPrice, DPrice, EPrice);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(Price, IPrice, DPrice)

#pragma once

#include <tvm/schema/message.hpp>

#include <tvm/replay_attack_protection/timestamp.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/small_dict_map.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/queue.hpp>
#include <tvm/string.hpp>

#include "Flex.hpp"
#include "PriceCommon.hpp"
#include "TONTokenWallet.hpp"

namespace tvm { namespace schema {

using ITONTokenWalletPtr = handle<ITONTokenWallet>;

struct SellArgs {
  uint128 amount;
  addr_std_fixed receive_wallet;
};

struct OrderInfo {
  uint128 original_amount;
  uint128 amount;
  uint128 account; // native funds from client to pay for processing
  addr_std_fixed tip3_wallet;
  addr_std_fixed client_addr;
  uint32 order_finish_time;
};
using OrderInfoWithIdx = std::pair<unsigned, OrderInfo>;

struct DetailsInfo {
  uint128 price;
  uint128 min_amount;
  uint128 sell_amount;
  uint128 buy_amount;
};

// usage from debot:
// co_await tip3.tail_call<OrderRet>(price_addr, gr).lendOwnership(...)

__interface IPrice {

  [[internal, noaccept, answer_id]]
  OrderRet onTip3LendOwnership(
    uint128 balance, uint32 lend_finish_time, uint256 pubkey, uint256 internal_owner,
    cell payload, address answer_addr) = 201;

  [[internal, noaccept, answer_id]]
  OrderRet buyTip3(uint128 amount, address receive_tip3, uint32 order_finish_time) = 202;

  [[internal, noaccept]]
  void processQueue() = 203;

  // will cancel all orders with this sender's receive_wallet
  [[internal, noaccept]]
  void cancelSell() = 204;

  // will cancel all orders with this sender's answer_addr
  [[internal, noaccept]]
  void cancelBuy() = 205;
};
using IPricePtr = handle<IPrice>;

struct DPrice {
  uint128 price_;
  uint128 sells_amount_;
  uint128 buys_amount_;
  addr_std_fixed flex_;
  uint128 min_amount_;
  uint8 deals_limit_; // limit for processed deals in one request

  IFLeXNotifyPtr notify_addr_;

  int8 workchain_id_;

  TonsConfig tons_cfg_;
  cell tip3_code_;
  Tip3Config tip3cfg_;

  queue<OrderInfo> sells_;
  queue<OrderInfo> buys_;
};

__interface EPrice {
};

__always_inline
std::pair<StateInit, uint256> prepare_price_state_init_and_addr(DPrice price_data, cell price_code) {
  cell price_data_cl = prepare_persistent_data<IPrice, void, DPrice>({}, price_data);
  StateInit price_init {
    /*split_depth*/{}, /*special*/{},
    price_code, price_data_cl, /*library*/{}
  };
  cell price_init_cl = build(price_init).make_cell();
  return { price_init, uint256(tvm_hash(price_init_cl)) };
}

}} // namespace tvm::schema

#include "PriceXchg.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

// Contract for trading price for tip3/tip3 exchange
// First tip3 in pair is major and terms "sell", "buy", amount are related to the first tip3 in pair
// Second tip3 is called "minor"

static constexpr unsigned ok = 0;
struct ec : tvm::error_code {
  static constexpr unsigned out_of_tons                    = 100; // partially processed because out of tons
  static constexpr unsigned deals_limit                    = 101; // partially processed because deals limit
  static constexpr unsigned not_enough_tons_to_process     = 102;
  static constexpr unsigned not_enough_tokens_amount       = 103;
  static constexpr unsigned too_big_tokens_amount          = 104;
  static constexpr unsigned different_workchain_id         = 105;
  static constexpr unsigned unverified_tip3_wallet         = 106;
  static constexpr unsigned canceled                       = 107;
  static constexpr unsigned expired                        = 108;
};

// For tip3 we have lend_finish_time, when ownership will return back to its original owner.
// And we need some safe period to not process orders with soon expiring tip3 ownership
static constexpr unsigned safe_delay_period = 5 * 60;

__always_inline
bool is_active_time(uint32 order_finish_time) {
  return tvm_now() + safe_delay_period < order_finish_time.get();
}

// calculate cost (amount of minor tip3 to match the "amount" of major tip3)
__always_inline
std::optional<uint128> minor_cost(uint128 amount, price_t price) {
  unsigned cost = __builtin_tvm_muldivr(amount.get(), price.numerator().get(), price.denominator().get());
  if (cost >> 128)
    return {};
  return uint128{cost};
}

// class for processing orders queues and performing deals
class dealer {
public:
  // returns (sell_out_of_tons, buy_out_of_tons, deal_amount)
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

    ITONTokenWalletPtr(sell.tip3_wallet_provide)(Grams(tons_cfg_.transfer_tip3.get()), IGNORE_ACTION_ERRORS).
      transfer(buy.tip3_wallet_receive, deal_amount, last_tip3_sell, sell.tip3_wallet_provide);
    ITONTokenWalletPtr(buy.tip3_wallet_provide)(Grams(tons_cfg_.transfer_tip3.get()), IGNORE_ACTION_ERRORS).
      transfer(sell.tip3_wallet_receive, *buy_payment, last_tip3_buy, buy.tip3_wallet_provide);

    notify_addr_(Grams(tons_cfg_.send_notify.get()), IGNORE_ACTION_ERRORS).
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
        IPriceCallbackPtr(ord.client_addr)(Grams(ord.account.get()), IGNORE_ACTION_ERRORS).
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
          IPriceXchgPtr(address{tvm_myaddr()})(Grams(tons_cfg_.process_queue.get()), IGNORE_ACTION_ERRORS).
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
          ITONTokenWalletPtr(sell.tip3_wallet_provide)(Grams(tons_cfg_.return_ownership.get()), IGNORE_ACTION_ERRORS).
            returnOwnership();
          IPriceCallbackPtr(sell.client_addr)(Grams(sell.account.get()), IGNORE_ACTION_ERRORS).
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
          ITONTokenWalletPtr(buy.tip3_wallet_provide)(Grams(tons_cfg_.return_ownership.get()), IGNORE_ACTION_ERRORS).
            returnOwnership();
          IPriceCallbackPtr(buy.client_addr)(Grams(buy.account.get()), IGNORE_ACTION_ERRORS).
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
      if (!sell.amount) {
        sells_.pop();
        OrderRet ret { uint32(ok), sell.original_amount, uint128{0} };
        if (sell_idx == sell_idx_cur)
          ret_ = ret;
        IPriceCallbackPtr(sell.client_addr)(Grams(sell.account.get()), IGNORE_ACTION_ERRORS).
          onOrderFinished(ret, bool_t{true});
        sell_opt.reset();
      }
      if (!buy.amount) {
        buys_.pop();
        OrderRet ret { uint32(ok), buy.original_amount, uint128{0} };
        if (buy_idx == buy_idx_cur)
          ret_ = ret;
        IPriceCallbackPtr(buy.client_addr)(Grams(buy.account.get()), IGNORE_ACTION_ERRORS).
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
  IFLeXNotifyPtr notify_addr_;
  price_t price_;
  unsigned deals_limit_;
  TonsConfig tons_cfg_;
  uint128 sells_amount_;
  big_queue<OrderInfoXchg> sells_;
  uint128 buys_amount_;
  big_queue<OrderInfoXchg> buys_;
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
                               IFLeXNotifyPtr notify_addr,
                               price_t price, uint8 deals_limit, TonsConfig tons_cfg,
                               unsigned sell_idx, unsigned buy_idx,
                               uint128 sells_amount, big_queue<OrderInfoXchg> sells,
                               uint128 buys_amount, big_queue<OrderInfoXchg> buys) {
  dealer d{tip3root_sell, tip3root_buy, notify_addr, price, deals_limit.get(), tons_cfg,
           sells_amount, sells, buys_amount, buys, {}};
  d.process_queue(sell_idx, buy_idx);
  return { d.sells_amount_, d.sells_, d.buys_amount_, d.buys_, d.ret_ };
}

__attribute__((noinline))
std::pair<big_queue<OrderInfoXchg>, uint128> cancel_order_impl(
    big_queue<OrderInfoXchg> orders, addr_std_fixed client_addr, uint128 all_amount, bool_t sell,
    Grams return_ownership, Grams process_queue, Grams incoming_val) {
  bool is_first = true;
  for (auto it = orders.begin(); it != orders.end();) {
    auto next_it = std::next(it);
    auto ord = *it;
    if (ord.client_addr == client_addr) {
      unsigned minus_val = process_queue.get();
      ITONTokenWalletPtr(ord.tip3_wallet_provide)(return_ownership, IGNORE_ACTION_ERRORS).
        returnOwnership();
      minus_val += return_ownership.get();

      unsigned plus_val = ord.account.get() + (is_first ? incoming_val.get() : 0);
      is_first = false;
      if (plus_val > minus_val) {
        unsigned ret_val = plus_val - minus_val;
        OrderRet ret { uint32(ec::canceled), ord.original_amount - ord.amount, uint128{0} };
        IPriceCallbackPtr(ord.client_addr)(Grams(ret_val), IGNORE_ACTION_ERRORS).
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
      uint128 lend_balance, uint32 lend_finish_time, uint256 pubkey, uint256 internal_owner,
      cell payload_cl, address answer_addr) {
    auto [tip3_wallet, value] = int_sender_and_value();
    ITONTokenWalletPtr wallet_in(tip3_wallet);
    Grams ret_owner_gr(tons_cfg_.return_ownership.get());

    // to send answer to the original caller (caller->tip3wallet->price->caller)
    set_int_sender(answer_addr);
    set_int_return_value(tons_cfg_.order_answer.get());
    set_int_return_flag(IGNORE_ACTION_ERRORS);

    auto min_value = onTip3LendOwnershipMinValue();

    auto args = parse<PayloadArgs>(payload_cl.ctos());
    bool_t is_sell = args.sell;
    auto amount = args.amount;
    auto minor_amount = minor_cost(amount, price_);
    unsigned err = 0;
    if (value.get() < min_value)
      err = ec::not_enough_tons_to_process;
    else if (is_sell ? !verify_tip3_addr(major_tip3cfg_, tip3_wallet, pubkey, internal_owner) :
                       !verify_tip3_addr(minor_tip3cfg_, tip3_wallet, pubkey, internal_owner))
      err = ec::unverified_tip3_wallet;
    else if (!minor_amount)
      err = ec::too_big_tokens_amount;
    else if (amount < min_amount_)
      err = ec::not_enough_tokens_amount;
    else if (lend_balance < (is_sell ? amount : *minor_amount))
      err = ec::too_big_tokens_amount;

    if (err)
      return on_ord_fail(err, wallet_in);

    uint128 account = uint128(value.get()) - tons_cfg_.process_queue - tons_cfg_.order_answer;

    OrderInfoXchg ord{amount, amount, account, tip3_wallet, args.receive_tip3_wallet, args.client_addr, lend_finish_time};
    unsigned sell_idx = 0;
    unsigned buy_idx = 0;
    if (is_sell) {
      sells_.push(ord);
      sells_amount_ += ord.amount;
      sell_idx = sells_.back_with_idx().first;
    } else {
      buys_.push(ord);
      buys_amount_ += ord.amount;
      buy_idx = buys_.back_with_idx().first;
    }

    auto [sells_amount, sells, buys_amount, buys, ret] =
      process_queue_impl(major_tip3cfg_.root_address, minor_tip3cfg_.root_address,
                         notify_addr_, price_, deals_limit_, tons_cfg_,
                         sell_idx, buy_idx,
                         sells_amount_, sells_, buys_amount_, buys_);
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
                         sells_amount_, sells_, buys_amount_, buys_);
    sells_ = sells;
    buys_ = buys;
    sells_amount_ = sells_amount;
    buys_amount_ = buys_amount;
    if (sells_.empty() && buys_.empty())
      suicide(flex_);
  }

  __always_inline
  void cancelSell() {
    addr_std_fixed client_addr = int_sender();
    auto value = int_value();
    auto [sells, sells_amount] =
      cancel_order_impl(sells_, client_addr, sells_amount_, bool_t{true},
                        Grams(tons_cfg_.return_ownership.get()),
                        Grams(tons_cfg_.process_queue.get()), value);
    sells_ = sells;
    sells_amount_ = sells_amount;

    if (sells_.empty() && buys_.empty())
      suicide(flex_);
  }

  __always_inline
  void cancelBuy() {
    addr_std_fixed client_addr = int_sender();
    auto value = int_value();
    auto [buys, buys_amount] =
      cancel_order_impl(buys_, client_addr, buys_amount_, bool_t{false},
                        Grams(tons_cfg_.return_ownership.get()),
                        Grams(tons_cfg_.process_queue.get()), value);
    buys_ = buys;
    buys_amount_ = buys_amount;

    if (sells_.empty() && buys_.empty())
      suicide(flex_);
  }

  // ========== getters ==========
  __always_inline
  DetailsInfoXchg getDetails() {
    return { getPriceNum(), getPriceDenum(), getMinimumAmount(), getSellAmount(), getBuyAmount() };
  }

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
  bool verify_tip3_addr(Tip3Config cfg,
                        address tip3_wallet, uint256 wallet_pubkey, uint256 internal_owner) {
    auto expected_address = expected_wallet_address(cfg, wallet_pubkey, internal_owner);
    return std::get<addr_std>(tip3_wallet()).address == expected_address;
  }
  __always_inline
  uint256 expected_wallet_address(Tip3Config cfg, uint256 wallet_pubkey, uint256 internal_owner) {
    std::optional<address> owner_addr;
    if (internal_owner)
      owner_addr = address::make_std(workchain_id_, internal_owner);
    DTONTokenWallet wallet_data {
      cfg.name, cfg.symbol, cfg.decimals,
      TokensType(0), cfg.root_public_key, wallet_pubkey,
      cfg.root_address, owner_addr, {}, tip3_code_, {}, workchain_id_
    };
    return prepare_wallet_state_init_and_addr(wallet_data).second;
  }

  __always_inline
  OrderRet on_ord_fail(unsigned ec, ITONTokenWalletPtr wallet_in) {
    auto incoming_value = int_value().get();
    tvm_rawreserve(tvm_balance() - incoming_value, rawreserve_flag::up_to);
    set_int_return_flag(SEND_ALL_GAS);
    wallet_in(Grams(tons_cfg_.return_ownership.get()), IGNORE_ACTION_ERRORS).returnOwnership();
    return { uint32(ec), {}, {} };
  }
};

DEFINE_JSON_ABI(IPriceXchg, DPriceXchg, EPriceXchg);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(PriceXchg, IPriceXchg, DPriceXchg)

#pragma once

#include <tvm/schema/message.hpp>

#include <tvm/replay_attack_protection/timestamp.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/small_dict_map.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/big_queue.hpp>
#include <tvm/string.hpp>
#include <tvm/numeric_limits.hpp>

#include "Flex.hpp"
#include "PriceCommon.hpp"
#include "TONTokenWallet.hpp"

namespace tvm { namespace schema {

using ITONTokenWalletPtr = handle<ITONTokenWallet>;

struct RationalPrice {
  uint128 numerator() const { return num; }
  uint128 denominator() const { return denum; }
  uint128 num;
  uint128 denum;
};
using price_t = RationalPrice;

struct PayloadArgs {
  bool_t sell;
  uint128 amount;
  addr_std_fixed receive_tip3_wallet;
  addr_std_fixed client_addr;
};

struct OrderInfoXchg {
  uint128 original_amount;
  uint128 amount;
  uint128 account; // native funds from client to pay for processing
  addr_std_fixed tip3_wallet_provide;
  addr_std_fixed tip3_wallet_receive;
  addr_std_fixed client_addr;
  uint32 order_finish_time;
};
using OrderInfoXchgWithIdx = std::pair<unsigned, OrderInfoXchg>;

struct DetailsInfoXchg {
  uint128 price_num;
  uint128 price_denum;
  uint128 min_amount;
  uint128 sell_amount;
  uint128 buy_amount;
};

__interface IPriceXchg {

  [[internal, noaccept, answer_id]]
  OrderRet onTip3LendOwnership(
    uint128 balance, uint32 lend_finish_time, uint256 pubkey, uint256 internal_owner,
    cell payload, address answer_addr) = 201;

  [[internal, noaccept]]
  void processQueue() = 203;

  // will cancel all orders with this sender's receive_wallet
  [[internal, noaccept]]
  void cancelSell() = 204;

  // will cancel all orders with this sender's answer_addr
  [[internal, noaccept]]
  void cancelBuy() = 205;
};
using IPriceXchgPtr = handle<IPriceXchg>;

struct DPriceXchg {
  price_t price_;
  uint128 sells_amount_;
  uint128 buys_amount_;
  addr_std_fixed flex_;
  uint128 min_amount_;
  uint8 deals_limit_; // limit for processed deals in one request

  IFLeXNotifyPtr notify_addr_;

  int8 workchain_id_;

  TonsConfig tons_cfg_;
  cell tip3_code_;
  Tip3Config major_tip3cfg_;
  Tip3Config minor_tip3cfg_;

  big_queue<OrderInfoXchg> sells_;
  big_queue<OrderInfoXchg> buys_;
};

__interface EPriceXchg {
};

__always_inline
std::pair<StateInit, uint256> prepare_price_xchg_state_init_and_addr(DPriceXchg price_data, cell price_code) {
  cell price_data_cl = prepare_persistent_data<IPriceXchg, void, DPriceXchg>({}, price_data);
  StateInit price_init {
    /*split_depth*/{}, /*special*/{},
    price_code, price_data_cl, /*library*/{}
  };
  cell price_init_cl = build(price_init).make_cell();
  return { price_init, uint256(tvm_hash(price_init_cl)) };
}

}} // namespace tvm::schema

#include "TradingPair.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

class TradingPair final : public smart_interface<ITradingPair>, public DTradingPair {
public:
  struct error_code : tvm::error_code {
    static constexpr unsigned not_enough_tons = 101;
  };

  __always_inline
  bool_t onDeploy() {
    require(int_value().get() > deploy_value_, error_code::not_enough_tons);

    tvm_rawreserve(deploy_value_.get(), rawreserve_flag::up_to);
    set_int_return_flag(SEND_ALL_GAS);
    return bool_t{true};
  }

  __always_inline
  address getFLeXAddr() {
    return flex_addr_;
  }

  __always_inline
  address getTip3Root() {
    return tip3_root_;
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(ITradingPair, void)

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }
};

DEFINE_JSON_ABI(ITradingPair, DTradingPair, ETradingPair);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(TradingPair, ITradingPair, DTradingPair)

#pragma once

#include <tvm/schema/message.hpp>

#include <tvm/replay_attack_protection/timestamp.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>

namespace tvm { namespace schema {

__interface ITradingPair {

  [[internal, noaccept, answer_id]]
  bool_t onDeploy();

  // ========== getters ==========
  [[getter]]
  address getFLeXAddr();

  [[getter]]
  address getTip3Root();
};
using ITradingPairPtr = handle<ITradingPair>;

struct DTradingPair {
  address flex_addr_;
  address tip3_root_;
  uint128 deploy_value_; // required minimum value to deploy TradingPair
};

__interface ETradingPair {
};

// Prepare Trading Pair StateInit structure and expected contract address (hash from StateInit)
inline
std::pair<StateInit, uint256> prepare_trading_pair_state_init_and_addr(DTradingPair pair_data, cell pair_code) {
  cell pair_data_cl = prepare_persistent_data<ITradingPair, void, DTradingPair>({}, pair_data);
  StateInit pair_init {
    /*split_depth*/{}, /*special*/{},
    pair_code, pair_data_cl, /*library*/{}
  };
  cell pair_init_cl = build(pair_init).make_cell();
  return { pair_init, uint256(tvm_hash(pair_init_cl)) };
}

}} // namespace tvm::schema

#include "XchgPair.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

class XchgPair final : public smart_interface<IXchgPair>, public DXchgPair {
public:
  struct error_code : tvm::error_code {
    static constexpr unsigned not_enough_tons = 101;
  };

  __always_inline
  bool_t onDeploy() {
    require(int_value().get() > deploy_value_, error_code::not_enough_tons);

    tvm_rawreserve(deploy_value_.get(), rawreserve_flag::up_to);
    set_int_return_flag(SEND_ALL_GAS);
    return bool_t{true};
  }

  __always_inline
  address getFLeXAddr() {
    return flex_addr_;
  }

  __always_inline
  address getTip3MajorRoot() {
    return tip3_major_root_;
  }

  __always_inline
  address getTip3MinorRoot() {
    return tip3_minor_root_;
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IXchgPair, void)

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }
};

DEFINE_JSON_ABI(IXchgPair, DXchgPair, EXchgPair);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(XchgPair, IXchgPair, DXchgPair)
#pragma once

#include <tvm/schema/message.hpp>

#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>

namespace tvm { namespace schema {

__interface IXchgPair {

  [[internal, noaccept, answer_id]]
  bool_t onDeploy();

  // ========== getters ==========
  [[getter]]
  address getFLeXAddr();

  // address of major tip3 token root
  [[getter]]
  address getTip3MajorRoot();

  // address of minor tip3 token root
  [[getter]]
  address getTip3MinorRoot();
};
using IXchgPairPtr = handle<IXchgPair>;

struct DXchgPair {
  address flex_addr_;
  address tip3_major_root_;
  address tip3_minor_root_;
  uint128 deploy_value_; // required minimum value to deploy TradingPair
};

__interface EXchgPair {
};

// Prepare Exchange Pair StateInit structure and expected contract address (hash from StateInit)
inline
std::pair<StateInit, uint256> prepare_xchg_pair_state_init_and_addr(DXchgPair pair_data, cell pair_code) {
  cell pair_data_cl = prepare_persistent_data<IXchgPair, void, DXchgPair>({}, pair_data);
  StateInit pair_init {
    /*split_depth*/{}, /*special*/{},
    pair_code, pair_data_cl, /*library*/{}
  };
  cell pair_init_cl = build(pair_init).make_cell();
  return { pair_init, uint256(tvm_hash(pair_init_cl)) };
}

}} // namespace tvm::schema

