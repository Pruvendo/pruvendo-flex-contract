#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/string.hpp>
#include <tvm/debot.hpp>
#include <tvm/default_support_functions.hpp>
#include <tvm/Console.hpp>
#include "Price.hpp"
#include "TradingPair.hpp"
#include "XchgPair.hpp"
#include "Flex.hpp"
#include "TONTokenWallet.hpp"
#include "FlexClient.hpp"

using namespace tvm;
using namespace schema;
using namespace debot;

__interface [[no_pubkey]] IFlexDebot {

  [[external]]
  void constructor() = 1;

  [[external]]
  resumable<void> start() = 2;
};

struct DFlexDebot {
  uint256 deployer_pubkey_;
  std::optional<IFlexPtr> flex_;
  std::optional<IFlexClientPtr> client_;
};

__interface EFlexDebot {
};

class FlexDebot final : public smart_interface<IFlexDebot>, public DFlexDebot {
  static constexpr unsigned one_full_ton_size = 1000000000;

  struct error_code : tvm::error_code {
    static constexpr unsigned unexpected_pair_address = 101;
  };

  IConsolePtr cout_ptr_ = IConsolePtr(address::make_std(schema::int8{0}, schema::uint256{0}));

  __always_inline IConsolePtr::proxy cout() {
    return cout_ptr_();
  }
  __always_inline
  auto printf(string fmt) {
    cell params = builder().endc();
    return cout().printf(fmt, params);
  }
  template<typename... Args>
  __always_inline
  auto printf(string fmt, Args... args) {
    auto tup = std::make_tuple(args...);
    auto chain = make_chain_tuple(tup);
    cell params = build(chain).endc();
    return cout().printf(fmt, params);
  }
public:
  __always_inline
  void constructor() override {
  }

  __always_inline
  resumable<void> start() override {
    uint128 min_amount{1};
    co_await cout().print("Hello, I am FLeX Debot!");
    do {
      if (!flex_) {
        flex_ = IFlexPtr(co_await cout().inputAddress("Flex address:", "FLEX"));
        bool_t initialized = co_await flex_->run().isFullyInitialized();
        if (initialized) {
          co_await printf("Flex is fully initialized: {address}\n", flex_->get());
        } else {
          co_await printf("Flex is NOT fully initialized: {address}\n", flex_->get());
          flex_.reset();
          continue;
        }
      }
      auto tons_cfg = co_await flex_->run().getTonsCfg();
      if (!client_) {
        client_ = IFlexClientPtr(co_await cout().inputAddress("Flex client address:", "FLEX_CLIENT"));
        co_await client_->debot_ext_in().setFlexCfg(tons_cfg, flex_->get());
      }
      co_await cout().iAmHome();
      co_await printf("Flex: {address}", flex_->get());
      co_await printf("client: {address}", client_->get());

      co_await printf("1). Buy tip3 tokens\n"
                      "2). Sell tip3 tokens\n"
                      "3). Buy tip3/tip3 tokens\n"
                      "4). Sell tip3/tip3 tokens\n"
                      "5). Cancel order\n"
                      "6). Deploy wrapper\n"
                      "7). Exit");
      auto select = co_await cout().inputUint256("");
      switch (select.get()) {
      case 1: {
        auto my_tip3 = ITONTokenWalletPtr(co_await cout().inputAddress("Token wallet address (to receive tokens):", "TIP3WALLET"));
        auto tip3info = co_await my_tip3.run().getDetails();

        co_await cout().print(tip3info.name);
        co_await printf("Tip3 root address = {address}", tip3info.root_address);
        auto trade_pair = ITradingPairPtr(co_await flex_->run().getSellTradingPair(tip3info.root_address));
        co_await printf("Sell pair is {address}", trade_pair.get());

        cell price_code = co_await flex_->run().getSellPriceCode(tip3info.root_address);
        co_await client_->debot_ext_in().setFlexWalletCode(tip3info.code);
        if (1 != co_await cout().getAccountType(trade_pair.get())) {
          co_await printf("Sell Pair is not yet exists and need to be deployed:");
          co_await printf("Deploying Sell Pair for:");
          co_await cout().print(tip3info.name);
          auto deploy_value = uint128((co_await cout().inputTONs("Deploy value (extra will return): ")).get());

          auto notify_addr = co_await cout().inputAddress("Notify address:", "FLEX NOTIFY");

          auto deployed_pair = co_await client_->debot_ext_in().deployTradingPair(
            tip3info.root_address, tons_cfg.trading_pair_deploy, deploy_value, min_amount, notify_addr);
          co_await printf("Sell pair deployed: {address}", deployed_pair);
        }
        Tip3Config tip3cfg {
          .name = tip3info.name,
          .symbol = tip3info.symbol,
          .decimals = tip3info.decimals,
          .root_public_key = tip3info.root_public_key,
          .root_address = tip3info.root_address
        };

        auto price = uint128((co_await cout().inputTONs("Price in TONs:")).get());
        auto amount = uint128((co_await cout().inputUint256("Amount:")).get());
        auto minutes = co_await cout().inputUint256("Order time in minutes:");
        uint32 order_finish_time((tvm_now() + minutes * 60).get());

        auto deals_limit = co_await flex_->run().getDealsLimit();

        uint128 deploy_value;
        uint128 min_deploy_value = price * amount + tons_cfg.process_queue + tons_cfg.order_answer;
        do {
          co_await printf("Required value is {value}", uint256(min_deploy_value.get()));
          deploy_value = uint128((co_await cout().inputTONs("Send value (extra will return): ")).get());
        } while (deploy_value < min_deploy_value);

        auto notify_addr = co_await trade_pair.run().getNotifyAddr();

        IPricePtr price_addr(co_await client_->debot_ext_in().deployPriceWithBuy(
          price, amount, order_finish_time, min_amount, deals_limit, deploy_value, price_code, my_tip3.get(),
          tip3cfg, notify_addr));

        //auto price_info = co_await price_addr.run().getDetails();
        //co_await printf("price getter: {value}", uint256(price_info.price.get()));
        //co_await printf("sell amount in price: {uint128}", price_info.sell_amount);
        //co_await printf("buy amount in price: {uint128}", price_info.buy_amount);
      } break;
      case 2: {
        auto my_tip3 = ITONTokenWalletPtr(co_await cout().inputAddress("Token wallet address:", "TIP3WALLET"));
        auto tip3info = co_await my_tip3.run().getDetails();
        co_await cout().print(tip3info.name);
        co_await printf("Tip3 root address = {address}", tip3info.root_address);
        // co_await printf("Token \"{bytes}\"", tip3info.name);
        auto trade_pair = ITradingPairPtr(co_await flex_->run().getSellTradingPair(tip3info.root_address));
        co_await printf("Sell pair is {address}", trade_pair.get());
        address receive_wallet = client_->get();

        co_await client_->debot_ext_in().setFlexWalletCode(tip3info.code);

        cell price_code = co_await flex_->run().getSellPriceCode(tip3info.root_address);
        if (1 != co_await cout().getAccountType(trade_pair.get())) {
          co_await printf("Deploying Sell Pair for:");
          co_await cout().print(tip3info.name);
          auto deploy_value = uint128((co_await cout().inputTONs("Deploy value (extra will return): ")).get());
          auto notify_addr = co_await cout().inputAddress("Notify address:", "FLEX NOTIFY");
          auto deployed_pair = co_await client_->debot_ext_in().deployTradingPair(
            tip3info.root_address, tons_cfg.trading_pair_deploy, deploy_value, min_amount, notify_addr);
          co_await printf("Sell pair deployed: {address}", deployed_pair);
        }

        Tip3Config tip3cfg {
          .name = tip3info.name,
          .symbol = tip3info.symbol,
          .decimals = tip3info.decimals,
          .root_public_key = tip3info.root_public_key,
          .root_address = tip3info.root_address
        };

        auto price = uint128((co_await cout().inputTONs("Price in TONs:")).get());
        auto amount = uint128((co_await cout().inputUint256("Amount:")).get());
        auto minutes = co_await cout().inputUint256("Order time in minutes:");
        uint32 lend_finish_time((tvm_now() + minutes * 60).get());

        auto deals_limit = co_await flex_->run().getDealsLimit();

        uint128 tons_value;
        auto min_value = tons_cfg.process_queue + tons_cfg.transfer_tip3 +
          tons_cfg.return_ownership + tons_cfg.order_answer;
        do {
          co_await printf("Required value is {value}", uint256(min_value.get()));
          tons_value = uint128((co_await cout().inputTONs("Processing value (extra will return):")).get());
        } while (tons_value < min_value);

        auto notify_addr = co_await trade_pair.run().getNotifyAddr();

        IPricePtr price_addr(co_await client_->debot_ext_in().deployPriceWithSell(
          price, amount, lend_finish_time, min_amount, deals_limit, tons_value, price_code,
          my_tip3.get(), receive_wallet, tip3cfg, notify_addr));

        // auto price_info = co_await price_addr.run().getDetails();
        // co_await printf("price getter: {value}", uint256(price_info.price.get()));
        // co_await printf("sell amount in price: {uint128}", price_info.sell_amount);
        // co_await printf("buy amount in price: {uint128}", price_info.buy_amount);
      } break;
      case 3: { // buy major tip3 for minor tip3
        ITONTokenWalletPtr my_tip3_receive(
          co_await cout().inputAddress("Tip3 wallet address (to buy tokens):", "TIP3WALLET"));
        ITONTokenWalletPtr my_tip3_provide(
          co_await cout().inputAddress("Tip3 wallet address (to provide tokens):", "TIP3WALLET"));

        auto tip3info_major = co_await my_tip3_receive.run().getDetails();
        auto tip3info_minor = co_await my_tip3_provide.run().getDetails();

        if (tvm_hash(tip3info_major.code) != tvm_hash(tip3info_minor.code)) {
          co_await cout().print("Tip3 wallets have different code\n");
          continue;
        }

        co_await client_->debot_ext_in().setFlexWalletCode(tip3info_major.code);

        co_await cout().print(tip3info_major.name);
        co_await printf("major tip3 root address = {address}", tip3info_major.root_address);
        co_await cout().print(tip3info_minor.name);
        co_await printf("minor tip3 root address = {address}", tip3info_minor.root_address);

        auto trade_pair = IXchgPairPtr(
          co_await flex_->run().getXchgTradingPair(tip3info_major.root_address, tip3info_minor.root_address)
          );
        co_await printf("Xchg Pair is {address}", trade_pair.get());

        TonsConfig tonsCfg = co_await flex_->run().getTonsCfg();

        cell price_code = co_await flex_->run().getXchgPriceCode(tip3info_major.root_address, tip3info_minor.root_address);
        if (1 != co_await cout().getAccountType(trade_pair.get())) {
          co_await printf("Xchg Pair is not yet exists and need to be deployed:");
          co_await printf("Deploying Xchg Pair for:");
          co_await cout().print(tip3info_major.name);
          co_await cout().print(tip3info_minor.name);
          auto deploy_value = uint128((co_await cout().inputTONs("Deploy value (extra will return): ")).get());
          auto notify_addr = co_await cout().inputAddress("Notify address:", "FLEX NOTIFY");
          auto deployed_pair = co_await client_->debot_ext_in().deployXchgPair(
            tip3info_major.root_address, tip3info_minor.root_address,
            tons_cfg.trading_pair_deploy, deploy_value, min_amount, notify_addr);
          co_await printf("Sell pair deployed: {address}", deployed_pair);
        }

        Tip3Config tip3_cfg_major {
          .name = tip3info_major.name,
          .symbol = tip3info_major.symbol,
          .decimals = tip3info_major.decimals,
          .root_public_key = tip3info_major.root_public_key,
          .root_address = tip3info_major.root_address
        };
        Tip3Config tip3_cfg_minor {
          .name = tip3info_minor.name,
          .symbol = tip3info_minor.symbol,
          .decimals = tip3info_minor.decimals,
          .root_public_key = tip3info_minor.root_public_key,
          .root_address = tip3info_minor.root_address
        };
        auto price = uint128((co_await cout().inputTONs("Price in minor tokens for one major token:")).get());
        auto amount = uint128((co_await cout().inputUint256("Amount (major):")).get());
        auto minor_amount = uint128{__builtin_tvm_muldivr(amount.get(), price.get(), one_full_ton_size)};
        if (minor_amount.get() >> 128) {
          co_await printf("Too big minor amount (>128 bit)");
          continue;
        }
        co_await printf("Minor amount: {uint128}", minor_amount);

        auto minutes = co_await cout().inputUint256("Order time in minutes:");
        uint32 lend_finish_time((tvm_now() + minutes * 60).get());

        auto deals_limit = co_await flex_->run().getDealsLimit();
        auto notify_addr = co_await trade_pair.run().getNotifyAddr();

        uint128 tons_value;
        auto min_value = tonsCfg.process_queue + tonsCfg.transfer_tip3 + tonsCfg.send_notify +
          tonsCfg.return_ownership + tonsCfg.order_answer + 1000000000;
        do {
          co_await printf("Required value is {value}", uint256(min_value.get()));
          tons_value = uint128((co_await cout().inputTONs("Processing value (extra will return):")).get());
        } while (tons_value < min_value);

        IPriceXchgPtr price_addr(co_await client_->debot_ext_in().deployPriceXchg(
          bool_t{false}, price, uint128{one_full_ton_size}, amount, minor_amount, lend_finish_time, min_amount, deals_limit,
          tons_value, price_code, my_tip3_provide.get(), my_tip3_receive.get(),
          tip3_cfg_major, tip3_cfg_minor, notify_addr
        ));
      } break;
      case 4: { // sell major tip3 for minor tip3
        ITONTokenWalletPtr my_tip3_provide(
          co_await cout().inputAddress("Tip3 wallet address (to sell tokens):", "TIP3WALLET"));
        ITONTokenWalletPtr my_tip3_receive(
          co_await cout().inputAddress("Tip3 wallet address (to receive tokens):", "TIP3WALLET"));

        auto tip3info_major = co_await my_tip3_provide.run().getDetails();
        auto tip3info_minor = co_await my_tip3_receive.run().getDetails();

        if (tvm_hash(tip3info_major.code) != tvm_hash(tip3info_minor.code)) {
          co_await cout().print("Tip3 wallets have different code\n");
          continue;
        }

        co_await client_->debot_ext_in().setFlexWalletCode(tip3info_major.code);

        co_await cout().print(tip3info_major.name);
        co_await printf("major tip3 root address = {address}", tip3info_major.root_address);
        co_await cout().print(tip3info_minor.name);
        co_await printf("minor tip3 root address = {address}", tip3info_minor.root_address);

        auto trade_pair = IXchgPairPtr(
          co_await flex_->run().getXchgTradingPair(tip3info_major.root_address, tip3info_minor.root_address)
          );
        co_await printf("Xchg Pair is {address}", trade_pair.get());

        TonsConfig tonsCfg = co_await flex_->run().getTonsCfg();

        cell price_code = co_await flex_->run().getXchgPriceCode(tip3info_major.root_address, tip3info_minor.root_address);
        if (1 != co_await cout().getAccountType(trade_pair.get())) {
          co_await printf("Xchg Pair is not yet exists and need to be deployed:");
          co_await printf("Deploying Xchg Pair for:");
          co_await cout().print(tip3info_major.name);
          co_await cout().print(tip3info_minor.name);
          auto deploy_value = uint128((co_await cout().inputTONs("Deploy value (extra will return): ")).get());
          auto notify_addr = co_await cout().inputAddress("Notify address:", "FLEX NOTIFY");
          auto deployed_pair = co_await client_->debot_ext_in().deployXchgPair(
            tip3info_major.root_address, tip3info_minor.root_address, tons_cfg.trading_pair_deploy,
            deploy_value, min_amount, notify_addr);
          co_await printf("Sell pair deployed: {address}", deployed_pair);
        }

        Tip3Config tip3_cfg_major {
          .name = tip3info_major.name,
          .symbol = tip3info_major.symbol,
          .decimals = tip3info_major.decimals,
          .root_public_key = tip3info_major.root_public_key,
          .root_address = tip3info_major.root_address
        };
        Tip3Config tip3_cfg_minor {
          .name = tip3info_minor.name,
          .symbol = tip3info_minor.symbol,
          .decimals = tip3info_minor.decimals,
          .root_public_key = tip3info_minor.root_public_key,
          .root_address = tip3info_minor.root_address
        };
        auto price = uint128((co_await cout().inputTONs("Price in minor tokens for one major token:")).get());
        auto amount = uint128((co_await cout().inputUint256("Amount (major):")).get());
        auto minor_amount = uint128{__builtin_tvm_muldivr(amount.get(), price.get(), one_full_ton_size)};
        if (minor_amount.get() >> 128) {
          co_await printf("Too big minor amount (>128 bit)");
          continue;
        }
        co_await printf("Minor amount: {uint128}", minor_amount);

        auto minutes = co_await cout().inputUint256("Order time in minutes:");
        uint32 lend_finish_time((tvm_now() + minutes * 60).get());

        auto deals_limit = co_await flex_->run().getDealsLimit();

        uint128 tons_value;
        auto min_value = tonsCfg.process_queue + tonsCfg.transfer_tip3 + tonsCfg.send_notify +
          tonsCfg.return_ownership + tonsCfg.order_answer + 1000000000;
        do {
          co_await printf("Required value is {value}", uint256(min_value.get()));
          tons_value = uint128((co_await cout().inputTONs("Processing value (extra will return):")).get());
        } while (tons_value < min_value);

        auto notify_addr = co_await trade_pair.run().getNotifyAddr();

        IPriceXchgPtr price_addr(co_await client_->debot_ext_in().deployPriceXchg(
          bool_t{true}, price, uint128{one_full_ton_size}, amount, amount, lend_finish_time, min_amount, deals_limit,
          tons_value, price_code, my_tip3_provide.get(), my_tip3_receive.get(),
          tip3_cfg_major, tip3_cfg_minor, notify_addr
        ));
      } break;
      case 5: {
        co_await printf("1). Cancel sell\n"
                        "2). Cancel buy\n"
                        "3). Cancel tip3/tip3 sell\n"
                        "4). Cancel tip3/tip3 buy\n");
        auto notify_addr = co_await cout().inputAddress("Notify address:", "FLEX NOTIFY");
        auto select = co_await cout().inputUint256("");
        if (select == 1) {
          auto my_tip3 = ITONTokenWalletPtr(co_await cout().inputAddress("Token wallet address:", "TIP3WALLET"));
          auto tip3info = co_await my_tip3.run().getDetails();
          co_await cout().print(tip3info.name);
          co_await client_->debot_ext_in().setFlexWalletCode(tip3info.code);
          Tip3Config tip3cfg {
            .name = tip3info.name,
            .symbol = tip3info.symbol,
            .decimals = tip3info.decimals,
            .root_public_key = tip3info.root_public_key,
            .root_address = tip3info.root_address
          };
          cell price_code = co_await flex_->run().getSellPriceCode(tip3info.root_address);
          auto deals_limit = co_await flex_->run().getDealsLimit();
          auto price = uint128((co_await cout().inputTONs("Price in TONs:")).get());
          auto tons_value = uint128((co_await cout().inputTONs("Processing value (extra will return):")).get());
          co_await client_->debot_ext_in().cancelSellOrder(price, min_amount, deals_limit, tons_value,
            price_code, tip3cfg, notify_addr);
        } else if (select == 2) {
          auto my_tip3 = ITONTokenWalletPtr(co_await cout().inputAddress("Token wallet address:", "TIP3WALLET"));
          auto tip3info = co_await my_tip3.run().getDetails();
          co_await cout().print(tip3info.name);
          co_await client_->debot_ext_in().setFlexWalletCode(tip3info.code);
          Tip3Config tip3cfg {
            .name = tip3info.name,
            .symbol = tip3info.symbol,
            .decimals = tip3info.decimals,
            .root_public_key = tip3info.root_public_key,
            .root_address = tip3info.root_address
          };
          cell price_code = co_await flex_->run().getSellPriceCode(tip3info.root_address);
          auto deals_limit = co_await flex_->run().getDealsLimit();
          auto price = uint128((co_await cout().inputTONs("Price in TONs:")).get());
          auto tons_value = uint128((co_await cout().inputTONs("Processing value (extra will return):")).get());
          co_await client_->debot_ext_in().cancelBuyOrder(price, min_amount, deals_limit, tons_value, price_code,
            tip3cfg, notify_addr);
        } else if (select == 3 || select == 4) { // cancel tip3/tip3 sell/buy
          ITONTokenWalletPtr major_tip3(
          	co_await cout().inputAddress("Major Tip3 wallet address:", "TIP3WALLET"));
		      ITONTokenWalletPtr minor_tip3(
		        co_await cout().inputAddress("Minor Tip3 wallet address:", "TIP3WALLET"));

		      auto tip3info_major = co_await major_tip3.run().getDetails();
		      auto tip3info_minor = co_await minor_tip3.run().getDetails();

		      if (tvm_hash(tip3info_major.code) != tvm_hash(tip3info_minor.code)) {
		        co_await cout().print("Tip3 wallets have different code\n");
		        continue;
		      }
		      co_await client_->debot_ext_in().setFlexWalletCode(tip3info_major.code);
		      co_await cout().print(tip3info_major.name);
		      co_await printf("major tip3 root address = {address}", tip3info_major.root_address);
		      co_await cout().print(tip3info_minor.name);
		      co_await printf("minor tip3 root address = {address}", tip3info_minor.root_address);
		      Tip3Config tip3_cfg_major {
		        .name = tip3info_major.name,
		        .symbol = tip3info_major.symbol,
		        .decimals = tip3info_major.decimals,
		        .root_public_key = tip3info_major.root_public_key,
		        .root_address = tip3info_major.root_address
		      };
		      Tip3Config tip3_cfg_minor {
		        .name = tip3info_minor.name,
		        .symbol = tip3info_minor.symbol,
		        .decimals = tip3info_minor.decimals,
		        .root_public_key = tip3info_minor.root_public_key,
		        .root_address = tip3info_minor.root_address
		      };

          cell xchg_price_code = co_await flex_->run().getXchgPriceCode(tip3_cfg_major.root_address, tip3_cfg_minor.root_address);
          auto deals_limit = co_await flex_->run().getDealsLimit();
          auto price = uint128((co_await cout().inputTONs("Price in TONs:")).get());
          auto tons_value = uint128((co_await cout().inputTONs("Processing value (extra will return):")).get());
          co_await client_->debot_ext_in().cancelXchgOrder(
            bool_t{select == 3}, price, uint128{one_full_ton_size}, min_amount, deals_limit, tons_value,
            xchg_price_code, tip3_cfg_major, tip3_cfg_minor, notify_addr
            );
        }
        break;
      }
      case 6: {
        co_await cout().print("Deploying wrapper...");

        cell ext_wallet_code = co_await cout().inputCode("../tokens/fungible/TONTokenWallet.tvc");
        cell flex_wallet_code = co_await cout().inputCode("../tokens/fungible/FlexWallet.tvc");
        cell flex_wrapper_code = co_await cout().inputCode("../tokens/fungible/Wrapper.tvc");

        co_await client_->debot_ext_in().setExtWalletCode(ext_wallet_code);
        co_await client_->debot_ext_in().setFlexWalletCode(flex_wallet_code);
        co_await client_->debot_ext_in().setFlexWrapperCode(flex_wrapper_code);

        auto my_tip3 = ITONTokenWalletPtr(co_await cout().inputAddress("Token wallet address:", "TIP3WALLET"));
        auto tip3info = co_await my_tip3.run().getDetails();
        co_await cout().print(tip3info.name);

        Tip3Config tip3cfg {
          tip3info.name, tip3info.symbol, tip3info.decimals,
          tip3info.root_public_key, tip3info.root_address
        };

        auto wrapper_pubkey = co_await cout().inputUint256("Wrapper pubkey:");
        uint128 wrapper_deploy_value{3 * one_full_ton_size / 2};
        uint128 wrapper_keep_balance{one_full_ton_size};
        uint128 ext_wallet_balance{one_full_ton_size};
        uint128 set_internal_wallet_value{one_full_ton_size / 2};
        // auto wrapper_addr = co_await client_->debot_ext_in().deployWrapperWithWallet(
        //   wrapper_pubkey, wrapper_deploy_value, wrapper_keep_balance, ext_wallet_balance,
        //   set_internal_wallet_value, tip3cfg);
        // co_await printf("Wrapper deployed = {address}", wrapper_addr);
        break;
      }
      case 7: {
        co_await cout().print("Burning internal wallet...");

        auto my_tip3 = ITONTokenWalletPtr(co_await cout().inputAddress("Token wallet address:", "TIP3WALLET"));
        auto tip3info = co_await my_tip3.run().getDetails();
        co_await cout().print(tip3info.name);

        auto out_pubkey = co_await cout().inputUint256("Out pubkey:");
        auto out_internal_owner = co_await cout().inputAddress("Out internal owner:", "");

        co_await client_->debot_ext_in().burnWallet(
          uint128{one_full_ton_size}, out_pubkey, out_internal_owner, my_tip3.get()
          );
        break;
      }
      case 8:
        co_await cout().print("You choose to exit, bye");
        co_return;
      }
    } while(true);
  }
  DEFAULT_SUPPORT_FUNCTIONS(IFlexDebot, void)

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }
};

DEFINE_JSON_ABI(IFlexDebot, DFlexDebot, EFlexDebot);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(FlexDebot, IFlexDebot, DFlexDebot)

