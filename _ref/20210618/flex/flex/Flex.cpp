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

