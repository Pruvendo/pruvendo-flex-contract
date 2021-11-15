#include "WrongListingMock.hpp"
#include "TradingPair.hpp"
#include "XchgPair.hpp"
#include "Wrapper.hpp"

#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/replay_attack_protection/timestamp.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;

static constexpr unsigned TIMESTAMP_DELAY = 1800;

class WrongListingMock final : public smart_interface<IWrongListingMock>, public DWrongListingMock {
  using replay_protection_t = replay_attack_protection::timestamp<TIMESTAMP_DELAY>;
public:
  struct error_code : tvm::error_code {
    static constexpr unsigned message_sender_is_not_my_owner = 100;
    static constexpr unsigned missed_ext_wallet_code         = 101;
    static constexpr unsigned missed_flex_wallet_code        = 102;
    static constexpr unsigned missed_flex_wrapper_code       = 103;
    static constexpr unsigned zero_owner_pubkey              = 104;
    static constexpr unsigned unexpected_refs_count_in_code  = 105;
  };

  __always_inline
  void constructor(uint256 pubkey, cell trading_pair_code, cell xchg_pair_code) {
    require(pubkey != 0, error_code::zero_owner_pubkey);
    owner_ = pubkey;
    flex_ = address::make_std(int8(0), uint256(0));

    require(trading_pair_code.ctos().srefs() == 2, error_code::unexpected_refs_count_in_code);
    trading_pair_code_ = builder().stslice(trading_pair_code.ctos()).stref(build(flex_).endc()).endc();
    require(xchg_pair_code.ctos().srefs() == 2, error_code::unexpected_refs_count_in_code);
    xchg_pair_code_ = xchg_pair_code;

    workchain_id_ = std::get<addr_std>(address{tvm_myaddr()}.val()).workchain_id;
  }

  // === additional configuration necessary for deploy wrapper === //

  __always_inline
  void setFlexWrapperCode(cell code) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    require(code.ctos().srefs() == 2, error_code::unexpected_refs_count_in_code);
    flex_wrapper_code_ = builder().stslice(code.ctos()).stref(build(flex_).endc()).endc();
  }

  // === ===================================================== === //
  __always_inline
  address deployWrapper(
    uint256 wrapper_pubkey,
    uint128 wrapper_deploy_value,
    uint128 wrapper_keep_balance,
    Tip3Config tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wrapper_code_, error_code::missed_flex_wrapper_code);
    tvm_accept();

    DWrapper wrapper_data {
      .name_ = tip3cfg.name,
      .symbol_ = tip3cfg.symbol,
      .decimals_ = tip3cfg.decimals,
      .workchain_id_ = workchain_id_,
      .root_pubkey_ = wrapper_pubkey,
      .root_owner_ = address{tvm_myaddr()},
      .total_granted_ = {},
      .internal_wallet_code_ = {},
      .start_balance_ = Grams(wrapper_keep_balance.get()),
      .wallet_ = {}
    };
    auto [wrapper_init, wrapper_hash_addr] = prepare_wrapper_state_init_and_addr(flex_wrapper_code_.get(), wrapper_data);
    IWrapperPtr wrapper_addr(address::make_std(workchain_id_, wrapper_hash_addr));

    // ================== Deploying Flex wrapper for Nuka ================== //
    wrapper_addr.deploy(wrapper_init, Grams(wrapper_deploy_value.get())).init(flex_);

    return wrapper_addr.get();
  }
  
    __always_inline
  address deployWrapperWithWrongCall(
    uint256 wrapper_pubkey,
    uint128 wrapper_deploy_value,
    uint128 wrapper_keep_balance,
    Tip3Config tip3cfg
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wrapper_code_, error_code::missed_flex_wrapper_code);
    tvm_accept();

    DWrapper wrapper_data {
      .name_ = tip3cfg.name,
      .symbol_ = tip3cfg.symbol,
      .decimals_ = tip3cfg.decimals,
      .workchain_id_ = workchain_id_,
      .root_pubkey_ = wrapper_pubkey,
      .root_owner_ = address{tvm_myaddr()},
      .total_granted_ = {},
      .internal_wallet_code_ = {},
      .start_balance_ = Grams(wrapper_keep_balance.get()),
      .wallet_ = {}
    };
    auto [wrapper_init, wrapper_hash_addr] = prepare_wrapper_state_init_and_addr(flex_wrapper_code_.get(), wrapper_data);
    IWrapperPtr wrapper_addr(address::make_std(workchain_id_, wrapper_hash_addr));

    // ================== Deploying Flex wrapper for Nuka ================== //
    wrapper_addr.deploy(wrapper_init, Grams(wrapper_deploy_value.get())).setInternalWalletCode(flex_wrapper_code_.get());

    return wrapper_addr.get();
  }

  __always_inline
  address deployTradingPair(
    address tip3_root,
    uint128 deploy_min_value,
    uint128 deploy_value,
    uint128 min_trade_amount,
    address notify_addr
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    DTradingPair pair_data {
      .flex_addr_ = flex_,
      .tip3_root_ = tip3_root,
      .notify_addr_ = address::make_std(int8(0), uint256(0))
    };

    auto [state_init, std_addr] = prepare_trading_pair_state_init_and_addr(pair_data, trading_pair_code_);
    auto trade_pair = ITradingPairPtr(address::make_std(workchain_id_, std_addr));
    trade_pair.deploy(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS, false).
      onDeploy(min_trade_amount, deploy_min_value, notify_addr);

    return trade_pair.get();
  }

  __always_inline
  address deployTradingPairWithWrongCall(
    address tip3_root,
    uint128 deploy_value
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    DTradingPair pair_data {
      .flex_addr_ = flex_,
      .tip3_root_ = tip3_root,
      .notify_addr_ = address::make_std(int8(0), uint256(0))
    };

    auto [state_init, std_addr] = prepare_trading_pair_state_init_and_addr(pair_data, trading_pair_code_);
    auto trade_pair = ITradingPairPtr(address::make_std(workchain_id_, std_addr));
    trade_pair.deploy_noop(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS);

    return trade_pair.get();
  }

  __always_inline
  address deployXchgPair(
    address tip3_major_root,
    address tip3_minor_root,
    uint128 deploy_min_value,
    uint128 deploy_value,
    uint128 min_trade_amount,
    address notify_addr
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    DXchgPair pair_data {
      .flex_addr_ = flex_,
      .tip3_major_root_ = tip3_major_root,
      .tip3_minor_root_ = tip3_minor_root,
      .notify_addr_ = address::make_std(int8(0), uint256(0))
    };

    auto [state_init, std_addr] = prepare_xchg_pair_state_init_and_addr(pair_data, xchg_pair_code_);
    auto trade_pair = IXchgPairPtr(address::make_std(workchain_id_, std_addr));
    trade_pair.deploy(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS, false).
      onDeploy(min_trade_amount, deploy_min_value, notify_addr);

    return trade_pair.get();
  }

  __always_inline
  address deployXchgPairWithWrongCall(
    address tip3_major_root,
    address tip3_minor_root,
    uint128 deploy_value
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    DXchgPair pair_data {
      .flex_addr_ = flex_,
      .tip3_major_root_ = tip3_major_root,
      .tip3_minor_root_ = tip3_minor_root,
      .notify_addr_ = address::make_std(int8(0), uint256(0))
    };

    auto [state_init, std_addr] = prepare_xchg_pair_state_init_and_addr(pair_data, xchg_pair_code_);
    auto trade_pair = IXchgPairPtr(address::make_std(workchain_id_, std_addr));
    trade_pair.deploy_noop(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS);

    return trade_pair.get();
  }

  __always_inline
  uint256 getOwner() {
    return owner_;
  }

  __always_inline
  bool_t hasFlexWrapperCode() {
    return bool_t{!!flex_wrapper_code_};
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IWrongListingMock, replay_protection_t)

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }

private:
};

DEFINE_JSON_ABI(IWrongListingMock, DWrongListingMock, EWrongListingMock);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS(WrongListingMock, IWrongListingMock, DWrongListingMock, TIMESTAMP_DELAY)


