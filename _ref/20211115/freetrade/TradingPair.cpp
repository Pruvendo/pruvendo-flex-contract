/** \file
 *  \brief Trading pair contract implementation
 *  \author Andrew Zhogin
 *  \copyright 2019-2021 (c) TON LABS
 */

#include "TradingPair.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;

/// Implements tvm::ITradingPair interface
class TradingPair final : public smart_interface<ITradingPair>, public DTradingPair {
public:
  static constexpr bool _checked_deploy = true; /// To allow deploy message only with `onDeploy` call
  struct error_code : tvm::error_code {
    static constexpr unsigned not_enough_crystals           = 101; ///< Not enough crystals to process
    static constexpr unsigned double_deploy                 = 102; ///< Double call of `onDeploy` method
    static constexpr unsigned zero_min_amount               = 103; ///< Zero minimum amount
    static constexpr unsigned bad_incoming_msg              = 104; ///< Bad incoming message
    static constexpr unsigned unexpected_refs_count_in_code = 105; ///< Unexpected references count in code
    static constexpr unsigned only_flex_may_deploy_me       = 106; ///< Only Flex may deploy this contract
  };

  __always_inline
  StateInit getStateInit(const message<anyval> &msg) {
    if (msg.init->isa<ref<StateInit>>()) {
      return msg.init->get<ref<StateInit>>()();
    } else {
      return msg.init->get<StateInit>();
    }
  }

  __always_inline
  bool_t onDeploy(uint128 min_amount, uint128 deploy_value, address notify_addr) {
    require(int_value().get() > deploy_value, error_code::not_enough_crystals);
    require(!min_amount_, error_code::double_deploy);
    require(min_amount > 0, error_code::zero_min_amount);

    auto parsed_msg = parse<message<anyval>>(parser(msg_slice()), error_code::bad_incoming_msg);
    require(!!parsed_msg.init, error_code::bad_incoming_msg);
    auto init = getStateInit(parsed_msg);
    require(!!init.code, error_code::bad_incoming_msg);
    auto mycode = *init.code;
    require(mycode.ctos().srefs() == 3, error_code::unexpected_refs_count_in_code);
    parser mycode_parser(mycode.ctos());
    mycode_parser.ldref();
    mycode_parser.ldref();
    auto mycode_salt = mycode_parser.ldrefrtos();
    auto flex_addr = parse<address>(mycode_salt);
    require(flex_addr == int_sender(), error_code::only_flex_may_deploy_me);

    min_amount_ = min_amount;
    notify_addr_ = notify_addr;
    tvm_rawreserve(deploy_value.get(), rawreserve_flag::up_to);
    set_int_return_flag(SEND_ALL_GAS);
    return bool_t{true};
  }

  __always_inline
  address getFlexAddr() {
    return flex_addr_;
  }

  __always_inline
  address getTip3Root() {
    return tip3_root_;
  }

  __always_inline
  uint128 getMinAmount() {
    return min_amount_;
  }

  __always_inline
  address getNotifyAddr() {
    return notify_addr_;
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

