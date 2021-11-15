/** \file
 *  \brief Trading pair (tip3/crystals) contract interfaces and data-structs.
 *  TradingPair - contract defining tip3/crystals trading pair. May only be deployed by Flex root contract.
 *  \author Andrew Zhogin
 *  \copyright 2019-2021 (c) TON LABS
 */

#pragma once

#include <tvm/schema/message.hpp>

#include <tvm/replay_attack_protection/timestamp.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>

namespace tvm {

/** \interface ITradingPair
 *  \brief TradingPair contract interface.
 */
__interface ITradingPair {

  /// Initialization method, may only be called by Flex root.
  [[internal, noaccept, answer_id, deploy]]
  bool_t onDeploy(
    uint128 min_amount,   ///< Minimum amount of major tokens for a deal or an order
    uint128 deploy_value, ///< Crystals to be kept in the contract
    address notify_addr   ///< Notification address (AMM)
  ) = 10;

  // ========== getters ==========
  /// Get address of Flex root
  [[getter]]
  address getFlexAddr() = 11;

  /// Get address of tip3 token root
  [[getter]]
  address getTip3Root() = 12;

  /// Get minimum amount of tokens for a deal or an order
  [[getter]]
  uint128 getMinAmount() = 13;

  /// Get notification address (AMM)
  [[getter]]
  address getNotifyAddr() = 14;
};
using ITradingPairPtr = handle<ITradingPair>;

/// TradingPair persistent data struct
struct DTradingPair {
  address flex_addr_;   ///< Flex root address
  address tip3_root_;   ///< Address of RootTokenContract for tip3 token
  uint128 min_amount_;  ///< Minimum amount of major tokens for a deal or an order
  address notify_addr_; ///< Notification address (AMM)
};

/// \interface ETradingPair
/// \brief TradingPair events interface
__interface ETradingPair {
};

/// Prepare Trading Pair StateInit structure and expected contract address (hash from StateInit)
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

} // namespace tvm

