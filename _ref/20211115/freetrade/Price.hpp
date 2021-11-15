/** \file
 *  \brief Price contract interfaces and data-structs
 *  Price - contract to enqueue and process tip3-crystals exchange orders at a specific price
 *  \author Andrew Zhogin
 *  \copyright 2019-2021 (c) TON LABS
 */

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
#include "FlexWallet.hpp"

namespace tvm {

using ITONTokenWalletPtr = handle<ITONTokenWallet>;

/// Sell order arguments in payload
struct SellArgs {
  uint128 amount;         ///< Amount of tip3 tokens to sell
  address receive_wallet; ///< Contract to receive native crystals
};

/// Tip3/crystals exchange order info
struct OrderInfo {
  uint128 original_amount;    ///< Original amount of tip3 tokens in order.
  uint128 amount;             ///< Current remaining amount of tip3 tokens in order.
  uint128 account;            ///< Crystals from client to pay for processing.
  addr_std_fixed tip3_wallet; ///< Tip3 token wallet.
  addr_std_fixed client_addr; ///< \brief Client contract address. Price will execute cancels from this address,
                              ///<  send notifications and return the remaining native funds (crystals) to this address.
  uint32 order_finish_time;   ///< Order finish time.
};
using OrderInfoWithIdx = std::pair<unsigned, OrderInfo>;

// usage from debot:
// co_await tip3.tail_call<OrderRet>(price_addr, cr).lendOwnership(...)

/** \interface IPrice
 *  \brief Price contract interface.
 *
 *  Price - contract to enqueue and process tip3/crystals exchange orders at a specific price.
 */
__interface IPrice {

  /// \brief Implementation of ITONTokenWalletNotify::onTip3LendOwnership().
  /** Tip3 wallet notifies Price contract about lent token balance.
      To start a sell order. **/
  [[internal, noaccept, answer_id]]
  OrderRet onTip3LendOwnership(
    uint128     balance,          ///< Lend token balance (amount of tokens to participate in a deal)
    uint32      lend_finish_time, ///< Lend ownership finish time
    uint256     pubkey,           ///< Public key of the tip3 wallet
    address_opt owner,            ///< Internal owner address of the tip3 wallet
    cell        payload,          ///< Payload, must be SellArgs struct
    address     answer_addr       ///< Answer address
  ) = 201;

  /// Add an order to buy Tip3 tokens for crystals
  [[internal, noaccept, answer_id]]
  OrderRet buyTip3(
    uint128 amount,           ///< Amount of tokens to buy
    address receive_tip3,     ///< Contract to receive native crystals
    uint32  order_finish_time ///< Order finish time
  ) = 202;

  /// \brief Process enqueued orders.
  /** This function is called from the Price itself when onTip3LendOwnership processing hits deals limit.
      Or when processQueue processing hits deals limit also. **/
  [[internal, noaccept]]
  void processQueue() = 203;

  /// Will cancel all orders with this sender's client_addr
  [[internal, noaccept]]
  void cancelSell() = 204;

  /// Will cancel all orders with this sender's client_addr
  [[internal, noaccept]]
  void cancelBuy() = 205;
};
using IPricePtr = handle<IPrice>;

/// Price persistent data struct
struct DPrice {
  uint128        price_;        /// Price of one atomic tip3 token in atomic (nano) crystals
  uint128        sells_amount_; ///< Common amount of tokens to sell.
                                ///< \warning May be not strictly actual because of possible expired orders in the queue.
  uint128        buys_amount_;  ///< Common amount of tokens to buy.
                                ///< \warning May be not strictly actual because of possible expired orders in the queue.
  addr_std_fixed flex_;         ///< Address of root flex contract (IFlex).
  uint128        min_amount_;   ///< Minimum amount of tokens, allowed to make a deal or an order.
  uint8          deals_limit_;  ///< Limit for processed deals in one request.
  IFlexNotifyPtr notify_addr_;  ///< Notification address for AMM (IFlexNotify).
  int8           workchain_id_; ///< Workchain id for the related tip3 token wallets.
  TonsConfig     tons_cfg_;     ///< Processing costs configuration of Flex in native funds (crystals).
  Tip3Config     tip3cfg_;      ///< Configuration of the tip3 token.
  queue<OrderInfo> sells_;      ///< Queue of sell orders.
  queue<OrderInfo> buys_;       ///< Queue of buy orders.
};

/// \interface EPrice
/// \brief Price events interface
__interface EPrice {
};

/// Prepare StateInit struct and std address to deploy Price contract
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

} // namespace tvm

