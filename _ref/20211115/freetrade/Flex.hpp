#pragma once

/** \file
 *  \brief Flex root contract interfaces and data-structs.
 *  \author Andrew Zhogin
 *  \copyright 2019-2021 (c) TON LABS
 */

#include <tvm/schema/message.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/replay_attack_protection/timestamp.hpp>
#include "PriceCommon.hpp"

namespace tvm {

static constexpr unsigned FLEX_TIMESTAMP_DELAY = 1800;
using flex_replay_protection_t = replay_attack_protection::timestamp<FLEX_TIMESTAMP_DELAY>;

/// Processing native funds value ...
struct TonsConfig {
  /// ... for executing tip3 transfer
  uint128 transfer_tip3;
  /// ... to return tip3 ownership
  uint128 return_ownership;
  /// ... to deploy tip3 trading pair
  uint128 trading_pair_deploy;
  /// .. to send answer message from Price
  uint128 order_answer;
  /// \brief ... to process processQueue function.
  /// Also is used for buyTip3 / onTip3LendOwnership / cancelSell / cancelBuy estimations.
  uint128 process_queue;
  /// ... to send notification about completed deal (IFlexNotify)
  uint128 send_notify;
};

/// Native funds (crystals) configuration for listing procedures
struct ListingConfig {
  /// Funds requirement (from client) to deploy wrapper
  uint128 register_wrapper_cost;
  /// \brief Funds to be taken in case of rejected wrapper.
  /// Rest will be returned to client.
  uint128 reject_wrapper_cost;
  /// Funds to send in wrapper deploy message
  uint128 wrapper_deploy_value;
  /// Wrapper will try to keep this balance (should be less then wrapper_deploy_value)
  uint128 wrapper_keep_balance;
  /// Funds to send in external wallet deploy message
  uint128 ext_wallet_balance;
  /// Funds to send with IWrapper::setInternalWalletCode message
  uint128 set_internal_wallet_value;
  /// Funds requirement (from client) to deploy xchg/trading pair
  uint128 register_pair_cost;
  /// \brief Funds to be taken in case of rejected xchg/trading pair.
  /// Rest will be returned to client.
  uint128 reject_pair_cost;
  /// Funds to send in pair deploy message
  uint128 pair_deploy_value;
  /// Pair will try to keep this balance
  uint128 pair_keep_balance;
  /// Value for answer
  uint128 register_return_value;
};

/** \interface IListingAnswer
 *  \brief Answers to client about approved/rejected listings.
 */
__interface IListingAnswer {
  /// Wrapper has been approved
  [[internal, noaccept]]
  void onWrapperApproved(uint256 pubkey, address contract) = 500;
  /// Wrapper has been rejected
  [[internal, noaccept]]
  void onWrapperRejected(uint256 pubkey) = 501;
  /// Trading pair has been approved
  [[internal, noaccept]]
  void onTradingPairApproved(uint256 pubkey, address contract) = 502;
  /// Trading pair has been rejected
  [[internal, noaccept]]
  void onTradingPairRejected(uint256 pubkey) = 503;
  /// Exchange pair has been approved
  [[internal, noaccept]]
  void onXchgPairApproved(uint256 pubkey, address contract) = 504;
  /// Exchange pair has been rejected
  [[internal, noaccept]]
  void onXchgPairRejected(uint256 pubkey) = 505;
};
using IListingAnswerPtr = handle<IListingAnswer>;

/** \interface IFlexNotify
 *  \brief Notifications to AMM about orders.
 */
// TODO: Add expired/out-of-crystals orders notifications (?)
__interface IFlexNotify {
  /// Notification about completed trading deal tip3/crystal
  [[internal, noaccept]]
  void onDealCompleted(
    address tip3root, ///< Address of RootTokenContract for the tip3 token
    uint128 price,    ///< Token price (amount of native nano-crystals for one atomic tip3 token)
    uint128 amount    ///< Amount of tip3 tokens
  ) = 10;
  /// Notification about completed exchange deal tip3/tip3
  [[internal, noaccept]]
  void onXchgDealCompleted(
    address tip3root_sell, ///< Address of RootTokenContract for the seller tip3 token (major token)
    address tip3root_buy,  ///< Address of RootTokenContract for the buyer tip3 token (minor token)
    uint128 price_num,     ///< Token price numerator
    uint128 price_denum,   ///< Token price denominator
    uint128 amount         ///< Amount of major tip3 tokens in the deal
  ) = 11;
  /// Notification about added trading order (tip3/crystals)
  [[internal, noaccept]]
  void onOrderAdded(
    bool_t  sell,      ///< Is it a sell order
    address tip3root,  ///< Address of RootTokenContract for the tip3 token
    uint128 price,     ///< Token price (amount of native nano-crystals for one atomic tip3 token)
    uint128 amount,    ///< Amount of tip3 tokens added in the order
    uint128 sum_amount ///< Summarized amount of tokens rest in all orders for this price (sell or buy only)
  ) = 12;
  /// Notification about canceled trading order (tip3/crystals)
  [[internal, noaccept]]
  void onOrderCanceled(
    bool_t  sell,      ///< Is it a sell order
    address tip3root,  ///< Address of RootTokenContract for the tip3 token
    uint128 price,     ///< Token price (amount of native nano-crystals for one atomic tip3 token)
    uint128 amount,    ///< Amount of tip3 tokens canceled
    uint128 sum_amount ///< Summarized amount of tokens rest in all orders for this price (sell or buy only)
  ) = 13;
  /// Notification about added exchange order (tip3/tip3)
  [[internal, noaccept]]
  void onXchgOrderAdded(
    bool_t  sell,           ///< Is it a sell order
    address tip3root_major, ///< Address of RootTokenContract for the major tip3 token
    address tip3root_minor, ///< Address of RootTokenContract for the minor tip3 token
    uint128 price_num,      ///< Token price numerator
    uint128 price_denum,    ///< Token price denominator
    uint128 amount,         ///< Amount of major tip3 tokens added in the order
    uint128 sum_amount      ///< Summarized amount of major tokens rest in all orders for this price (sell or buy only)
  ) = 14;
  /// Notification about canceled exchange order (tip3/tip3)
  [[internal, noaccept]]
  void onXchgOrderCanceled(
    bool_t sell,            ///< Is it a sell order
    address tip3root_major, ///< Address of RootTokenContract for the major tip3 token
    address tip3root_minor, ///< Address of RootTokenContract for the minor tip3 token
    uint128 price_num,      ///< Token price numerator
    uint128 price_denum,    ///< Token price denominator
    uint128 amount,         ///< Amount of major tip3 tokens canceled
    uint128 sum_amount      ///< Summarized amount of major tokens rest in all orders for this price (sell or buy only)
  ) = 15;
};
using IFlexNotifyPtr = handle<IFlexNotify>;

/// Request to deploy wrapper
struct WrapperListingRequest {
  /// Client address to send notification with the remaining funds
  address client_addr;
  /// Native funds, sent by client
  uint128 client_funds;
  /// Configuration of external tip3 wallet
  Tip3Config tip3cfg;
};

/// Request to deploy wrapper with public key (for getter)
struct WrapperListingRequestWithPubkey {
  uint256 wrapper_pubkey;        ///< Wrapper's public key
  WrapperListingRequest request; ///< Request's details
};

/// Request to deploy trading pair (tip3/crystals)
struct TradingPairListingRequest {
  address client_addr;  ///< Client address to send notification with the remaining funds
  uint128 client_funds; ///< Native funds, sent by client
  address tip3_root;    ///< Address of RootTokenContract for the tip3 token
  uint128 min_amount;   ///< Minimum amount of tokens for a deal or an order
  address notify_addr;  ///< Notification address (AMM)
};

/// Request to deploy trading pair (tip3/crystals) with public key (for getter)
struct TradingPairListingRequestWithPubkey {
  uint256 pubkey;                    ///< Request's public key
  TradingPairListingRequest request; ///< Request's details
};

/// Request to deploy exchange pair (tip3/tip3)
struct XchgPairListingRequest {
  address client_addr;     ///< Client address to send notification with the remaining funds
  uint128 client_funds;    ///< Native funds, sent by client
  address tip3_major_root; ///< Address of RootTokenContract for the major tip3 token
  address tip3_minor_root; ///< Address of RootTokenContract for the minor tip3 token
  uint128 min_amount;      ///< Minimum amount of major tokens for a deal or an order
  address notify_addr;     ///< Notification address (AMM)
};

/// Request to deploy exchange pair (tip3/tip3) with public key (for getter)
struct XchgPairListingRequestWithPubkey {
  uint256 pubkey;                 ///< Request's public key
  XchgPairListingRequest request; ///< Request's details
};

/// Ownership info for Flex root
struct FlexOwnershipInfo {
  uint256 deployer_pubkey;              ///< Deployer's public key
  string ownership_description;         ///< Ownership description
  address_opt owner; ///< If Flex is managed by other contract (deployer will not be able to execute non-deploy methods)
};

/// Flex root details (for getter)
struct FlexDetails {
  bool_t initialized;          ///< Is Flex completely initialized
  TonsConfig tons_cfg;         ///< Native funds (processing costs) configuration
  ListingConfig listing_cfg;   ///< Listing processing costs configuration
  cell trading_pair_code;      ///< Trading pair code (TradingPair)
  cell xchg_pair_code;         ///< Exchange pair code (XchgPair)
  uint8 deals_limit;           ///< Deals limit to be processed in one transaction
  FlexOwnershipInfo ownership; ///< Ownership info
  dict_array<WrapperListingRequestWithPubkey> wrapper_listing_requests; ///< Wrapper listing requests
  dict_array<TradingPairListingRequestWithPubkey> trading_pair_listing_requests; ///< Trading pair listing requests
  dict_array<XchgPairListingRequestWithPubkey> xchg_pair_listing_requests; ///< Exchange pair listing requests
};

/// Enumeration of code types for Flex initialization
enum class code_type {
  trade_pair_code = 1, ///< Code of trading pair (tip3/crystals)
  xchg_pair_code,      ///< Code of exchange pair (tip3/tip3)
  wrapper_code,        ///< Code of Wrapper
  ext_wallet_code,     ///< Code of external wallet
  flex_wallet_code,    ///< Code of flex wallet
  price_code,          ///< Code of Price contract (tip3/crystals)
  xchg_price_code      ///< Code of PriceXchg contract (tip3/tip3)
};

/** \interface IFlex
 *  \brief Flex root contract interface.
 *  Flex is a root contract for exchange system.
 */
__interface IFlex {

  /// Constructor of Flex
  [[external]]
  void constructor(
    uint256 deployer_pubkey,      ///< Deployer's public key.
                                  ///< If \p owner_address is not specified, will also be an owner.
    string ownership_description, ///< Ownership description
    address_opt owner_address,    ///< Owner contract address (optional)
    TonsConfig tons_cfg,          ///< Native funds (processing costs) configuration
    uint8 deals_limit,            ///< Deals limit for one transaction
    ListingConfig listing_cfg     ///< Listing configuration (listing processing costs)
  ) = 10;

  /// To fit message size limit, we need to set specific code in separate function (not in constructor).
  /// To set pairs, wrapper, wallets, prices contract codes.
  /// /p `type` should be code_type enum.
  [[external, noaccept]]
  void setSpecificCode(uint8 type, cell code) = 11;

  /// Transfer of native funds to destination contract
  [[external, internal, noaccept]]
  void transfer(address to, uint128 crystals) = 12;

  // Listing procedures
  /// Request to register tip3/crystals trading pair (returns pre-calculated address of future trading pair)
  [[internal, noaccept, answer_id]]
  address registerTradingPair(
    uint256 pubkey,     ///< Public key of the request (just for id)
    address tip3_root,  ///< Address of RootTokenContract for the tip3 token
    uint128 min_amount, ///< Minimum amount of tokens for a deal or an order
    address notify_addr ///< Notification address (AMM)
    ) = 13;
  /// Request to register tip3/tip3 xchg pair (returns pre-calculated address of future xchg pair)
  [[internal, noaccept, answer_id]]
  address registerXchgPair(
    uint256 pubkey,          ///< Public key of the request (just for id)
    address tip3_major_root, ///< Address of RootTokenContract for the major tip3 token
    address tip3_minor_root, ///< Address of RootTokenContract for the minor tip3 token
    uint128 min_amount,      ///< Minimum amount of major tokens for a deal or an order
    address notify_addr      ///< Notification address (AMM)
    ) = 14;
  /// Request to register wrapper (returns pre-calculated address of future wrapper)
  [[internal, noaccept, answer_id]]
  address registerWrapper(
    uint256 pubkey,    ///< Wrapper's pubkey
    Tip3Config tip3cfg ///< Configuration of external tip3 wallet
    ) = 15;

  /// Approve tip3/crystals trading pair
  [[external, internal, noaccept, answer_id]]
  address approveTradingPair(
    uint256 pubkey
    ) = 16;
  /// Reject tip3/crystals trading pair
  [[external, internal, noaccept]]
  bool_t rejectTradingPair(
    uint256 pubkey
    ) = 17;
  /// Approve tip3/tip3 exchange pair
  [[external, internal, noaccept, answer_id]]
  address approveXchgPair(
    uint256 pubkey
    ) = 18;
  /// Reject tip3/tip3 exchange pair
  [[external, internal, noaccept]]
  bool_t rejectXchgPair(
    uint256 pubkey
    ) = 19;
  /// Approve wrapper
  [[external, internal, noaccept, answer_id]]
  address approveWrapper(
    uint256 pubkey
    ) = 20;
  /// Reject wrapper
  [[external, internal, noaccept]]
  bool_t rejectWrapper(
    uint256 pubkey
    ) = 21;
  // ========== getters ==========

  /// Is Flex completely initialized.
  /// Means setSpecificCode for all code types executed.
  [[getter]]
  bool_t isFullyInitialized() = 22;

  /// Get contract state details.
  [[getter]]
  FlexDetails getDetails() = 23;

  /// Get Price contract code with salt added (Flex address and tip3 root address).
  [[getter]]
  cell getSellPriceCode(address tip3_addr) = 24;

  /// Get PriceXchg contract code with salt added (Flex address and tip3 root addresses).
  [[getter]]
  cell getXchgPriceCode(address tip3_addr1, address tip3_addr2) = 25;

  /// Get address of tip3/crystals trading pair
  [[getter]]
  address getSellTradingPair(address tip3_root) = 26;

  /// Get address of tip3/tip3 exchange pair
  [[getter]]
  address getXchgTradingPair(address tip3_major_root, address tip3_minor_root) = 27;
};
using IFlexPtr = handle<IFlex>;

/// Flex persistent data struct
struct DFlex {
  uint256 deployer_pubkey_;      ///< Deployer's public key
  int8 workchain_id_;            ///< Workchain id
  string ownership_description_; ///< Ownership description
  address_opt owner_address_;    ///< Owner contract address (optional)
  TonsConfig tons_cfg_;          ///< Native funds (processing costs) configuration
  ListingConfig listing_cfg_;    ///< Listing processing costs configuration
  optcell pair_code_;            ///< TradingPair code (with salt added)
  optcell xchg_pair_code_;       ///< XchgPair code (with salt added)
  optcell price_code_;           ///< Price code
  optcell xchg_price_code_;      ///< PriceXchg code
  optcell ext_wallet_code_;      ///< External wallet code (TONTokenWallet.tvc)
  optcell flex_wallet_code_;     ///< Flex wallet code (FlexWallet.tvc)
  optcell wrapper_code_;         ///< Wrapper code
  uint8 deals_limit_;            ///< Deals limit for one transaction

  /// Map from wrapper pubkey into listing data
  using wrappers_map = dict_map<uint256, WrapperListingRequest>;
  wrappers_map wrapper_listing_requests_;
  /// Map from request pubkey into trading pair listing data
  using trading_pairs_map = dict_map<uint256, TradingPairListingRequest>;
  trading_pairs_map trading_pair_listing_requests_;
  /// Map from request pubkey into xchg pair listing data
  using xchg_pairs_map = dict_map<uint256, XchgPairListingRequest>;
  xchg_pairs_map xchg_pair_listing_requests_;
};

/// \interface EFlex
/// \brief Flex events interface
__interface EFlex {
};

/// Prepare Flex StateInit structure and expected contract address (hash from StateInit)
inline
std::pair<StateInit, uint256> prepare_flex_state_init_and_addr(DFlex flex_data, cell flex_code) {
  cell flex_data_cl =
    prepare_persistent_data<IFlex, flex_replay_protection_t, DFlex>(
      flex_replay_protection_t::init(), flex_data
    );
  StateInit flex_init {
    /*split_depth*/{}, /*special*/{},
    flex_code, flex_data_cl, /*library*/{}
  };
  cell flex_init_cl = build(flex_init).make_cell();
  return { flex_init, uint256(tvm_hash(flex_init_cl)) };
}

} // namespace tvm

