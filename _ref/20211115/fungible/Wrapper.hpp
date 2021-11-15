/** \file
 *  \brief Wrapper contract interfaces and data-structs.
 *  Wrapper contract performes conversion of external tip3 wallet tokens into flex tip3 wallet tokens.
 *  Flex tip3 wallet supports only internal ownership (by some contract),
 *   and supports lend ownership to temporary grant ownership of tokens to Price / PriceXchg contracts for trading.
 *  Macroses TIP3_WRAPPER_WALLET_CODE_HASH / TIP3_WRAPPER_WALLET_CODE_DEPTH
 *   must be defined in compilation (code hash and code depth of FlexWallet).
 *  Use tonos-cli to get those values :
 *      tonos-cli decode stateinit --tvc FlexWallet.tvc
 *  ...
 *  "code_hash": "daf8d5fab85a9698fc9546e1beefbe0f1373f24d7980294bf26c0d5793cf1338",
 *  "data_hash": "55a703465a160dce20481375de2e5b830c841c2787303835eb5821d62d65ca9d",
 *  "code_depth": "20",
 *  "data_depth": "1",
 *  ...
 *  \author Andrew Zhogin
 *  \copyright 2019-2021 (c) TON LABS
 */

#pragma once

#include "TONTokenWallet.hpp"

namespace tvm {

static constexpr unsigned WRAPPER_TIMESTAMP_DELAY = 1800;
using wrapper_replay_protection_t = replay_attack_protection::timestamp<WRAPPER_TIMESTAMP_DELAY>;

/// Wrapper onTip3Transfer answer
struct WrapperRet {
  uint32  err_code;    ///< Error code (0 if success).
  address flex_wallet; ///< Deployed flex wallet.
};

/// Arguments to deploy wallet. Should be attached as a payload cell in transfer notification.
struct FlexDeployWalletArgs {
  uint256     pubkey;   ///< New wallet's public key.
  address_opt owner;    ///< New wallet's internal owner address.
  uint128     crystals; ///< Crystals to be sent to the deployable wallet.
};

/// Wrapper details info (for getter).
struct wrapper_details_info {
  string   name;            ///< Token name.
  string   symbol;          ///< Token short symbol.
  uint8    decimals;        ///< Decimals for ui purposes. ex: balance 100 with decimals 2 will be printed as 1.00.
  uint256  root_pubkey;     ///< Public key of the related RootTokenContract.
  address  root_owner;      ///< Internal owner address (or 0:00..0 if not set).
  uint128  total_granted;   ///< Total allocated and granted tokens.
  cell     wallet_code;     ///< Flex wallet code.
  address  external_wallet; ///< External wallet address.
};

// ===== FLeX Wrapper Contract ===== //
/** \interface IWrapper
 *  \brief Wrapper contract interface.
 */
__interface IWrapper {

  /// Additional initialization on deploy.
  [[internal, external, answer_id, deploy]]
  bool_t init(address external_wallet) = 10;

  /// Set internal wallet code. Can't be overrided after initialization.
  [[internal, external, noaccept, answer_id]]
  bool_t setInternalWalletCode(cell wallet_code) = 11;

  /// Deploy empty wallet.
  [[internal, noaccept, answer_id]]
  address deployEmptyWallet(
    uint256     pubkey,  ///< New wallet's public key.
    address_opt owner,   ///< New wallet's internal owner address.
    uint128     crystals ///< Crystals to be sent to the deployable wallet.
  ) = 12;

  /// \brief Implements ITONTokenWalletNotify::onTip3Transfer().
  /// Notification about incoming tokens from Wrapper owned external wallet.
  [[internal, noaccept, answer_id]]
  WrapperRet onTip3Transfer(
    uint128     balance,       ///< New balance of the wallet.
    uint128     new_tokens,    ///< Amount of tokens received in transfer.
    uint256     sender_pubkey, ///< Sender wallet pubkey.
    address_opt sender_owner,  ///< Sender wallet internal owner.
    cell        payload,       ///< Payload. Must be FlexDeployWalletArgs.
    address     answer_addr    ///< Answer address (to receive answer and the remaining processing crystals).
  ) = 202;

  /// \brief Burn internal tokens.
  /** Flex wallet will call this method when self destruct and wants to convert internal tokens to external.
      Wrapper will check that sender is a correct flex wallet
       and will transfer the same amount of tokens from its wallet to (out_pubkey, out_owner) tip3 wallet **/
  [[internal, noaccept]]
  void burn(
    uint128     tokens,        ///< Amount of tokens (balance of flex wallet on burn).
    address     answer_addr,   ///< Answer address.
    uint256     sender_pubkey, ///< Sender wallet pubkey.
    address_opt sender_owner,  ///< Sender wallet internal owner.
    uint256     out_pubkey,    ///< Pubkey of external (wrapped) tip3 wallet.
                               ///< Where to return external tip3 tokens.
    address_opt out_owner      ///< Internal owner (contract) of external (wrapped) tip3 wallet.
                               ///< Where to return external tip3 tokens.
  ) = 13;

  /// Request total granted tokens.
  [[internal, noaccept, answer_id]]
  uint128 requestTotalGranted() = 14;

  /// Get info about contract state details.
  [[getter]]
  wrapper_details_info getDetails() = 15;

  /// If internal wallet code was set up
  [[getter]]
  bool_t hasInternalWalletCode() = 16;

  /// Calculate flex tip3 wallet address
  [[getter, dyn_chain_parse]]
  address getWalletAddress(
    uint256     pubkey, ///< Public key of the wallet.
    address_opt owner   ///< Internal owner address of the wallet.
  ) = 17;
};
using IWrapperPtr = handle<IWrapper>;

/// Wrapper persistent data struct
struct DWrapper {
  string      name_;                 ///< Token name.
  string      symbol_;               ///< Token short symbol.
  uint8       decimals_;             ///< Decimals for ui purposes. ex: balance 100 with decimals 2 will be printed as 1.00.
  int8        workchain_id_;         ///< Workchain id.
  uint256     root_pubkey_;          ///< Public key of the Wrapper.
  address_opt root_owner_;           ///< Owner contract address (for internal ownership).
  uint128     total_granted_;        ///< Total allocated and granted tokens.
  optcell     internal_wallet_code_; ///< Internal (Flex) wallet code.
  Crystals    start_balance_;        ///< Start balance of Wrapper (to keep on deploy).
  opt<ITONTokenWalletPtr> wallet_;   ///< External (wrapped) tip3 wallet, owned by the Wrapper.
};

/// \interface EWrapper
/// \brief Wrapper events interface
struct EWrapper {
};

/// Prepare Wrapper StateInit structure and expected contract address (hash from StateInit)
inline
std::pair<StateInit, uint256> prepare_wrapper_state_init_and_addr(cell wrapper_code, DWrapper wrapper_data) {
  cell wrapper_data_cl =
    prepare_persistent_data<IWrapper, wrapper_replay_protection_t, DWrapper>(
      wrapper_replay_protection_t::init(), wrapper_data);
  StateInit wrapper_init {
    /*split_depth*/{}, /*special*/{},
    wrapper_code, wrapper_data_cl, /*library*/{}
  };
  cell wrapper_init_cl = build(wrapper_init).make_cell();
  return { wrapper_init, uint256(tvm_hash(wrapper_init_cl)) };
}

} // namespace tvm

