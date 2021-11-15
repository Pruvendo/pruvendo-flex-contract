#pragma once

#include <tvm/schema/message.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/replay_attack_protection/timestamp.hpp>

#include "PriceCommon.hpp"
<<<<<<< HEAD
#include "RootTokenContract.hpp"
#include "DePool.hpp"
=======
#include "DePool.hpp"
#include "TONTokenWallet.hpp"
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055

namespace tvm { inline namespace schema {

static constexpr unsigned STTONS_TIMESTAMP_DELAY = 1800;
using sttons_replay_protection_t = replay_attack_protection::timestamp<STTONS_TIMESTAMP_DELAY>;

<<<<<<< HEAD
struct stTONsCosts {
  uint128 receive_stake_transfer_costs; // full costs of receiveStakeTransfer processing
  uint128 store_crystals_costs; // costs of storeCrystalls processing
  uint128 mint_costs; // costs of `mint` call
  uint128 process_receive_stake_costs; // costs of receiveStakeTransfer function processing itself
  uint128 deploy_wallet_costs; // costs of deployWallet (without crystals stored in the wallet)
  uint128 min_transfer_tokens;
  uint128 transfer_stake_costs;
};

struct StoredCrystalsPair {
  uint256 std_addr;
  uint128 account;
};
=======
// lend structures are declared in TONTokenWallet.hpp
/*struct lend_record {
  uint128 lend_balance;
  uint32 lend_finish_time;
};
using lend_ownership_map = small_dict_map<addr_std_fixed, lend_record>;

struct lend_array_record {
  address lend_addr;
  uint128 lend_balance;
  uint32 lend_finish_time;
};
using lend_ownership_array = dict_array<lend_array_record>;*/

__interface IstTONsNotify {
  [[internal, noaccept, answer_id]]
  bool_t onLendOwnership(
    address answer_addr,
    uint128 balance,
    uint32  lend_finish_time,
    uint256 pubkey,
    std::optional<address> internal_owner,
    address depool,
    uint256 depool_pubkey,
    cell    payload
  ) = 201;
};
using IstTONsNotifyPtr = handle<IstTONsNotify>;
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055

struct stTONsDetails {
  uint256 owner_pubkey;
  std::optional<address> owner_address;
<<<<<<< HEAD
  address tip3root;
  address depool;
  dict_array<StoredCrystalsPair> accounts;
  stTONsCosts costs;
=======
  address depool;
  uint256 depool_pubkey;
  uint128 balance;
  lend_ownership_array lend_ownership;
  uint128 lend_balance; // sum lend balance to all targets
  bool_t transferring_stake_back;
  uint8 last_depool_error;
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
};

__interface IstTONs {

<<<<<<< HEAD
  [[external]]
  void constructor(
    uint256 owner_pubkey,
    Tip3Config tip3cfg,
    address depool,
    stTONsCosts costs,
    cell tip3code
  ) = 10;

  // store crystalls in account for sender (to be used in next receiveStakeTransfer call)
  [[internal, noaccept]]
  void storeCrystalls(address client_addr) = 11;
=======
  [[internal, noaccept]]
  void onDeploy() = 10;

  // lend ownership to some contract until 'lend_finish_time'
  [[external, internal, noaccept, answer_id]]
  void lendOwnership(
    address answer_addr,
    uint128 grams,
    address dest,
    uint128 lend_balance,
    uint32  lend_finish_time,
    cell    deploy_init_cl,
    cell    payload
  ) = 11;

  // return ownership back to the original owner (for provided amount of tokens)
  [[internal, noaccept]]
  void returnOwnership(uint128 tokens) = 12;

  // Return stake to the provided `dst`.
  // Only works when contract is not in "lend mode".
  // Will return all stake (calling `IDePool::transferStake(dst, 0_u64)`)
  // `processing_crystals` - value will be attached to the message
  [[external, internal, noaccept]]
  void returnStake(address dst, uint128 processing_crystals) = 13;

  // Eliminate contract and return all the remaining crystals to `dst`
  // `ignore_errors` - ignore error returned by depool for transferStake
  // finalize will not work if contract is not in "lend mode"
  // or last_depool_error_ != 0 && !ignore_errors
  // WARNING: do not use `ignore_errors=true`, until you are really sure that
  //   your stake in depool is empty or insignificant
  // STATUS_DEPOOL_CLOSED / STATUS_NO_PARTICIPANT are not considered as an errors forbidding `finalize`
  [[external, internal, noaccept]]
  void finalize(address dst, bool_t ignore_errors) = 14;
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055

  // Receive stake transfer notify (from solidity IParticipant::onTransfer(address source, uint128 amount))
  [[internal, noaccept]]
  void receiveStakeTransfer(address source, uint128 amount) = 0x23c4771d; // = hash_v<"onTransfer(address,uint128)()v2">

<<<<<<< HEAD
  // Receive tokens from other wallet
  [[internal, noaccept, answer_id]]
  void internalTransfer(
    uint128 tokens,
    address answer_addr,
    uint256 sender_pubkey,
    address sender_owner,
    bool_t  notify_receiver,
    cell    payload
  ) = 16; // value must be the same as in TONTokenWallet::internalTransfer

  // ========== getters ==========
  [[getter]]
  stTONsDetails getDetails() = 17;
=======
  // If error occured while transferring stake back
  [[internal, noaccept]]
  void receiveAnswer(uint32 errcode, uint64 comment) = 0x3f109e44; // IParticipant::receiveAnswer

  // ========== getters ==========
  [[getter]]
  stTONsDetails getDetails() = 15;

  [[getter]]
  address calcStTONsAddr(
    cell code,
    uint256 owner_pubkey,
    std::optional<address> owner_address,
    address depool
  ) = 16;
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
};
using IstTONsPtr = handle<IstTONs>;

struct DstTONs {
  uint256 owner_pubkey_;
  std::optional<address> owner_address_;
<<<<<<< HEAD
  Tip3Config tip3cfg_;
  IDePoolPtr depool_;
  dict_map<uint256, uint128> stored_crystals_;
  stTONsCosts costs_;
  int8 workchain_id_;
  cell tip3code_;
=======
  IDePoolPtr depool_;
  uint256 depool_pubkey_;
  uint128 balance_;
  lend_ownership_map lend_ownership_;
  bool_t transferring_stake_back_;
  uint8 last_depool_error_;
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
};

__interface EstTONs {
};

// Prepare stTONs StateInit structure and expected contract address (hash from StateInit)
inline
std::pair<StateInit, uint256> prepare_sttons_state_init_and_addr(DstTONs data, cell code) {
  cell data_cl =
    prepare_persistent_data<IstTONs, sttons_replay_protection_t, DstTONs>(
      sttons_replay_protection_t::init(), data
    );
  StateInit sttons_init {
    /*split_depth*/{}, /*special*/{},
    code, data_cl, /*library*/{}
  };
  cell init_cl = build(sttons_init).make_cell();
  return { sttons_init, uint256(tvm_hash(init_cl)) };
}

}} // namespace tvm::schema

