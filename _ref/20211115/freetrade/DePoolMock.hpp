#pragma once

#include <tvm/schema/message.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/replay_attack_protection/timestamp.hpp>

namespace tvm { inline namespace schema {

static constexpr unsigned DEPOOL_MOCK_TIMESTAMP_DELAY = 1800;
using depool_mock_replay_protection_t = replay_attack_protection::timestamp<DEPOOL_MOCK_TIMESTAMP_DELAY>;

struct TransferRecord {
  address dst;
  address src;
  uint128 amount;
  uint64  timestamp;
};

struct DePoolMockDetails {
  uint256 owner_pubkey;
  dict_array<TransferRecord> fwd_records;
  dict_array<TransferRecord> bck_records;
};

__interface IParticipant {
  [[internal, noaccept]]
  void onTransfer(address source, uint128 amount) = 0x23c4771d;
<<<<<<< HEAD
=======
  [[internal, noaccept]]
  void receiveAnswer(uint32 errcode, uint64 comment) = 0x3f109e44;
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
};
using IParticipantPtr = handle<IParticipant>;

__interface IDePoolMock {

  [[external]]
  void constructor(uint256 owner_pubkey);

  [[external, noaccept]]
  void sendOnTransfer(address dst, address src, uint128 amount);

  [[internal, noaccept]]
  void transferStake(address destination, uint64 amount) = 0x6810bf4e;

  // ========== getters ==========
  [[getter]]
  DePoolMockDetails getDetails() = 20;
};
using IDePoolMockPtr = handle<IDePoolMock>;

struct DDePoolMock {
  uint256 owner_pubkey_;
  dict_array<TransferRecord> fwd_records_;
  dict_array<TransferRecord> bck_records_;
};

__interface EDePoolMock {
};

}} // namespace tvm::schema

