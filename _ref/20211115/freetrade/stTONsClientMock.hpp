#pragma once

#include <tvm/schema/message.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/replay_attack_protection/timestamp.hpp>

namespace tvm { inline namespace schema {

__interface IstTONsClientMock {

  [[external]]
  void constructor(uint256 owner_pubkey);

  [[external, noaccept]]
<<<<<<< HEAD
  void storeCrystalls(address client_addr, address dst, uint128 amount);

  [[external, noaccept]]
  void sendTransferBack(address stTONsAddr, address wallet, uint128 crystals, uint128 amount);
=======
  address deployStTONs(
    uint128 crystals,
    cell code,
    uint256 owner_pubkey,
    std::optional<address> owner_address,
    address depool,
    uint256 depool_pubkey
  );

  [[external, noaccept]]
  void returnStake(
    address stTONsAddr,
    address dst,
    uint128 processing_crystals,
    uint128 depool_processing_crystals
  );

  [[external, noaccept]]
  void finalize(
    address stTONsAddr,
    address dst,
    uint128 processing_crystals,
    bool_t ignore_errors
  );
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055

  // ========== getters ==========
  [[getter]]
  uint256 getOwnerPubkey();
};
using IstTONsClientMockPtr = handle<IstTONsClientMock>;

struct DstTONsClientMock {
  uint256 owner_pubkey_;
};

__interface EstTONsClientMock {
};

}} // namespace tvm::schema
