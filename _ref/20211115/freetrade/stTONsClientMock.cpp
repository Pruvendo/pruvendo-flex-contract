#include "stTONsClientMock.hpp"
#include "stTONs.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>
#include <tvm/suffixes.hpp>

using namespace tvm;
using namespace schema;

static constexpr unsigned TIMESTAMP_DELAY = 1800;

class stTONsClientMock final : public smart_interface<IstTONsClientMock>, public DstTONsClientMock {
public:
  using replay_protection_t = replay_attack_protection::timestamp<TIMESTAMP_DELAY>;

  struct error_code : tvm::error_code {
    static constexpr unsigned sender_is_not_my_owner = 100;
  };

  __always_inline
  void constructor(uint256 owner_pubkey) {
    owner_pubkey_ = owner_pubkey;
  }

  __always_inline
  address deployStTONs(
    uint128 crystals,
    cell code,
    uint256 owner_pubkey,
    std::optional<address> owner_address,
    address depool,
    uint256 depool_pubkey
  ) {
    require(msg_pubkey() == owner_pubkey_, error_code::sender_is_not_my_owner);
    tvm_accept();
    DstTONs data {
      .owner_pubkey_ = owner_pubkey,
      .owner_address_ = owner_address,
      .depool_ = depool,
      .depool_pubkey_ = depool_pubkey,
      .balance_ = 0u128,
      .lend_ownership_ = {},
      .transferring_stake_back_ = bool_t{false},
      .last_depool_error_ = 0u8
    };
    auto [init, hash] = prepare_sttons_state_init_and_addr(data, code);
    auto workchain_id = std::get<addr_std>(address{tvm_myaddr()}.val()).workchain_id;
    IstTONsPtr dst(address::make_std(workchain_id, hash));
    dst.deploy(init, Grams(crystals.get())).onDeploy();
    return dst.get();
  }

  __always_inline
  void returnStake(
    address stTONsAddr,
    address dst,
    uint128 processing_crystals,
    uint128 depool_processing_crystals
  ) {
    require(msg_pubkey() == owner_pubkey_, error_code::sender_is_not_my_owner);
    tvm_accept();
    IstTONsPtr(stTONsAddr)(Grams(processing_crystals.get())).
      returnStake(dst, depool_processing_crystals);
  }

  __always_inline
  void finalize(
    address stTONsAddr,
    address dst,
    uint128 processing_crystals,
    bool_t ignore_errors
  ) {
    require(msg_pubkey() == owner_pubkey_, error_code::sender_is_not_my_owner);
    tvm_accept();
    IstTONsPtr(stTONsAddr)(Grams(processing_crystals.get())).
      finalize(dst, ignore_errors);
  }

  __always_inline
  uint256 getOwnerPubkey() {
    return owner_pubkey_;
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IstTONsClientMock, replay_protection_t)

  // default processing of unknown messages
  //__always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
  //  return 0;
  //}
};

DEFINE_JSON_ABI(IstTONsClientMock, DstTONsClientMock, EstTONsClientMock);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS(stTONsClientMock, IstTONsClientMock, DstTONsClientMock, TIMESTAMP_DELAY)

