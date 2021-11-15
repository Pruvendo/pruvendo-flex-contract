#include "DePoolMock.hpp"
#include "stTONs.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>
<<<<<<< HEAD
=======
#include <tvm/suffixes.hpp>
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055

using namespace tvm;
using namespace schema;

class DePoolMock final : public smart_interface<IDePoolMock>, public DDePoolMock {
public:
  struct error_code : tvm::error_code {
    static constexpr unsigned sender_is_not_my_owner = 100;
  };

  __always_inline
  void constructor(uint256 owner_pubkey) {
    owner_pubkey_ = owner_pubkey;
  }

  __always_inline
  void sendOnTransfer(address dst, address source, uint128 amount) {
    require(msg_pubkey() == owner_pubkey_, error_code::sender_is_not_my_owner);
    tvm_accept();
    fwd_records_.push_back({dst, source, amount, uint64(tvm_now())});
    IParticipantPtr(dst)(Grams(10000000), SENDER_WANTS_TO_PAY_FEES_SEPARATELY).
      onTransfer(source, amount);
  }

  __always_inline
  void transferStake(address destination, uint64 amount) {
    bck_records_.push_back({destination, int_sender(), uint128(amount.get()), uint64(tvm_now())});
<<<<<<< HEAD
=======
    tvm_rawreserve(tvm_balance() - int_value().get(), rawreserve_flag::up_to);
    IParticipantPtr(int_sender())(Grams(0), SEND_ALL_GAS).
      receiveAnswer(0u32, 0u64);
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
  }

  __always_inline
  DePoolMockDetails getDetails() {
    return { owner_pubkey_, fwd_records_, bck_records_ };
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IDePoolMock, depool_mock_replay_protection_t)

  // default processing of unknown messages
  //__always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
  //  return 0;
  //}
};

DEFINE_JSON_ABI(IDePoolMock, DDePoolMock, EDePoolMock);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS(DePoolMock, IDePoolMock, DDePoolMock, DEPOOL_MOCK_TIMESTAMP_DELAY)

