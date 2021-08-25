#include "TradingPair.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

class TradingPair final : public smart_interface<ITradingPair>, public DTradingPair {
public:
  struct error_code : tvm::error_code {
    static constexpr unsigned not_enough_tons = 101;
  };

  __always_inline
  bool_t onDeploy() {
    require(int_value().get() > deploy_value_, error_code::not_enough_tons);

    tvm_rawreserve(deploy_value_.get(), rawreserve_flag::up_to);
    set_int_return_flag(SEND_ALL_GAS);
    return bool_t{true};
  }

  __always_inline
  address getFLeXAddr() {
    return flex_addr_;
  }

  __always_inline
  address getTip3Root() {
    return tip3_root_;
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

