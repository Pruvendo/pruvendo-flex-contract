#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/string.hpp>
#include <tvm/debot.hpp>
#include <tvm/default_support_functions.hpp>
#include <tvm/Console.hpp>
#include "TONTokenWallet.hpp"

using namespace tvm;
using namespace schema;
using namespace debot;

__interface [[no_pubkey]] ITip3Debot {

  [[external]]
  void constructor() = 1;

  [[external]]
  resumable<void> start() = 2;
};

struct DTip3Debot {
  std::optional<ITONTokenWalletPtr> tip3_;
};

__interface ETip3Debot {
};

class Tip3Debot final : public smart_interface<ITip3Debot>, public DTip3Debot {

  IConsolePtr cout_ptr_ = IConsolePtr(address::make_std(schema::int8{0}, schema::uint256{0}));

  __always_inline IConsolePtr::proxy cout() {
    return cout_ptr_();
  }
  __always_inline
  auto printf(string fmt) {
    cell params = builder().endc();
    return cout().printf(fmt, params);
  }
  template<typename... Args>
  __always_inline
  auto printf(string fmt, Args... args) {
    auto tup = std::make_tuple(args...);
    auto chain = make_chain_tuple(tup);
    cell params = build(chain).endc();
    return cout().printf(fmt, params);
  }
public:
  __always_inline
  void constructor() override {
  }

  // co_awaits in nested function calls require additional support, so we use macros here
#define PRINT_TIP3_DETAILS(tip3info_in)                                                            \
    {                                                                                              \
      const auto tip3info_temp = (tip3info_in);                                                    \
      co_await printf("Name:");                                                                    \
      co_await cout().print(tip3info_temp.name);                                                   \
      co_await printf("Symbol:");                                                                  \
      co_await cout().print(tip3info_temp.symbol);                                                 \
      co_await printf("Decimals: {uint8}", tip3info_temp.decimals);                                \
      co_await printf("Balance: {uint128}", tip3info_temp.balance);                                \
      if (tip3info_temp.lend_ownership.empty()) {                                                  \
        co_await cout().print("Lend owner: None");                                                 \
      } else {                                                                                     \
        for (auto v : tip3info_temp.lend_ownership) {                                              \
          co_await printf("Lend owner: {address}", (address)v.lend_addr);                          \
          co_await printf("Lend balance: {uint128}", v.lend_balance);                              \
          co_await printf("Lend finish time: {datetime}", uint32(v.lend_finish_time.get()));       \
        }                                                                                          \
      }                                                                                            \
    }

  __always_inline
  resumable<void> start() override {
    co_await cout().print("Hello, I am Tip3 Debot!");
    tip3_ = ITONTokenWalletPtr(co_await cout().inputAddress("Tip3 token wallet address:", "TIP3WALLET"));
    auto tip3info = co_await tip3_->run().getDetails();
    PRINT_TIP3_DETAILS(tip3info);
    do {
      co_await cout().iAmHome();
      co_await printf("1). transfer\n"
                      "5). Exit");
      auto select = co_await cout().inputUint256("");
      switch (select.get()) {
      case 1: {
        auto to = ITONTokenWalletPtr(co_await cout().inputAddress("Destination tip3 token wallet address:", "TIP3WALLET"));
        PRINT_TIP3_DETAILS((co_await to.run().getDetails()));
        auto tokens = uint128((co_await cout().inputUint256("Transfer tokens:")).get());
        auto grams = uint128((co_await cout().inputTONs("Processing value (extra will return): ")).get());
        co_await tip3_->debot_ext_in().transfer(tip3_->get(), to.get(), tokens, grams, bool_t{false});
      } break;
      case 5: {
        co_await printf("Exiting...");
        co_return;
      } break;
      }
    } while(true);
  }
  DEFAULT_SUPPORT_FUNCTIONS(ITip3Debot, void)

  // default processing of unknown messages
  __always_inline static int _fallback(cell msg, slice msg_body) {
    return 0;
  }
};

DEFINE_JSON_ABI(ITip3Debot, DTip3Debot, ETip3Debot);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(Tip3Debot, ITip3Debot, DTip3Debot)


