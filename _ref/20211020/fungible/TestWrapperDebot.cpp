#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/string.hpp>
#include <tvm/debot.hpp>
#include <tvm/default_support_functions.hpp>
#include <tvm/Console.hpp>
#include "TONTokenWallet.hpp"
#include "RootTokenContract.hpp"
#include "Wrapper.hpp"

using namespace tvm;
using namespace schema;
using namespace debot;

static constexpr unsigned one_full_ton_size = 1000000000;

Grams operator "" _T(long double v) {
  return Grams(static_cast<unsigned>(v * one_full_ton_size));
}
Grams operator "" _T(unsigned long long v) {
  return Grams(v * one_full_ton_size);
}
uint128 operator "" _UT(long double v) {
  return uint128(static_cast<unsigned>(v * one_full_ton_size));
}
uint128 operator "" _UT(unsigned long long v) {
  return uint128(v * one_full_ton_size);
}

__interface [[no_pubkey]] ITestWrapperDebot {

  [[external]]
  void constructor() = 1;

  [[external]]
  resumable<void> start() = 2;
};

struct DTestWrapperDebot {
  std::optional<address> client_addr_;
};

__interface ETestWrapperDebot {
};

class TestWrapperDebot final : public smart_interface<ITestWrapperDebot>, public DTestWrapperDebot {
  struct error_code : tvm::error_code {
    static constexpr unsigned unexpected_pair_address = 101;
  };

  static constexpr uint256 RunIdx = uint256(7);

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

  __always_inline
  resumable<void> start() override {
    co_await cout().print("Wrapper Test Debot");
    client_addr_ = co_await cout().requestProxy("Proxy will be used as a client contract");
    cell token_root_code = co_await cout().inputCode("RootTokenContract.tvc");
    cell wrapper_code = co_await cout().inputCode("Wrapper.tvc");
    cell external_wallet_code = co_await cout().inputCode("TONTokenWallet.tvc");
    cell internal_wallet_code = co_await cout().inputCode("FLeXWallet.tvc");

    auto root_ptr = deployTokenRoot(token_root_code);
    co_await printf("[Test] Token root deploying: {address}", root_ptr.get());
    co_await printf("[Test] Token root deployed: {address}", root_ptr.get());
    co_await printf("[Test] Root.setWalletCode");
    co_await root_ptr(0.5_T).setWalletCode(external_wallet_code);
    if (!co_await root_ptr.run().hasWalletCode()) {
      co_await printf("[ERROR] Token root is not initialized, exiting...");
      co_return;
    }

    auto [wrapper_ptr, wrapper_init] = prepareDeployWrapper(wrapper_code, 1_T);
    co_await printf("[Test] Root.deployWallet for wrapper external wallet");
    auto wrapper_external_wallet =
      co_await root_ptr(1.5_T).deployWallet(RunIdx, wrapper_ptr.get(), uint128(0), 1_UT);

    co_await printf("[Test] Wrapper External wallet deployed: {address}", wrapper_external_wallet);

    co_await printf("[Test] Deploying wrapper...");
    co_await wrapper_ptr.deploy(wrapper_init, 1.5_T).init(wrapper_external_wallet);
    co_await printf("[Test] Wrapper deployed: {address}", wrapper_ptr.get());
    co_await printf("[Test] Wrapper.setInternalWalletCode");
    co_await wrapper_ptr(0.5_T).setInternalWalletCode(internal_wallet_code);
    if (!co_await wrapper_ptr.run().hasInternalWalletCode()) {
      co_await printf("[ERROR] Wrapper is not initialized, exiting...");
      co_return;
    }

    co_await printf("[Test] Root.deployWallet for client external wallet");
    auto client_external_wallet =
      ITONTokenWalletPtr(co_await root_ptr(1.5_T).deployWallet(RunIdx, *client_addr_, uint128(12000), 1_UT));
    co_await printf("[Test] Client External wallet deployed: {address}", client_external_wallet.get());

    co_await printf("[Test] Now testing external->internal conversion");

    cell payload = build(FlexDeployWalletArgs{RunIdx, *client_addr_, 1_UT}).endc();
    auto ret = co_await client_external_wallet.tail_call<WrapperRet>(wrapper_ptr.get(), 2_T).
      transferWithNotify(
        *client_addr_, wrapper_external_wallet, uint128(5000), uint128(0), bool_t{false}, payload
      );

    co_await printf("[Test] Wrapper answer: ( err_code: {uint32}, flex_wallet: {address} )", ret.err_code, ret.flex_wallet);
    ITONTokenWalletPtr flex_wallet(ret.flex_wallet);
    auto intern_details = co_await flex_wallet.run().getDetails();
    co_await printf("[Test] intern_details.balance = {uint128}", intern_details.balance);
    if (intern_details.balance != 5000) {
      co_await printf("[ERROR] Incorrect internal balance, exiting...");
      co_return;
    }

    auto wrapper_wallet_details = co_await ITONTokenWalletPtr(wrapper_external_wallet).run().getDetails();
    co_await printf("[Test] wrapper_wallet_details.balance = {uint128}", wrapper_wallet_details.balance);
    if (wrapper_wallet_details.balance != 5000) {
      co_await printf("[ERROR] Incorrect wrapper wallet balance, exiting...");
      co_return;
    }

    auto client_wallet_details = co_await client_external_wallet.run().getDetails();
    co_await printf("[Test] client_wallet_details.balance = {uint128}", client_wallet_details.balance);
    if (client_wallet_details.balance != 12000 - 5000) {
      co_await printf("[ERROR] Incorrect client wallet balance, exiting...");
      co_return;
    }

    flex_wallet(1_T).burn(RunIdx, *client_addr_);
    co_await printf("[Test] FlexWallet.burn");
    co_await printf("[Test] flex wallet after burn: {address}", flex_wallet.get());

    wrapper_wallet_details = co_await ITONTokenWalletPtr(wrapper_external_wallet).run().getDetails();
    co_await printf("[Test] wrapper_wallet_details.balance = {uint128}", wrapper_wallet_details.balance);
    if (wrapper_wallet_details.balance != 0) {
      co_await printf("[ERROR] Incorrect wrapper wallet balance (after burn), exiting...");
      co_return;
    }

    client_wallet_details = co_await client_external_wallet.run().getDetails();
    co_await printf("[Test] client_wallet_details.balance = {uint128}", client_wallet_details.balance);
    if (client_wallet_details.balance != 12000) {
      co_await printf("[ERROR] Incorrect client wallet balance (after burn), exiting...");
      co_return;
    }

    co_return;
  }

  __always_inline
  IRootTokenContractPtr deployTokenRoot(cell token_root_code) {
    DRootTokenContract root_data {
      "Funtics", "FUN", uint8(2),
      /*pubkey*/ RunIdx,
      /*total_supply*/ uint128(200000), /*total_granted*/ uint128(0),
      {}, *client_addr_, 1_T
    };
    auto [root_init, hash_addr] = prepare_root_state_init_and_addr(token_root_code, root_data);
    IRootTokenContractPtr root_addr(address::make_std(int8(0), hash_addr));
    root_addr.deploy_noop(root_init, 1_T);
    return root_addr;
  }

  __always_inline
  std::pair<IWrapperPtr, StateInit> prepareDeployWrapper(cell wrapper_code, Grams start_balance) {
    DWrapper wrapper_data {
      "Funtics", "FUN", uint8(2), int8(0),
      /*pubkey*/ RunIdx,
      /*total_granted*/ uint128(0),
      {}, *client_addr_, start_balance, {}
    };
    auto [wrapper_init, hash_addr] = prepare_wrapper_state_init_and_addr(wrapper_code, wrapper_data);
    IWrapperPtr wrapper_addr(address::make_std(int8(0), hash_addr));
    return { wrapper_addr, wrapper_init };
  }

  DEFAULT_SUPPORT_FUNCTIONS(ITestWrapperDebot, void)

  // default processing of unknown messages
  __always_inline static int _fallback(cell msg, slice msg_body) {
    return 0;
  }
};

DEFINE_JSON_ABI(ITestWrapperDebot, DTestWrapperDebot, ETestWrapperDebot);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(TestWrapperDebot, ITestWrapperDebot, DTestWrapperDebot)

