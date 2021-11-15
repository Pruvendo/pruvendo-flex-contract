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
#include "Proxy.hpp"
#include "Flex.hpp"
#include "PriceXchg.hpp"
#include "XchgPair.hpp"
#include "FlexClient.hpp"

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

uint128 operator "" _u128(unsigned long long v) {
  return uint128(v);
}
uint256 operator "" _u256(unsigned long long v) {
  return uint256(v);
}
uint8 operator "" _u8(unsigned long long v) {
  return uint8(v);
}
int8 operator "" _i8(unsigned long long v) {
  return int8(v);
}

#define ASSERT(Cond, Str) \
  if (!(Cond)) {            \
    co_await printf(Str); \
    co_return;            \
  }

__interface [[no_pubkey]] IFlexClientTest {

  [[external]]
  void constructor() = 1;

  [[external]]
  resumable<void> start() = 2;
};

struct DFlexClientTest {
};

__interface EFlexClientTest {
};

__interface [[no_pubkey, no_expire]] IGiver {
  [[external]]
  void grant(address addr);
};
using IGiverPtr = handle<IGiver>;

class FlexClientTest final : public smart_interface<IFlexClientTest>, public DFlexClientTest {

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
    co_await cout().print("FlexClient testing...");
    cell flex_client_code = co_await cout().inputCode("FlexClient.tvc");
    cell trading_pair_code = co_await cout().inputCode("TradingPair.tvc");
    cell xchg_pair_code = co_await cout().inputCode("XchgPair.tvc");
    cell tip3_root_code = co_await cout().inputCode("../tokens/fungible/RootTokenContract.tvc");

    uint256 flex_client_pubkey = co_await cout().genkey();
    cell flex_client_data_cl = builder().stu(1, 1).stu(flex_client_pubkey.get(), 256).endc();
    StateInit flex_client_init {
      /*split_depth*/{}, /*special*/{},
      flex_client_code, flex_client_data_cl, /*library*/{}
    };
    cell init_cl = build(flex_client_init).endc();
    auto flex_client_addr = address::make_std(0_i8, uint256(tvm_hash(init_cl)));
    co_await printf("[Test] flex_client_addr (future): {address}", flex_client_addr);

    auto giver_addr = address::make_std(0_i8, uint256(0x653b9a6452c7a982c6dc92b2da9eba832ade1c467699ebb3b43dca6d77b780dd));
    co_await printf("[Test] giver_addr: {address}", giver_addr);
    co_await printf("[Test] Requesting giver grant to: {address}", flex_client_addr);
    IGiverPtr(giver_addr).debot_ext_in_nosign().grant(flex_client_addr);
    co_await printf("[Test] Giver grant processed: {address}", flex_client_addr);
    co_await IFlexClientPtr(flex_client_addr).deploy_ext(flex_client_pubkey, flex_client_init)
      .constructor(flex_client_pubkey, trading_pair_code, xchg_pair_code);
    co_await printf("[Test] FlexClient deployed: {address}", flex_client_addr);

    IFlexClientPtr client_ptr(flex_client_addr);
    ASSERT(!co_await client_ptr.run().hasExtWalletCode(), "Ext wallet code already set up");
    ASSERT(!co_await client_ptr.run().hasFlexWalletCode(), "Flex wallet code already set up");
    ASSERT(!co_await client_ptr.run().hasFlexWrapperCode(), "Flex wrapper code already set up");

    // ========================================== //
    co_await cout().print("Deploying external token root...");

    string tip3name = "Funtics";
    string tip3sym = "FUN";
    auto tip3decim = 0_u8;

    uint256 tip3_root_pubkey = co_await cout().genkey();
    cell root_data_cl = builder().stu(1, 1).stu(tip3_root_pubkey.get(), 256).endc();
    StateInit root_init {
      /*split_depth*/{}, /*special*/{},
      tip3_root_code, root_data_cl, /*library*/{}
    };
    cell root_init_cl = build(root_init).endc();
    auto root_addr = address::make_std(0_i8, uint256(tvm_hash(root_init_cl)));
    co_await printf("[Test] root_addr (future): {address}", root_addr);

    co_await printf("[Test] Requesting giver grant to: {address}", root_addr);
    IGiverPtr(giver_addr).debot_ext_in_nosign().grant(root_addr);
    co_await printf("[Test] Giver grant processed: {address}", root_addr);
    co_await IRootTokenContractPtr(root_addr).deploy_ext(tip3_root_pubkey, root_init)
      .constructor(tip3name, tip3sym, tip3decim, tip3_root_pubkey,
                   address::make_std(0_i8, 0_u256), 100000_u128);
    co_await printf("[Test] RootTokenContract deployed: {address}", root_addr);

    // Deploying user ext wallet
    co_await cout().print("Deploying user ext wallet...");
    uint256 user_wallet_pubkey = co_await cout().genkey();
    IRootTokenContractPtr root_ptr(root_addr);
    auto user_ext_wallet = ITONTokenWalletPtr(
      co_await root_ptr.debot_ext_in().deployWallet(user_wallet_pubkey, address::make_std(0_i8, 0_u256), 50000_u128, 5_UT)
      );

    // ========================================== //

    co_await cout().print("Deploying wrapper...");

    cell ext_wallet_code = co_await cout().inputCode("../tokens/fungible/TONTokenWallet.tvc");
    cell flex_wallet_code = co_await cout().inputCode("../tokens/fungible/FlexWallet.tvc");
    cell flex_wrapper_code = co_await cout().inputCode("../tokens/fungible/Wrapper.tvc");

    co_await client_ptr.debot_ext_in().setExtWalletCode(ext_wallet_code);
    co_await client_ptr.debot_ext_in().setFlexWalletCode(flex_wallet_code);
    co_await client_ptr.debot_ext_in().setFlexWrapperCode(flex_wrapper_code);

    ASSERT(co_await client_ptr.run().hasExtWalletCode(), "Ext wallet code not set up");
    ASSERT(co_await client_ptr.run().hasFlexWalletCode(), "Flex wallet code not set up");
    ASSERT(co_await client_ptr.run().hasFlexWrapperCode(), "Flex wrapper code not set up");

    Tip3Config tip3cfg {
      .name = tip3name,
      .symbol = tip3sym,
      .decimals = tip3decim,
      .root_public_key = tip3_root_pubkey,
      .root_address = root_addr
    };

    auto wrapper_pubkey = co_await cout().genkey();

    FlexDeployWrapperArgs deploy_args {
      .wrapper_pubkey = wrapper_pubkey,
      .wrapper_deploy_value = 1.5_UT,
      .wrapper_keep_balance = 1_UT,
      .ext_wallet_balance = 1_UT,
      .set_internal_wallet_value = 0.5_UT,
      .tip3cfg = {tip3cfg}
      };
    auto wrapper_ptr = IWrapperPtr(co_await client_ptr.debot_ext_in().deployWrapperWithWallet(build(deploy_args).endc()));
    co_await printf("Wrapper deployed = {address}", wrapper_ptr.get());
    auto wrapper_ext_wallet = (co_await wrapper_ptr.run().getDetails()).external_wallet;
    co_await printf("Wrapper ext wallet deployed = {address}", wrapper_ext_wallet);

    // external -> internal conversion
    auto flex_funtics_pubkey = co_await cout().genkey();
    co_await printf("[Test] Now testing Funtics external->internal conversion");
    cell payload = build(FLeXDeployWalletArgs{flex_funtics_pubkey, client_ptr.get(), 1_UT}).endc();
    co_await user_ext_wallet.debot_ext_in().
      transferWithNotify(
        user_ext_wallet.get(), wrapper_ext_wallet, 20000_u128, 1_UT, bool_t{false}, payload
      );

    auto flex_wallet = ITONTokenWalletPtr(co_await wrapper_ptr.run().getWalletAddress(flex_funtics_pubkey, client_ptr.get()));
    co_await printf("Flex wallet deployed = {address}", flex_wallet.get());

    PRINT_TIP3_DETAILS(co_await flex_wallet.run().getDetails());

    FlexBurnWalletArgs burn_params {
      .tons_value = 1_UT,
      .out_pubkey = user_wallet_pubkey,
      .out_internal_owner = address::make_std(0_i8, 0_u256),
      .my_tip3_addr = flex_wallet.get()
      };
    co_await client_ptr.debot_ext_in().burnWallet(build(burn_params).endc());

    auto ext_wallet_info_after = co_await user_ext_wallet.run().getDetails();
    co_await printf("User ext wallet after back conversion: {address}", user_ext_wallet.get());
    PRINT_TIP3_DETAILS(ext_wallet_info_after);
    ASSERT(ext_wallet_info_after.balance == 50000, "Incorrect balance after burn");

    co_await printf("[Test] all tests completed");

    co_return;
  }
  DEFAULT_SUPPORT_FUNCTIONS(IFlexClientTest, void)

  // default processing of unknown messages
  __always_inline static int _fallback(cell msg, slice msg_body) {
    return 0;
  }
};

DEFINE_JSON_ABI(IFlexClientTest, DFlexClientTest, EFlexClientTest);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(FlexClientTest, IFlexClientTest, DFlexClientTest)


