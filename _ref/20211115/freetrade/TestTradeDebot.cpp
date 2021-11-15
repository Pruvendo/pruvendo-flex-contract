#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/string.hpp>
#include <tvm/debot.hpp>
#include <tvm/default_support_functions.hpp>
#include <tvm/Console.hpp>
#include "Proxy.hpp"
#include "Flex.hpp"
#include "FlexWallet.hpp"
#include "Wrapper.hpp"
#include "RootTokenContract.hpp"

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
  if (!Cond) {            \
    co_await printf(Str); \
    co_return;            \
  }

__interface [[no_pubkey]] ITestTradeDebot {

  [[external]]
  void constructor() = 1;

  [[external]]
  resumable<void> start() = 2;
};

struct DTestTradeDebot {
  std::optional<address> client1_addr_;
  optcell flex_wallet_code_;
  optcell flex_wrapper_code_;
  optcell ext_wallet_code_;
  optcell ext_troot_code_;
};

__interface ETestTradeDebot {
};

__interface [[no_pubkey, no_expire]] IGiver {
  [[external]]
  void grant(address addr);
};
using IGiverPtr = handle<IGiver>;

class TestTradeDebot final : public smart_interface<ITestTradeDebot>, public DTestTradeDebot {
  struct error_code : tvm::error_code {
    static constexpr unsigned unexpected_pair_address = 101;
  };

  static constexpr uint256 RunIdx = uint256(1);

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
    co_await cout().print("Trade Test Debot");
    cell proxy_code = co_await cout().inputCode("Proxy.tvc");
    cell flex_code = co_await cout().inputCode("Flex.tvc");
    co_await printf("[Test] Flex code loaded");
    cell pair_code = co_await cout().inputCode("TradingPair.tvc");
    co_await printf("[Test] TradingPair code loaded");
    cell xchg_pair_code = co_await cout().inputCode("XchgPair.tvc");
    co_await printf("[Test] XchgPair code loaded");
    cell price_code = co_await cout().inputCode("Price.tvc");
    co_await printf("[Test] Price code loaded");
    cell xchg_price_code = co_await cout().inputCode("PriceXchg.tvc");
    co_await printf("[Test] PriceXchg code loaded");
    flex_wallet_code_ = co_await cout().inputCode("../tokens/fungible/FlexWallet.tvc");
    co_await printf("[Test] FlexWallet code loaded");
    flex_wrapper_code_ = co_await cout().inputCode("../tokens/fungible/Wrapper.tvc");
    co_await printf("[Test] Wrapper code loaded");
    ext_wallet_code_ = co_await cout().inputCode("../tokens/fungible/TONTokenWallet.tvc");
    co_await printf("[Test] TONTokenWallet code loaded");
    ext_troot_code_ = co_await cout().inputCode("../tokens/fungible/RootTokenContract.tvc");
    co_await printf("[Test] RootTokenContract code loaded");

    auto giver_addr = address::make_std(0_i8, uint256(0x653b9a6452c7a982c6dc92b2da9eba832ade1c467699ebb3b43dca6d77b780dd));
    co_await printf("[Test] giver_addr: {address}", giver_addr);
    auto giver_pubkey = co_await cout().loadkey("~/giver_keys.json");
    co_await printf("[Test] giver pubkey: {uint256}", giver_pubkey);

    //auto proxy_pubkey = co_await cout().genkey();
    auto proxy_pubkey = giver_pubkey;
    co_await printf("[Test] Proxy pubkey: {uint256}", proxy_pubkey);
    auto [proxy_init, proxy_addr] = prepare_proxy_state_init_and_addr(0_i8, proxy_code, {proxy_pubkey});
    co_await printf("[Test] Requesting giver grant to: {address}", proxy_addr);
    IGiverPtr(giver_addr).debot_ext_in_nosign().grant(proxy_addr);
    co_await printf("[Test] Giver grant processing: {address}", proxy_addr);
    co_await printf("[Test] Giver grant processed: {address}", proxy_addr);
    co_await IProxyPtr(proxy_addr).deploy_ext(proxy_pubkey, proxy_init).onDeploy();
    co_await printf("[Test] Proxy deploying: {address}", proxy_addr);
    co_await printf("[Test] Proxy deployed: {address}", proxy_addr);

    client1_addr_ = co_await cout().requestProxy("Proxy will be used as a client contract");
    co_await printf("[Test] Proxy defined");
    TonsConfig tons_cfg {
      .transfer_tip3 = 0.2_UT,
      .return_ownership = 0.2_UT,
      .trading_pair_deploy = 1_UT,
      .order_answer = 0.1_UT,
      .process_queue = 0.4_UT,
      .send_notify = 0.1_UT
    };
    address notify_addr = co_await cout().inputAddress("Address for AMM notifications:", "AMM");
    uint256 deployer_pubkey = co_await cout().inputPubkey("Flex deployer pubkey:");
    auto root_ptr = deployFlex(flex_code, tons_cfg, deployer_pubkey, 10_u8, notify_addr);
    co_await printf("[Test] Flex deploying: {address}", root_ptr.get());
    co_await printf("[Test] Flex deployed: {address}", root_ptr.get());
    co_await printf("[Test] Flex.setPairCode");
    //co_await root_ptr.debot_ext_in().setPairCode(pair_code);
    co_await printf("[Test] Flex.setXchgPairCode");
    //co_await root_ptr.debot_ext_in().setXchgPairCode(xchg_pair_code);
    co_await printf("[Test] Flex.setPriceCode");
    //co_await root_ptr.debot_ext_in().setPriceCode(price_code);
    co_await printf("[Test] Flex.setXchgPriceCode");
    //co_await root_ptr.debot_ext_in().setXchgPriceCode(xchg_price_code);

    ASSERT(co_await root_ptr.run().isFullyInitialized(), "[ERROR] Flex is not initialized, exiting...");

    auto nuka_root_pubkey = co_await cout().genkey();
    co_await printf("[Test] Nuka root pubkey: {uint256}", nuka_root_pubkey);

    string nuka_name = "Nuka caps";
    string nuka_symbol = "NUKA";
    auto nuka_decimals = 0_u8;
    auto nuka_root = deployTokenRoot(
      nuka_name, nuka_symbol, nuka_decimals,
      nuka_root_pubkey, 20000_u128, 0_u128, 0_i8);
    co_await printf("[Test] Nuka root deploying: {address}", nuka_root.get());
    co_await printf("[Test] Nuka root deployed: {address}", nuka_root.get());

    auto nuka1_pubkey = co_await cout().genkey();
    co_await printf("[Test] Nuka wallet1 pubkey: {uint256}", nuka1_pubkey);

    auto nuka1_wallet = deployWallet(
      nuka_name, nuka_symbol, nuka_decimals,
      nuka_root_pubkey, nuka1_pubkey, nuka_root.get(), *client1_addr_, 0_i8);
    co_await printf("[Test] Nuka wallet #1 deploying: {address}", nuka1_wallet.get());
    co_return;
  }

  __always_inline
  IFlexPtr deployFlex(
    cell flex_code, TonsConfig tons_cfg, uint256 deployer_pubkey,
    uint8 deals_limit, address notify_addr
  ) {
    DFlex flex_data {
      .deployer_pubkey_ = deployer_pubkey,
      .tons_cfg_ = tons_cfg,
      .pair_code_ = {},
      .xchg_pair_code_ = {},
      .price_code_ = {},
      .xchg_price_code_ = {},
      .deals_limit_ = deals_limit
    };
    auto [flex_init, hash_addr] = prepare_flex_state_init_and_addr(flex_data, flex_code);
    IFlexPtr flex_addr(address::make_std(int8(0), hash_addr));
    flex_addr.deploy_noop(flex_init, 1_T);
    return flex_addr;
  }

  __always_inline
  IWrapperPtr deployWrapper(
    bytes name, bytes symbol, uint8 decimals,
    uint256 root_pubkey, address external_wallet, int8 workchain_id
  ) {
    DWrapper wrapper_data {
      .name_ = name,
      .symbol_ = symbol,
      .decimals_ = decimals,
      .workchain_id_ = workchain_id,
      .root_public_key_ = root_pubkey,
      .total_granted_ = 0_u128,
      .internal_wallet_code_ = flex_wallet_code_,
      .owner_address_ = *client1_addr_,
      .start_balance_ = 1_T,
      .external_wallet_ = external_wallet
    };
    auto [wrapper_init, hash_addr] = prepare_wrapper_state_init_and_addr(flex_wrapper_code_.get(), wrapper_data);
    IWrapperPtr wrapper_addr(address::make_std(workchain_id, hash_addr));
    wrapper_addr.deploy_noop(wrapper_init, 1_T);
    return wrapper_addr;
  }

  __always_inline
  IRootTokenContractPtr deployTokenRoot(
    string name, string symbol, uint8 decimals,
    uint256 root_pubkey, uint128 total_supply, uint128 total_granted,
    int8 workchain_id
  ) {
    DRootTokenContract root_data {
      .name_ = name,
      .symbol_ = symbol,
      .decimals_ = decimals,
      .root_public_key_ = root_pubkey,
      .total_supply_ = total_supply,
      .total_granted_ = total_granted,
      .wallet_code_ = ext_wallet_code_,
      .owner_address_ = *client1_addr_,
      .start_balance_ = 1_T
    };
    auto [root_init, hash_addr] = prepare_root_state_init_and_addr(ext_troot_code_.get(), root_data);
    IRootTokenContractPtr root_addr(address::make_std(workchain_id, hash_addr));
    root_addr.deploy_noop(root_init, 1_T);
    return root_addr;
  }

  __always_inline
  ITONTokenWalletPtr deployWallet(
    string name, string symbol, uint8 decimals,
    uint256 root_pubkey, uint256 wallet_pubkey,
    address root_address, address owner_addr, int8 workchain_id
  ) {
    auto [wallet_init, hash_addr] = prepare_internal_wallet_state_init_and_addr(
      name, symbol, decimals,
      root_pubkey, wallet_pubkey, root_address,
      owner_addr, flex_wallet_code_.get(), workchain_id);
    ITONTokenWalletPtr wallet_addr(address::make_std(workchain_id, hash_addr));
    wallet_addr.deploy_noop(wallet_init, 1_T);
    return wallet_addr;
  }

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }

  DEFAULT_SUPPORT_FUNCTIONS(ITestTradeDebot, void)
};

DEFINE_JSON_ABI(ITestTradeDebot, DTestTradeDebot, ETestTradeDebot);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(TestTradeDebot, ITestTradeDebot, DTestTradeDebot)

