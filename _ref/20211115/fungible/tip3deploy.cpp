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
#include "../../freetrade/Proxy.hpp"
#include "../../freetrade/Flex.hpp"
#include "../../freetrade/PriceXchg.hpp"
#include "../../freetrade/XchgPair.hpp"

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

__interface [[no_pubkey]] ITip3Deploy {

  [[external]]
  void constructor() = 1;

  [[external]]
  resumable<void> start() = 2;
};

struct DTip3Deploy {
  std::optional<address> client1_addr_;
  optcell flex_wallet_code_;
  optcell flex_wrapper_code_;
  optcell ext_wallet_code_;
  optcell ext_troot_code_;
  std::optional<IRootTokenContractPtr> nuka_root_;
  std::optional<IRootTokenContractPtr> funtics_root_;
  std::optional<IWrapperPtr> nuka_flex_wrapper_;
  std::optional<IWrapperPtr> funtics_flex_wrapper_;
  std::optional<ITONTokenWalletPtr> nuka_wrapper_ext_wallet_;
  std::optional<ITONTokenWalletPtr> funtics_wrapper_ext_wallet_;
  std::optional<ITONTokenWalletPtr> nuka1_ext_wallet_;
  std::optional<ITONTokenWalletPtr> nuka2_ext_wallet_;
  std::optional<ITONTokenWalletPtr> funtics1_ext_wallet_;
  std::optional<ITONTokenWalletPtr> funtics2_ext_wallet_;
  std::optional<ITONTokenWalletPtr> flex_nuka1_wallet_;
  std::optional<ITONTokenWalletPtr> flex_nuka2_wallet_;
  std::optional<ITONTokenWalletPtr> flex_funtics1_wallet_;
  std::optional<ITONTokenWalletPtr> flex_funtics2_wallet_;
  std::optional<IFlexPtr> flex_;
  std::optional<IXchgPairPtr> nuka_fun_pair_;
  std::optional<IPriceXchgPtr> price_ptr_;
};

__interface ETip3Deploy {
};

__interface [[no_pubkey, no_expire]] IGiver {
  [[external]]
  void grant(address addr);
};
using IGiverPtr = handle<IGiver>;

class Tip3Deploy final : public smart_interface<ITip3Deploy>, public DTip3Deploy {

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
    co_await cout().print("Hello, I am Tip3 Deploy Debot!");
    cell proxy_code = co_await cout().inputCode("../../freetrade/Proxy.tvc");
    cell price_code = co_await cout().inputCode("../../freetrade/Price.tvc");
    cell xchg_price_code = co_await cout().inputCode("../../freetrade/PriceXchg.tvc");
    cell flex_code = co_await cout().inputCode("../../freetrade/Flex.tvc");
    cell pair_code = co_await cout().inputCode("../../freetrade/TradingPair.tvc");
    cell xchg_pair_code = co_await cout().inputCode("../../freetrade/XchgPair.tvc");
    flex_wallet_code_ = co_await cout().inputCode("FlexWallet.tvc");
    flex_wrapper_code_ = co_await cout().inputCode("Wrapper.tvc");
    ext_wallet_code_ = co_await cout().inputCode("TONTokenWallet.tvc");
    ext_troot_code_ = co_await cout().inputCode("RootTokenContract.tvc");

    auto giver_addr = address::make_std(0_i8, uint256(0x653b9a6452c7a982c6dc92b2da9eba832ade1c467699ebb3b43dca6d77b780dd));
    co_await printf("[Test] giver_addr: {address}", giver_addr);
    auto proxy_pubkey = co_await cout().genkey();
    co_await printf("[Test] Proxy pubkey: {uint256}", proxy_pubkey);

    auto [proxy_init, proxy_addr] = prepare_proxy_state_init_and_addr(0_i8, proxy_code, {proxy_pubkey});
    co_await printf("[Test] Requesting giver grant to: {address}", proxy_addr);
    IGiverPtr(giver_addr).debot_ext_in_nosign().grant(proxy_addr);
    co_await printf("[Test] Giver grant processed: {address}", proxy_addr);
    co_await IProxyPtr(proxy_addr).deploy_ext(proxy_pubkey, proxy_init).onDeploy();
    co_await printf("[Test] Proxy deployed: {address}", proxy_addr);

    co_await cout().setProxy(proxy_addr, proxy_pubkey);
    client1_addr_ = proxy_addr;

    // =================== Deploying external NUKA token root =================== //
    auto nuka_root_pubkey = co_await cout().genkey();
    co_await printf("[Test] Nuka root pubkey: {uint256}", nuka_root_pubkey);
    string nuka_name = "Nuka caps";
    string nuka_symbol = "NUKA";
    auto nuka_decimals = 0_u8;
    nuka_root_ = deployTokenRoot(nuka_name, nuka_symbol, nuka_decimals, nuka_root_pubkey, 20000_u128, 0_u128, 0_i8);
    co_await printf("[Test] NUKA Token root deploying: {address}", nuka_root_->get());
    co_await printf("[Test] NUKA Token root deployed: {address}", nuka_root_->get());
    co_await printf("[Test] NUKA Root.setWalletCode");
    co_await (*nuka_root_)(0.5_T).setWalletCode(ext_wallet_code_.get());
    ASSERT(co_await nuka_root_->run().hasWalletCode(), "[ERROR] Token root is not initialized, exiting...");

    // ========== Prepare flex wrapper deploy to calculate address ========= //
    auto nuka_wrapper_pubkey = co_await cout().genkey();
    co_await printf("[Test] NUKA wrapper pubkey: {uint256}", nuka_wrapper_pubkey);
    auto [nuka_flex_wrapper_addr, nuka_wrapper_init] = prepareDeployWrapper(nuka_name, nuka_symbol, nuka_decimals, nuka_wrapper_pubkey);
    nuka_flex_wrapper_ = nuka_flex_wrapper_addr;

    // ============= Deploying external wallet for Flex wrapper ============ //
    nuka_wrapper_ext_wallet_ = deployWallet(nuka_name, nuka_symbol, nuka_decimals,
      nuka_root_pubkey, nuka_wrapper_pubkey, nuka_root_->get(), nuka_flex_wrapper_->get(), 0_i8);
    co_await printf("[Test] NUKA Wrapper ext wallet deploying: {address}", nuka_wrapper_ext_wallet_->get());
    co_await printf("[Test] NUKA Wrapper ext wallet deployed: {address}", nuka_wrapper_ext_wallet_->get());
    PRINT_TIP3_DETAILS((co_await nuka_wrapper_ext_wallet_->run().getDetails()));

    // ================== Deploying Flex wrapper for Nuka ================== //
    co_await nuka_flex_wrapper_->deploy(nuka_wrapper_init, 1.5_T).init(nuka_wrapper_ext_wallet_->get());
    co_await printf("[Test] NUKA Wrapper deployed: {address}", nuka_flex_wrapper_->get());
    co_await printf("[Test] NUKA Wrapper.setInternalWalletCode");
    co_await (*nuka_flex_wrapper_)(0.5_T).setInternalWalletCode(flex_wallet_code_.get());
    ASSERT(co_await nuka_flex_wrapper_->run().hasInternalWalletCode(), "[ERROR] NUKA Wrapper is not initialized, exiting...");

    // =================== Deploying external FUNTICS token root =================== //
    auto funtics_root_pubkey = co_await cout().genkey();
    co_await printf("[Test] Funtics root pubkey: {uint256}", funtics_root_pubkey);
    string funtics_name = "Funtics";
    string funtics_symbol = "FUN";
    auto funtics_decimals = 0_u8;
    funtics_root_ = deployTokenRoot(funtics_name, funtics_symbol, funtics_decimals, funtics_root_pubkey, 200000_u128, 0_u128, 0_i8);
    co_await printf("[Test] FUNTICS Token root deploying: {address}", funtics_root_->get());
    co_await printf("[Test] FUNTICS Token root deployed: {address}", funtics_root_->get());
    co_await printf("[Test] FUNTICS Root.setWalletCode");
    co_await (*funtics_root_)(0.5_T).setWalletCode(ext_wallet_code_.get());
    ASSERT(co_await funtics_root_->run().hasWalletCode(), "[ERROR] Token root is not initialized, exiting...");

    // ========== Prepare flex wrapper deploy to calculate address ========= //
    auto funtics_wrapper_pubkey = co_await cout().genkey();
    co_await printf("[Test] FUNTICS wrapper pubkey: {uint256}", funtics_wrapper_pubkey);
    auto [funtics_flex_wrapper_addr, funtics_wrapper_init] =
      prepareDeployWrapper(funtics_name, funtics_symbol, funtics_decimals, funtics_wrapper_pubkey);
    funtics_flex_wrapper_ = funtics_flex_wrapper_addr; 

    // ============= Deploying external wallet for Funtics Flex wrapper ============ //
    funtics_wrapper_ext_wallet_ = deployWallet(funtics_name, funtics_symbol, funtics_decimals,
      funtics_root_pubkey, funtics_wrapper_pubkey, funtics_root_->get(), funtics_flex_wrapper_->get(), 0_i8);
    co_await printf("[Test] FUNTICS Wrapper ext wallet deploying: {address}", funtics_wrapper_ext_wallet_->get());
    co_await printf("[Test] FUNTICS Wrapper ext wallet deployed: {address}", funtics_wrapper_ext_wallet_->get());
    PRINT_TIP3_DETAILS((co_await funtics_wrapper_ext_wallet_->run().getDetails()));

    // ================== Deploying Flex wrapper for Funtics ================== //
    co_await funtics_flex_wrapper_->deploy(funtics_wrapper_init, 1.5_T).init(funtics_wrapper_ext_wallet_->get());
    co_await printf("[Test] FUNTICS Wrapper deployed: {address}", funtics_flex_wrapper_->get());
    co_await printf("[Test] FUNTICS Wrapper.setInternalWalletCode");
    co_await (*funtics_flex_wrapper_)(0.5_T).setInternalWalletCode(flex_wallet_code_.get());
    ASSERT(co_await funtics_flex_wrapper_->run().hasInternalWalletCode(), "[ERROR] FUNTICS Wrapper is not initialized, exiting...");

    // ======================== Deploying Flex root ======================== //
    // address notify_addr = co_await cout().inputAddress("Address for AMM notifications:", "AMM");
    address notify_addr = address::make_std(0_i8, uint256(0x48e6891227df6a7e29e342e5ebced85ccefec9d0f842031c922a38c691d61af9));
    TonsConfig tons_cfg {
      .transfer_tip3 = 0.2_UT,
      .return_ownership = 0.2_UT,
      .trading_pair_deploy = 1_UT,
      .order_answer = 0.1_UT,
      .process_queue = 0.4_UT,
      .send_notify = 0.1_UT
    };
    auto flex_deployer_pubkey = co_await cout().genkey();
    flex_ = deployFlex(flex_code, tons_cfg, flex_deployer_pubkey, 10_u8);
    co_await printf("[Test] Flex deploying: {address}", flex_->get());
    co_await printf("[Test] Flex deployed: {address}", flex_->get());
    co_await printf("[Test] Flex.setPairCode");
    co_await flex_->debot_ext_in(flex_deployer_pubkey).setPairCode(pair_code);
    co_await printf("[Test] Flex.setXchgPairCode");
    co_await flex_->debot_ext_in(flex_deployer_pubkey).setXchgPairCode(xchg_pair_code);
    co_await printf("[Test] Flex.setPriceCode");
    co_await flex_->debot_ext_in(flex_deployer_pubkey).setPriceCode(price_code);
    co_await printf("[Test] Flex.setXchgPriceCode");
    co_await flex_->debot_ext_in(flex_deployer_pubkey).setXchgPriceCode(xchg_price_code);

    ASSERT(co_await flex_->run().isFullyInitialized(), "[ERROR] Flex is not initialized, exiting...");

    // ============= Deploying Nuka external wallet for client1 ============ //
    auto nuka1_pubkey = co_await cout().genkey();
    co_await printf("[Test] Nuka1 pubkey: {uint256}", nuka1_pubkey);
    nuka1_ext_wallet_ = deployWallet(nuka_name, nuka_symbol, nuka_decimals,
      nuka_root_pubkey, nuka1_pubkey, nuka_root_->get(), *client1_addr_, 0_i8);
    co_await printf("[Test] Nuka1 ext wallet deploying: {address}", nuka1_ext_wallet_->get());
    co_await printf("[Test] Nuka1 ext wallet deployed: {address}", nuka1_ext_wallet_->get());
    PRINT_TIP3_DETAILS((co_await nuka1_ext_wallet_->run().getDetails()));

    co_await printf("[Test] granting 10000 nuka tokens to nuka1 ext wallet...");
    co_await nuka_root_->tail_call<bool_t>(nuka1_ext_wallet_->get(), 0.5_T).grant(nuka1_ext_wallet_->get(), 10000_u128, 0_UT);
    PRINT_TIP3_DETAILS((co_await nuka1_ext_wallet_->run().getDetails()));

    // ============ Converting external Nuka tokens to internal ============ //
    auto flex_nuka1_pubkey = co_await cout().genkey();
    co_await printf("[Test] Now testing Nuka external->internal conversion");
    cell payload1 = build(FlexDeployWalletArgs{flex_nuka1_pubkey, *client1_addr_, 1_UT}).endc();
    auto ret1 = co_await nuka1_ext_wallet_->tail_call<WrapperRet>(nuka_flex_wrapper_->get(), 2_T).
      transferWithNotify(
        *client1_addr_, nuka_wrapper_ext_wallet_->get(), 5000_u128, 0_u128, bool_t{false}, payload1
      );
    co_await printf("[Test] Wrapper answer: ( err_code: {uint32}, flex_wallet: {address} )", ret1.err_code, ret1.flex_wallet);
    flex_nuka1_wallet_ = ret1.flex_wallet;
    co_await printf("[Test] FLEX nuka wallet1: {address}", flex_nuka1_wallet_->get());
    auto nuka_intern_details = co_await flex_nuka1_wallet_->run().getDetails();
    PRINT_TIP3_DETAILS(nuka_intern_details);
    ASSERT(nuka_intern_details.balance == 5000, "[ERROR] Incorrect nuka internal balance, exiting...");
    ASSERT((co_await nuka1_ext_wallet_->run().getDetails()).balance == 5000, "[ERROR] Incorrect nuka remaining ext balance, exiting...");

    // ======== Deploying empty internal Funtics wallet for client1 ======== //
    auto flex_funtics1_pubkey = co_await cout().genkey();
    // Testing deploy using wrapper method call
    flex_funtics1_wallet_ = co_await (*funtics_flex_wrapper_)(1.5_T).deployEmptyWallet(flex_funtics1_pubkey, *client1_addr_, 1_UT);
    co_await printf("[Test] FLEX funtics wallet1: {address}", flex_funtics1_wallet_->get());

    // ============ Deploying Funtics external wallet for client2 ========== //
    auto funtics2_pubkey = co_await cout().genkey();
    co_await printf("[Test] Funtics2 pubkey: {uint256}", funtics2_pubkey);
    funtics2_ext_wallet_ = deployWallet(funtics_name, funtics_symbol, funtics_decimals,
      funtics_root_pubkey, funtics2_pubkey, funtics_root_->get(), *client1_addr_, 0_i8);
    co_await printf("[Test] Funtics2 ext wallet deploying: {address}", funtics2_ext_wallet_->get());
    co_await printf("[Test] Funtics2 ext wallet deployed: {address}", funtics2_ext_wallet_->get());
    PRINT_TIP3_DETAILS((co_await funtics2_ext_wallet_->run().getDetails()));

    co_await printf("[Test] granting 70000 funtics tokens to funtics2 ext wallet...");
    co_await funtics_root_->tail_call<bool_t>(funtics2_ext_wallet_->get(), 0.5_T).grant(funtics2_ext_wallet_->get(), 70000_u128, 0_UT);
    PRINT_TIP3_DETAILS((co_await funtics2_ext_wallet_->run().getDetails()));

    // =========== Converting external Funtics tokens to internal ========== //
    auto flex_funtics2_pubkey = co_await cout().genkey();
    co_await printf("[Test] Now testing Funtics external->internal conversion");
    cell payload2 = build(FlexDeployWalletArgs{flex_funtics2_pubkey, *client1_addr_, 1_UT}).endc();
    auto ret2 = co_await funtics2_ext_wallet_->tail_call<WrapperRet>(funtics_flex_wrapper_->get(), 2_T).
      transferWithNotify(
        *client1_addr_, funtics_wrapper_ext_wallet_->get(), 50000_u128, 0_u128, bool_t{false}, payload2
      );
    co_await printf("[Test] Wrapper answer: ( err_code: {uint32}, flex_wallet: {address} )", ret2.err_code, ret2.flex_wallet);
    flex_funtics2_wallet_ = ret2.flex_wallet;
    co_await printf("[Test] FLEX funtics wallet2: {address}", flex_funtics2_wallet_->get());
    auto funtics_intern_details = co_await flex_funtics2_wallet_->run().getDetails();
    PRINT_TIP3_DETAILS(funtics_intern_details);
    ASSERT(funtics_intern_details.balance == 50000, "[ERROR] Incorrect funtics internal balance, exiting...");
    ASSERT((co_await funtics2_ext_wallet_->run().getDetails()).balance == 20000,
      "[ERROR] Incorrect funtics remaining ext balance, exiting...");

    // ======== Deploying empty internal Nuka wallet for client2 ======== //
    auto flex_nuka2_pubkey = co_await cout().genkey();
    // Testing deploy using wrapper method call
    flex_nuka2_wallet_ = co_await (*nuka_flex_wrapper_)(1.5_T).deployEmptyWallet(flex_nuka2_pubkey, *client1_addr_, 1_UT);
    co_await printf("[Test] FLEX nuka wallet2: {address}", flex_nuka2_wallet_->get());

    // ============ Check & Deploy XCHG Pair ============ //

    auto tip3info_major = co_await flex_nuka1_wallet_->run().getDetails();
    auto tip3info_minor = co_await flex_funtics1_wallet_->run().getDetails();

    auto major_root = nuka_flex_wrapper_->get();
    auto minor_root = funtics_flex_wrapper_->get();
    nuka_fun_pair_ = IXchgPairPtr(co_await flex_->run().getXchgTradingPair(major_root, minor_root));
    co_await printf("[Test] Xchg Pair is {address}", nuka_fun_pair_->get());
    TonsConfig tonsCfg = co_await flex_->run().getTonsCfg();
    cell nuka_fun_price_code = co_await flex_->run().getXchgPriceCode(major_root, minor_root);

    cell flex_xchg_pair_code = co_await flex_->run().getXchgPairCode();
    DXchgPair pair_data {
      .flex_addr_ = flex_->get(),
      .tip3_major_root_ = nuka_flex_wrapper_->get(),
      .tip3_minor_root_ = funtics_flex_wrapper_->get()
    };
    auto [pair_init, pair_std_addr] =
      prepare_xchg_pair_state_init_and_addr(pair_data, flex_xchg_pair_code);
    auto pair_addr = address::make_std(0_i8, pair_std_addr);
    ASSERT(pair_addr == nuka_fun_pair_->get(), "[ERROR] Different trade pair addresses");
    if (1 != co_await cout().getAccountType(nuka_fun_pair_->get())) {
      co_await printf("[Test] Xchg Pair is not yet exists and need to be deployed");
      auto min_amount = 1_u128;
      co_await nuka_fun_pair_->deploy(pair_init, 2_T).onDeploy(min_amount, tonsCfg.trading_pair_deploy, notify_addr);
      co_await printf("[Test] Xchg pair deployed: {address}", nuka_fun_pair_->get());
    }

    // === Sell order flex_nuka1_wallet:flex_funtics1_wallet === //
    auto min_amount = co_await nuka_fun_pair_->run().getMinAmount();
    auto deals_limit = co_await flex_->run().getDealsLimit();

    Tip3Config tip3_cfg_major {
      .name = tip3info_major.name,
      .symbol = tip3info_major.symbol,
      .decimals = tip3info_major.decimals,
      .root_public_key = tip3info_major.root_public_key,
      .root_address = tip3info_major.root_address
    };
    Tip3Config tip3_cfg_minor {
      .name = tip3info_minor.name,
      .symbol = tip3info_minor.symbol,
      .decimals = tip3info_minor.decimals,
      .root_public_key = tip3info_minor.root_public_key,
      .root_address = tip3info_minor.root_address
    };

    auto price = 72.20_UT;
    auto amount = 100_u128;
    auto minor_amount = uint128{__builtin_tvm_muldivr(amount.get(), price.get(), one_full_ton_size)};
    ASSERT(minor_amount.get() >> 128 == 0, "Too big minor amount (>128 bit)");
    co_await printf("[Test] Major amount: {uint128}, Minor amount: {uint128}", amount, minor_amount);

    DPriceXchg price_data {
      .price_ = RationalPrice{uint128{price.get()}, uint128{one_full_ton_size}},
      .sells_amount_ = 0_u128,
      .buys_amount_ = 0_u128,
      .flex_ = flex_->get(),
      .min_amount_ = min_amount,
      .deals_limit_ = deals_limit,
      .notify_addr_ = notify_addr,
      .workchain_id_ = 0_i8,
      .tons_cfg_ = tonsCfg,
      .tip3_code_ = tip3info_major.code,
      .major_tip3cfg_ = tip3_cfg_major,
      .minor_tip3cfg_ = tip3_cfg_minor,
      .sells_ = {},
      .buys_ = {}
    };
    auto [price_init, price_std_addr] = prepare_price_xchg_state_init_and_addr(price_data, nuka_fun_price_code);
    price_ptr_ = IPriceXchgPtr(address::make_std(0_i8, price_std_addr));
    co_await printf("[Test] price_addr: {address}", price_ptr_->get());

    cell deploy_init_cl = build(price_init).endc();
    unsigned hours = 1;
    auto grams = tonsCfg.process_queue + tonsCfg.transfer_tip3 + tonsCfg.send_notify +
        tonsCfg.return_ownership + tonsCfg.order_answer + one_full_ton_size;
    {
      PayloadArgs sell_args = {
        .sell = bool_t{true},
        .amount = amount,
        .receive_tip3_wallet = flex_funtics1_wallet_->get(),
        .client_addr = *client1_addr_
      };
      cell sell_payload = build(sell_args).endc();
      uint32 cur_time(tvm_now());
      uint32 lend_finish_time(tvm_now() + hours * 60 * 60);
      co_await printf("[Test] The order will ends at {datetime}", lend_finish_time);

      auto ret3 = co_await flex_nuka1_wallet_->tail_call<OrderRet>(price_ptr_->get(), Grams(grams.get())).
        lendOwnership(*client1_addr_, 0_u128, std::get<addr_std>(price_ptr_->get().val()).address, amount,
                      lend_finish_time, deploy_init_cl, sell_payload);
      co_await printf("[Test] SELL err_code: {uint32}", ret3.err_code);
      co_await printf("[Test] SELL processed: {uint128}", ret3.processed);
      co_await printf("[Test] SELL enqueued: {uint128}", ret3.enqueued);

      ASSERT(ret3.err_code == 0, "[ERROR] [SELL] Can't deploy order");
      ASSERT(ret3.enqueued == 100, "[ERROR] [SELL] Wrong 'enqueued' returned");
      ASSERT(ret3.processed == 0, "[ERROR] [SELL] Wrong 'processed' returned");
    }
    co_await printf("=== NUKA1 WALLET after sell order enqueued:");
    PRINT_TIP3_DETAILS((co_await flex_nuka1_wallet_->run().getDetails()));

    // === Buy order flex_funtics2_wallet:flex_nuka2_wallet === //
    {
      PayloadArgs buy_args = {
        .sell = bool_t{false},
        .amount = amount,
        .receive_tip3_wallet = flex_nuka2_wallet_->get(),
        .client_addr = *client1_addr_
      };
      cell buy_payload = build(buy_args).endc();
      uint32 cur_time(tvm_now());
      uint32 lend_finish_time(tvm_now() + hours * 60 * 60);
      co_await printf("[Test] The order will ends at {datetime}", lend_finish_time);

      auto ret4 = co_await flex_funtics2_wallet_->tail_call<OrderRet>(price_ptr_->get(), Grams(grams.get())).
        lendOwnership(*client1_addr_, 0_u128, std::get<addr_std>(price_ptr_->get().val()).address, minor_amount,
                      lend_finish_time, deploy_init_cl, buy_payload);
      co_await printf("[Test] BUY err_code: {uint32}", ret4.err_code);
      co_await printf("[Test] BUY processed: {uint128}", ret4.processed);
      co_await printf("[Test] BUY enqueued: {uint128}", ret4.enqueued);

      ASSERT(ret4.err_code == 0, "[ERROR] [BUY] Can't deploy order");
      ASSERT(ret4.enqueued == 0, "[ERROR] [BUY] Wrong 'enqueued' returned");
      ASSERT(ret4.processed == 100, "[ERROR] [BUY] Wrong 'processed' returned");
    }
    co_await printf("=== NUKA1 WALLET after deal processed:");
    PRINT_TIP3_DETAILS((co_await flex_nuka1_wallet_->run().getDetails()));
    co_await printf("=== NUKA2 WALLET after deal processed:");
    PRINT_TIP3_DETAILS((co_await flex_nuka2_wallet_->run().getDetails()));

    co_await printf("=== FUNTICS1 WALLET after deal processed:");
    PRINT_TIP3_DETAILS((co_await flex_funtics1_wallet_->run().getDetails()));
    co_await printf("=== FUNTICS2 WALLET after deal processed:");
    PRINT_TIP3_DETAILS((co_await flex_funtics2_wallet_->run().getDetails()));

    ASSERT((co_await flex_nuka1_wallet_->run().getDetails()).balance == 5000 - 100,
      "[ERROR] Wrong nuka1_wallet balance after deal");
    ASSERT((co_await flex_nuka2_wallet_->run().getDetails()).balance == 100,
      "[ERROR] Wrong nuka2_wallet balance after deal");
    ASSERT((co_await flex_funtics1_wallet_->run().getDetails()).balance == 7220,
      "[ERROR] Wrong funtics1_wallet balance after deal");
    ASSERT((co_await flex_funtics2_wallet_->run().getDetails()).balance == 50000 - 7220,
      "[ERROR] Wrong funtics2_wallet balance after deal");

    co_await printf("[Test] Processing burn operations (internal->external)...");
    unsigned answer_id_v = temporary_data::getglob(global_id::answer_id);
    temporary_data::setglob(global_id::answer_id, 1ul << 32);
    (*flex_nuka1_wallet_)(1_T).burn(nuka1_pubkey, *client1_addr_);
    temporary_data::setglob(global_id::answer_id, 1ul << 32);
    (*flex_funtics2_wallet_)(1_T).burn(funtics2_pubkey, *client1_addr_);
    temporary_data::setglob(global_id::answer_id, answer_id_v);
    auto funtics1_pubkey = co_await cout().genkey();
    auto nuka2_pubkey = co_await cout().genkey();

    unsigned answer_id_v2 = temporary_data::getglob(global_id::answer_id);
    temporary_data::setglob(global_id::answer_id, 1ul << 32);
    (*flex_funtics1_wallet_)(1_T).burn(funtics1_pubkey, *client1_addr_);
    temporary_data::setglob(global_id::answer_id, 1ul << 32);
    (*flex_nuka2_wallet_)(1_T).burn(nuka2_pubkey, *client1_addr_);
    temporary_data::setglob(global_id::answer_id, answer_id_v2);

    co_await printf("[Test] Burn processed");

    nuka2_ext_wallet_ = ITONTokenWalletPtr(co_await nuka_root_->run().getWalletAddress(nuka2_pubkey, *client1_addr_));
    funtics1_ext_wallet_ = ITONTokenWalletPtr(co_await funtics_root_->run().getWalletAddress(funtics1_pubkey, *client1_addr_));

    co_await printf("=== NUKA1 EXT WALLET after deal processed:");
    PRINT_TIP3_DETAILS((co_await nuka1_ext_wallet_->run().getDetails()));
    co_await printf("=== NUKA2 EXT WALLET after deal processed:");
    PRINT_TIP3_DETAILS((co_await nuka2_ext_wallet_->run().getDetails()));

    co_await printf("=== FUNTICS1 EXT WALLET after deal processed:");
    PRINT_TIP3_DETAILS((co_await funtics1_ext_wallet_->run().getDetails()));
    co_await printf("=== FUNTICS2 EXT WALLET after deal processed:");
    PRINT_TIP3_DETAILS((co_await funtics2_ext_wallet_->run().getDetails()));

    ASSERT((co_await nuka1_ext_wallet_->run().getDetails()).balance == 10000 - 100,
      "[ERROR] Wrong ext nuka1_wallet balance after deal");
    ASSERT((co_await nuka2_ext_wallet_->run().getDetails()).balance == 100,
      "[ERROR] Wrong ext nuka2_wallet balance after deal");
    ASSERT((co_await funtics1_ext_wallet_->run().getDetails()).balance == 7220,
      "[ERROR] Wrong ext funtics1_wallet balance after deal");
    ASSERT((co_await funtics2_ext_wallet_->run().getDetails()).balance == 70000 - 7220,
      "[ERROR] Wrong ext funtics2_wallet balance after deal");

    co_await printf("[Test] all tests completed");

    co_return;
  }
  DEFAULT_SUPPORT_FUNCTIONS(ITip3Deploy, void)

  __always_inline
  std::pair<IWrapperPtr, StateInit> prepareDeployWrapper(string name, string symbol, uint8 decimals, uint256 wrapper_pubkey) {
    DWrapper wrapper_data {
      name, symbol, decimals, 0_i8,
      wrapper_pubkey, 0_u128,
      {}, *client1_addr_, 1_T, {}
    };
    auto [wrapper_init, hash_addr] = prepare_wrapper_state_init_and_addr(flex_wrapper_code_.get(), wrapper_data);
    IWrapperPtr wrapper_addr(address::make_std(0_i8, hash_addr));
    return { wrapper_addr, wrapper_init };
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
      .wallet_code_ = {},
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
    auto [wallet_init, hash_addr] = prepare_external_wallet_state_init_and_addr(
      name, symbol, decimals,
      root_pubkey, wallet_pubkey, root_address,
      owner_addr, ext_wallet_code_.get(), workchain_id);
    ITONTokenWalletPtr wallet_addr(address::make_std(workchain_id, hash_addr));
    wallet_addr.deploy_noop(wallet_init, 1_T);
    return wallet_addr;
  }

  __always_inline
  IFlexPtr deployFlex(
    cell flex_code, TonsConfig tons_cfg, uint256 deployer_pubkey,
    uint8 deals_limit
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
    IFlexPtr flex_addr(address::make_std(0_i8, hash_addr));
    flex_addr.deploy_noop(flex_init, 1_T);
    return flex_addr;
  }

  // default processing of unknown messages
  __always_inline static int _fallback(cell msg, slice msg_body) {
    return 0;
  }
};

DEFINE_JSON_ABI(ITip3Deploy, DTip3Deploy, ETip3Deploy);

// ----------------------------- Main entry functions ---------------------- //
MAIN_ENTRY_FUNCTIONS_NO_REPLAY(Tip3Deploy, ITip3Deploy, DTip3Deploy)


