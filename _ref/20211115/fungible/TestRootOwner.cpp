#include "TONTokenWallet.hpp"
#include "RootTokenContract.hpp"

#include <tvm/contract.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

__interface ITestRootOwner {
  [[external]]
  void constructor(uint256 owner_key);

  [[external, noaccept]]
  void set_root_code(cell root_code);

  [[external, noaccept]]
  void set_wallet_code(cell wallet_code);

  [[external, noaccept]]
  void deployRoot(string name, string symbol, uint8 decimals, uint128 crystalsToRoot);

  [[external, noaccept]]
  resumable<address> deployWallet(uint128 processingCrystals,
    uint256 pubkey, address_opt owner, uint128 tokens, uint128 crystals);

  [[external, noaccept]]
  void grant(uint128 processingCrystals, address dest, uint128 tokens, uint128 crystals);

  [[external, noaccept]]
  void mint(uint128 processingCrystals, uint128 tokens);

  // === getters ===

  [[getter]]
  uint256 getOwnerKey();

  [[getter]]
  address getTokenRoot();
};

struct DTestRootOwner {
  uint256 owner_key_;
  handle<IRootTokenContract> token_root_;
  std::optional<cell> root_code_;
  std::optional<cell> wallet_code_;
};

struct ETestRootOwner {
};

static constexpr unsigned TIMESTAMP_DELAY = 1800;

class TestRootOwner final : public smart_interface<ITestRootOwner>, public DTestRootOwner {
public:
  using replay_protection_t = replay_attack_protection::timestamp<TIMESTAMP_DELAY>;

  struct error_code : tvm::error_code {
    static constexpr unsigned message_sender_is_not_my_owner = 100;
    static constexpr unsigned wrong_wallet_answer            = 101;
    static constexpr unsigned wrong_root_answer              = 102;
  };

  __always_inline
  void constructor(uint256 owner_key) {
    owner_key_ = owner_key;
    token_root_ = address::make_std(int8(0), uint256(0));
  }

  __always_inline
  void set_root_code(cell root_code) {
    require(msg_pubkey() == owner_key_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    root_code_ = root_code;
  }

  __always_inline
  void set_wallet_code(cell wallet_code) {
    require(msg_pubkey() == owner_key_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    wallet_code_ = wallet_code;
  }

  __always_inline
  void deployRoot(string name, string symbol, uint8 decimals, uint128 crystalsToRoot) {
    require(msg_pubkey() == owner_key_, error_code::message_sender_is_not_my_owner);
    tvm_accept();
    address myaddr{tvm_myaddr()};
    int8 workchain_id = std::get<addr_std>(myaddr()).workchain_id;
    auto [root_init, dest] = calc_root_init(workchain_id, myaddr, name, symbol, decimals, crystalsToRoot);
    token_root_ = handle<IRootTokenContract>(dest);
    token_root_.deploy(root_init, Crystals(crystalsToRoot.get())).
      mint(uint128{0});
  }

  __always_inline
  resumable<address> deployWallet(uint128 processingCrystals,
                                  uint256 pubkey, address_opt owner,
                                  uint128 tokens, uint128 crystals) {
    require(msg_pubkey() == owner_key_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    address wallet_addr = co_await token_root_(Crystals(processingCrystals.get())).
      deployWallet(pubkey, owner, tokens, crystals);
    co_return wallet_addr;
  }

  __always_inline
  void grant(uint128 processingCrystals, address dest, uint128 tokens, uint128 crystals) {
    require(msg_pubkey() == owner_key_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    token_root_(Crystals(processingCrystals.get())).grant(dest, tokens, crystals);
  }

  __always_inline
  void mint(uint128 processingCrystals, uint128 tokens) {
    require(msg_pubkey() == owner_key_, error_code::message_sender_is_not_my_owner);
    tvm_accept();

    token_root_(Crystals(processingCrystals.get())).mint(tokens);
  }

  // ==================== getters ============================
  __always_inline
  uint256 getOwnerKey() {
    return owner_key_;
  }

  __always_inline
  address getTokenRoot() {
    return token_root_.get();
  }

  // ==================== Support methods ====================
  // default processing of unknown messages
  __always_inline static int _fallback(cell msg, slice msg_body) {
    return 0;
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(ITestRootOwner, replay_protection_t)

private:
  __always_inline
  std::pair<StateInit, address> calc_root_init(int8 workchain_id,
                                               address_opt owner_addr,
                                               string name, string symbol, uint8 decimals,
                                               uint128 crystalsToRoot) {
    DRootTokenContract root_data {
      name, symbol, decimals,
      .root_pubkey_ = uint256{0},
      .root_owner_ = owner_addr,
      .total_supply_ = uint128(0),
      .total_granted_ = uint128(0),
      .wallet_code_ = *wallet_code_
    };
    auto [root_init, dest_addr] = prepare_root_state_init_and_addr(*root_code_, root_data);
    address dest = address::make_std(workchain_id, dest_addr);
    return { root_init, dest };
  }
};

DEFINE_JSON_ABI(ITestRootOwner, DTestRootOwner, ETestRootOwner);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS(TestRootOwner, ITestRootOwner, DTestRootOwner, TIMESTAMP_DELAY)

