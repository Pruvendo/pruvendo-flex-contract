#include "TONTokenWallet.hpp"
#include "RootTokenContract.hpp"

#include <tvm/contract.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;
using namespace schema;

__interface ITestWalletOwner {
  [[external, dyn_chain_parse]]
  resumable<void>
  constructor(uint256 owner_key, address token_root,
              uint128 votes_price, uint128 grams, uint128 gramsToWallet);

  [[external, noaccept]]
  resumable<void>
  buyVotes(uint128 grams);

  // === getters ===

  [[getter]]
  uint256 getOwnerKey();

  [[getter]]
  address getTokenRoot();

  [[getter]]
  address getMyWallet();

  [[getter]]
  uint128 getVotesPrice();

  [[getter]]
  uint128 getVotes();
};

struct DTestWalletOwner {
  uint128 votes_price_;
  uint128 votes_;
  uint256 owner_key_;
  address token_root_;
  std::optional<address> my_wallet_;
};

struct ETestWalletOwner {
};

static constexpr unsigned TIMESTAMP_DELAY = 1800;

class TestWalletOwner final : public smart_interface<ITestWalletOwner>, public DTestWalletOwner {
public:
  using replay_protection_t = replay_attack_protection::timestamp<TIMESTAMP_DELAY>;

  struct error_code : tvm::error_code {
    static constexpr unsigned message_sender_is_not_my_owner = 100;
    static constexpr unsigned wrong_wallet_answer            = 101;
    static constexpr unsigned wrong_root_answer              = 102;
  };

  __always_inline
  resumable<void>
  constructor(uint256 owner_key, address token_root, uint128 votes_price, 
              uint128 grams, uint128 gramsToWallet) {
    owner_key_ = owner_key;
    token_root_ = token_root;
    votes_price_ = votes_price;
    votes_ = 0;

    address myaddr{tvm_myaddr()};

    handle<IRootTokenContract> root_handle(token_root_);
    my_wallet_ = co_await root_handle(Grams(grams.get())).
      deployEmptyWallet(uint256{0}, myaddr, gramsToWallet);
  }

  __always_inline
  resumable<void> buyVotes(uint128 grams) {
    require(owner_key_ == msg_pubkey(), error_code::message_sender_is_not_my_owner);
    require(!!my_wallet_, error_code::wrong_wallet_answer);

    tvm_accept();

    handle<ITONTokenWallet> dest_wallet(*my_wallet_);
    uint128 balance = co_await dest_wallet(Grams(grams.get())).
      requestBalance();

    votes_ = balance / votes_price_;
  }

  // getters
  __always_inline
  uint256 getOwnerKey() {
    return owner_key_;
  }

  __always_inline
  address getTokenRoot() {
    return token_root_;
  }

  __always_inline
  address getMyWallet() {
    require(!!my_wallet_, error_code::wrong_wallet_answer);
    return *my_wallet_;
  }

  __always_inline
  uint128 getVotesPrice() {
    return votes_price_;
  }

  __always_inline
  uint128 getVotes() {
    return votes_;
  }

  // ==================== Support methods ====================
  // default processing of unknown messages
  __always_inline static int _fallback(cell msg, slice msg_body) {
    return 0;
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(ITestWalletOwner, replay_protection_t)
};

DEFINE_JSON_ABI(ITestWalletOwner, DTestWalletOwner, ETestWalletOwner);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS(TestWalletOwner, ITestWalletOwner, DTestWalletOwner, TIMESTAMP_DELAY)

