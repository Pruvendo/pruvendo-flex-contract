#include "stTONs.hpp"
#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>
<<<<<<< HEAD
=======
#include <tvm/suffixes.hpp>
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055

#include "DePool.hpp"

using namespace tvm;
using namespace schema;

<<<<<<< HEAD
=======
enum class DePoolError {
  STATUS_SUCCESS                           = 0,
  STATUS_DEPOOL_CLOSED                     = 3,
  STATUS_NO_PARTICIPANT                    = 6,
  STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL = 16,
  STATUS_TRANSFER_AMOUNT_IS_TOO_BIG        = 18,
  STATUS_TRANSFER_SELF                     = 19,
  STATUS_TRANSFER_TO_OR_FROM_VALIDATOR     = 20,
  STATUS_INVALID_ADDRESS                   = 22,
  STATUS_TRANSFER_WHILE_COMPLETING_STEP    = 26,
  STATUS_NOT_REPORTED_YET                  = 0xFF
};

>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
template<bool Internal>
class stTONs final : public smart_interface<IstTONs>, public DstTONs {
public:
  struct error_code : tvm::error_code {
<<<<<<< HEAD
    static constexpr unsigned sender_is_not_my_owner        = 100;
    static constexpr unsigned crystalls_inconsistency       = 101;
    static constexpr unsigned not_enough_crystalls          = 102;
    static constexpr unsigned store_crystalls_first         = 103;
    static constexpr unsigned small_tokens_value            = 104;
    static constexpr unsigned not_good_wallet               = 105;
    static constexpr unsigned too_big_amount_to_return_back = 106;
  };

  __always_inline
  void constructor(
    uint256 owner_pubkey,
    Tip3Config tip3cfg,
    address depool,
    stTONsCosts costs,
    cell tip3code
  ) {
    require(costs.receive_stake_transfer_costs >
              costs.store_crystals_costs + costs.mint_costs + costs.deploy_wallet_costs,
            error_code::crystalls_inconsistency);

    owner_pubkey_ = owner_pubkey;
    tip3cfg_ = tip3cfg;
    depool_ = depool;
    costs_ = costs;
    tip3code_ = tip3code;
    workchain_id_ = std::get<addr_std>(address{tvm_myaddr()}.val()).workchain_id;
  }

  __always_inline
  IRootTokenContractPtr tip3root() const { return IRootTokenContractPtr(tip3cfg_.root_address); }

  __always_inline
  void storeCrystalls(address client_addr) {
    require(int_value().get() > costs_.receive_stake_transfer_costs, error_code::not_enough_crystalls);

    auto std_addr = std::get<addr_std>(client_addr.val()).address;
    if (auto opt_exist = stored_crystals_.lookup(std_addr.get()))
      stored_crystals_.set_at(std_addr.get(), *opt_exist + int_value().get() - costs_.store_crystals_costs);
    else
      stored_crystals_.set_at(std_addr.get(), int_value().get() - costs_.store_crystals_costs);
=======
    static constexpr unsigned sender_is_not_my_owner               = 100;
    static constexpr unsigned transferring_stake_back              = 101;
    static constexpr unsigned not_transferred_stake_back           = 102;
    static constexpr unsigned not_enough_balance                   = 103;
    static constexpr unsigned finish_time_must_be_greater_than_now = 104;
    static constexpr unsigned internal_owner_enabled               = 105;
    static constexpr unsigned internal_owner_disabled              = 106;
    static constexpr unsigned wallet_in_lend_owneship              = 107;
    static constexpr unsigned incorrect_depool_address             = 108;
    static constexpr unsigned has_depool_error                     = 109;
    static constexpr unsigned only_original_owner_allowed          = 110;
  };

  __always_inline
  void onDeploy() {
  }

  __always_inline
  void lendOwnership(
    address answer_addr,
    uint128 grams,
    address dest,
    uint128 lend_balance,
    uint32  lend_finish_time,
    cell    deploy_init_cl,
    cell    payload
  ) {
    require(!transferring_stake_back_.get(), error_code::transferring_stake_back);
    auto allowed_balance = check_owner(/*original_owner_only*/true, /*allowed_for_original_owner_in_lend_state*/true);
    // Current allocated lend balance plus new lend balance LEQ all wallet balance
    require(lend_balance > 0 && lend_balance <= allowed_balance, error_code::not_enough_balance);
    require(lend_finish_time > tvm_now(), error_code::finish_time_must_be_greater_than_now);
    tvm_accept();

    auto answer_addr_fxd = fixup_answer_addr(answer_addr);

    // repeated lend to the same address will be { sumX + sumY, max(timeX, timeY) }
    auto sum_lend_balance = lend_balance;
    auto sum_lend_finish_time = lend_finish_time;
    if (auto existing_lend = lend_ownership_.lookup(dest)) {
      sum_lend_balance += existing_lend->lend_balance;
      sum_lend_finish_time = std::max(lend_finish_time, existing_lend->lend_finish_time);
    }

    lend_ownership_.set_at(dest, {sum_lend_balance, sum_lend_finish_time});

    unsigned msg_flags = prepare_transfer_message_flags(grams);
    auto deploy_init_sl = deploy_init_cl.ctos();
    StateInit deploy_init;
    if (!deploy_init_sl.empty())
      deploy_init = parse<StateInit>(deploy_init_cl.ctos());
    if (deploy_init.code && deploy_init.data) {
      // performing `tail call` - requesting dest to answer to our caller
      temporary_data::setglob(global_id::answer_id, return_func_id()->get());
      IstTONsNotifyPtr(dest).deploy(deploy_init, Grams(grams.get()), msg_flags).
        onLendOwnership(answer_addr_fxd, lend_balance, lend_finish_time,
                        owner_pubkey_, owner_address_, depool_.get(), depool_pubkey_, payload);
    } else {
      // performing `tail call` - requesting dest to answer to our caller
      temporary_data::setglob(global_id::answer_id, return_func_id()->get());
      IstTONsNotifyPtr(dest)(Grams(grams.get()), msg_flags).
        onLendOwnership(answer_addr_fxd, lend_balance, lend_finish_time,
                        owner_pubkey_, owner_address_, depool_.get(), depool_pubkey_, payload);
    }
  }

  __always_inline
  void returnOwnership(uint128 tokens) {
    check_owner(/*original_owner_only*/false, /*allowed_for_original_owner_in_lend_state*/false);
    auto sender = int_sender();
    auto v = lend_ownership_[sender];
    if (v.lend_balance <= tokens) {
      lend_ownership_.erase(sender);
    } else {
      v.lend_balance -= tokens;
      lend_ownership_.set_at(sender, v);
    }
  }

  __always_inline
  void returnStake(address dst, uint128 processing_crystals) {
    check_owner(/*original_owner_only*/true, /*allowed_for_original_owner_in_lend_state*/false);
    depool_(Grams(processing_crystals.get())).transferStake(dst, 0u64);
    transferring_stake_back_ = true;
    last_depool_error_ = static_cast<unsigned>(DePoolError::STATUS_NOT_REPORTED_YET);
  }

  __always_inline
  void finalize(address dst, bool_t ignore_errors) {
    require(transferring_stake_back_.get(), error_code::not_transferred_stake_back);
    check_owner(/*original_owner_only*/true, /*allowed_for_original_owner_in_lend_state*/false);
    tvm_accept();
    require(ignore_errors ||
      (last_depool_error_ == static_cast<unsigned>(DePoolError::STATUS_SUCCESS)) ||
      (last_depool_error_ == static_cast<unsigned>(DePoolError::STATUS_DEPOOL_CLOSED)) ||
      (last_depool_error_ == static_cast<unsigned>(DePoolError::STATUS_NO_PARTICIPANT)),
      error_code::has_depool_error);
    suicide(dst);
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
  }

  __always_inline
  void receiveStakeTransfer(address source, uint128 amount) {
<<<<<<< HEAD
    // transferStake has uint64 amount argument, so we will not be able to return back stakes > (1 << 64)
    require((amount >> 64) == 0, error_code::too_big_amount_to_return_back);
    auto std_addr = std::get<addr_std>(source.val()).address;
    auto opt_account = stored_crystals_.extract(std_addr.get());
    require(!!opt_account, error_code::store_crystalls_first);
    tvm_accept();

    tip3root()(Grams(costs_.mint_costs.get())).mint(amount);

    auto rest_crystals = *opt_account - costs_.process_receive_stake_costs - costs_.mint_costs;
    tip3root()(Grams(rest_crystals.get())).
      deployWallet(uint256(0), source, amount, rest_crystals - costs_.deploy_wallet_costs);
  }

  __always_inline
  void internalTransfer(
    uint128 tokens,
    address answer_addr,
    uint256 sender_pubkey,
    address sender_owner,
    bool_t  notify_receiver,
    cell    payload
  ) {
    require(tokens >= costs_.min_transfer_tokens, error_code::small_tokens_value);

    uint256 expected_address = expected_sender_address(sender_pubkey, sender_owner);
    auto [sender, value_gr] = int_sender_and_value();
    require(std::get<addr_std>(sender()).address == expected_address,
            error_code::not_good_wallet);

    depool_(Grams(costs_.transfer_stake_costs.get())).transferStake(sender_owner, uint64(tokens.get()));
=======
    require(int_sender() == depool_.get(), error_code::incorrect_depool_address);
    tvm_accept();

    balance_ += amount;
  }

  __always_inline
  void receiveAnswer(uint32 errcode, uint64 comment) {
    require(int_sender() == depool_.get(), error_code::incorrect_depool_address);
    tvm_accept();

    last_depool_error_ = uint8(errcode.get());
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
  }

  __always_inline
  stTONsDetails getDetails() {
<<<<<<< HEAD
    return {
      owner_pubkey_,
      owner_address_,
      tip3root().get(),
      depool_.get(),
      getStoredCrystals(),
      costs_
=======
    auto [filtered_lend_array, lend_balance] = filter_lend_ownerhip_array();
    return {
      owner_pubkey_,
      owner_address_,
      depool_.get(),
      depool_pubkey_,
      balance_,
      filtered_lend_array,
      lend_balance,
      transferring_stake_back_,
      last_depool_error_
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
      };
  }

  __always_inline
<<<<<<< HEAD
  dict_array<StoredCrystalsPair> getStoredCrystals() const {
    dict_array<StoredCrystalsPair> rv;
    for (auto v : stored_crystals_) {
      rv.push_back({v.first, v.second});
    }
    return rv;
  }

  __always_inline
  void check_owner() {
    bool internal_ownership = !!owner_address_;
    if constexpr (Internal)
      require(internal_ownership && (int_sender() == *owner_address_), error_code::sender_is_not_my_owner);
    else
      require(!internal_ownership && (msg_pubkey() == owner_pubkey_), error_code::sender_is_not_my_owner);
  }

  // transform x:0000...0000 address into empty optional<address>
  __always_inline
  std::optional<address> optional_owner(address owner) {
    return std::get<addr_std>(owner()).address ?
      std::optional<address>(owner) : std::optional<address>();
  }

  __always_inline
  std::pair<StateInit, uint256> calc_wallet_init_hash(uint256 pubkey, address internal_owner) {
    return prepare_internal_wallet_state_init_and_addr(
      tip3cfg_.name, tip3cfg_.symbol, tip3cfg_.decimals, tip3cfg_.root_public_key, pubkey, tip3cfg_.root_address,
      optional_owner(internal_owner), tip3code_, workchain_id_);
  }

  __always_inline
  uint256 expected_sender_address(uint256 sender_public_key, address sender_owner) {
    return calc_wallet_init_hash(sender_public_key, sender_owner).second;
=======
  address calcStTONsAddr(
    cell code,
    uint256 owner_pubkey,
    std::optional<address> owner_address,
    address depool
  ) {
    DstTONs data {
      .owner_pubkey_ = owner_pubkey,
      .owner_address_ = owner_address,
      .depool_ = depool,
      .balance_ = 0u128,
      .lend_ownership_ = {},
      .transferring_stake_back_ = bool_t{false},
      .last_depool_error_ = 0u8
    };
    auto [init, hash] = prepare_sttons_state_init_and_addr(data, code);
    auto workchain_id = std::get<addr_std>(address{tvm_myaddr()}.val()).workchain_id;
    return address::make_std(workchain_id, hash);
  }

  __always_inline bool is_internal_owner() const { return owner_address_.has_value(); }

  // original_owner_only - methods only allowed to call by original owner (no lend)
  // allowed_for_original_owner_in_lend_state - methods allowed to call by original owner in lend state
  __always_inline
  uint128 check_internal_owner(bool original_owner_only, bool allowed_for_original_owner_in_lend_state) {
    auto [filtered_map, actual_lend_balance] = filter_lend_ownerhip_map();
    if (actual_lend_balance > 0) {
      if (allowed_for_original_owner_in_lend_state) {
        require(is_internal_owner(), error_code::internal_owner_disabled);
        if (*owner_address_ == int_sender())
          return balance_ - actual_lend_balance;
      }
      require(!original_owner_only, error_code::only_original_owner_allowed);
      auto elem = filtered_map.lookup(int_sender());
      require(!!elem, error_code::sender_is_not_my_owner);
      return std::min(balance_, elem->lend_balance);
    } else {
      require(is_internal_owner(), error_code::internal_owner_disabled);
      require(*owner_address_ == int_sender(),
              error_code::sender_is_not_my_owner);
      return balance_;
    }
  }

  __always_inline
  uint128 check_external_owner() {
    require(!is_internal_owner(), error_code::internal_owner_enabled);
    require(msg_pubkey() == owner_pubkey_, error_code::sender_is_not_my_owner);
    tvm_accept();
    auto [filtered_map, lend_balance] = filter_lend_ownerhip_map();
    require(filtered_map.empty(), error_code::wallet_in_lend_owneship);
    return balance_;
  }

  __always_inline
  uint128 check_owner(bool original_owner_only, bool allowed_in_lend_state) {
    if constexpr (Internal)
      return check_internal_owner(original_owner_only, allowed_in_lend_state);
    else
      return check_external_owner();
  }

  __always_inline
  unsigned prepare_transfer_message_flags(uint128 &grams) {
    unsigned msg_flags = 0;
    if constexpr (Internal) {
      tvm_rawreserve(tvm_balance() - int_value().get(), rawreserve_flag::up_to);
      msg_flags = SEND_ALL_GAS;
      grams = 0;
    }
    return msg_flags;
  }

  // If zero answer_addr is specified, it is corrected to incoming sender (for internal message),
  // or this contract address (for external message)
  __always_inline
  address fixup_answer_addr(address answer_addr) {
    if (std::get<addr_std>(answer_addr()).address == 0) {
      if constexpr (Internal)
        return address{int_sender()};
      else
        return address{tvm_myaddr()};
    }
    return answer_addr;
  }

  // Filter lend ownership map to keep only actual (unexpired) records and common lend balance
  __always_inline
  std::pair<lend_ownership_map, uint128> filter_lend_ownerhip_map() {
    if (lend_ownership_.empty())
      return {};
    auto now_v = tvm_now();
    lend_ownership_map rv;
    uint128 lend_balance;
    for (auto v : lend_ownership_) {
      if (now_v < v.second.lend_finish_time) {
        rv.insert(v);
        lend_balance += v.second.lend_balance;
      }
    }
    lend_ownership_ = rv;
    return { rv, lend_balance };
  }

  __always_inline
  std::pair<lend_ownership_array, uint128> filter_lend_ownerhip_array() {
    if (lend_ownership_.empty())
      return {};
    auto now_v = tvm_now();
    lend_ownership_array rv;
    uint128 lend_balance;
    for (auto v : lend_ownership_) {
      if (now_v < v.second.lend_finish_time) {
        rv.push_back({v.first, v.second.lend_balance, v.second.lend_finish_time});
        lend_balance += v.second.lend_balance;
      }
    }
    return { rv, lend_balance };
  }

  __always_inline
  address get_owner_addr() {
    return owner_address_ ? *owner_address_ :
                            address::make_std(int8(0), uint256(0));
>>>>>>> deb0dd63c03bbd16d2ebacf8391fb20dfecc8055
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IstTONs, sttons_replay_protection_t)

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }
};

DEFINE_JSON_ABI(IstTONs, DstTONs, EstTONs);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS_TMPL(stTONs, IstTONs, DstTONs, STTONS_TIMESTAMP_DELAY)

