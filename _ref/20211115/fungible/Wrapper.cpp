/** \file
 *  \brief Wrapper contract implementation
 *  \author Andrew Zhogin
 *  \copyright 2019-2021 (c) TON LABS
 */

#include "Wrapper.hpp"
#include "TONTokenWallet.hpp"

#include <tvm/contract.hpp>
#include <tvm/smart_switcher.hpp>
#include <tvm/contract_handle.hpp>
#include <tvm/default_support_functions.hpp>

using namespace tvm;

#ifndef TIP3_WALLET_CODE_HASH
#error "Macros TIP3_WALLET_CODE_HASH must be defined (code hash of FlexWallet)"
#endif

#ifndef TIP3_WALLET_CODE_DEPTH
#error "Macros TIP3_WALLET_CODE_DEPTH must be defined (code depth of FlexWallet)"
#endif

template<bool Internal>
class Wrapper final : public smart_interface<IWrapper>, public DWrapper {
public:
  static constexpr bool _checked_deploy = true; /// Deploy is only allowed with [[deploy]] function call
  static constexpr unsigned internal_wallet_hash       = TIP3_WALLET_CODE_HASH;
  static constexpr unsigned internal_wallet_code_depth = TIP3_WALLET_CODE_DEPTH;

  struct error_code : tvm::error_code {
    static constexpr unsigned message_sender_is_not_my_owner    = 100; ///< Authorization error
    static constexpr unsigned wrong_bounced_header              = 101; ///< Wrong header of bounced message
    static constexpr unsigned wrong_bounced_args                = 102; ///< Wrong arguments in bounced message
    static constexpr unsigned internal_owner_enabled            = 103; ///< Internal ownership is enabled (can't process external commands)
    static constexpr unsigned internal_owner_disabled           = 104; ///< Internal ownership is disabled (can't process internal commands)
    static constexpr unsigned wrong_wallet_code_hash            = 105; ///< Wallet code hash is differ from TIP3_WALLET_CODE_HASH macros
    static constexpr unsigned cant_override_wallet_code         = 106; ///< Wallet code is already set and can't be overriden
    static constexpr unsigned not_my_wallet_notifies            = 107; ///< Wallet notification received from wrong address
    static constexpr unsigned burn_unallocated                  = 108; ///< Burn more tokens that was allocated
    static constexpr unsigned message_sender_is_not_good_wallet = 109; ///< Message sender is not a good wallet
    static constexpr unsigned cant_override_external_wallet     = 110; ///< Can't override external wallet
    static constexpr unsigned only_flex_may_deploy_me           = 111; ///< Wrapper may only be deployed by Flex contract
    static constexpr unsigned unexpected_refs_count_in_code     = 112; ///< Unexpected references count in code
  };

  __always_inline
  StateInit getStateInit(const message<anyval> &msg) {
    if (msg.init->isa<ref<StateInit>>()) {
      return msg.init->get<ref<StateInit>>()();
    } else {
      return msg.init->get<StateInit>();
    }
  }

  __always_inline
  bool_t init(address external_wallet) {
    require(!wallet_, error_code::cant_override_external_wallet);

    auto parsed_msg = parse<message<anyval>>(parser(msg_slice()), error_code::bad_incoming_msg);
    require(!!parsed_msg.init, error_code::bad_incoming_msg);
    auto init = getStateInit(parsed_msg);
    require(!!init.code, error_code::bad_incoming_msg);
    auto mycode = *init.code;
    require(mycode.ctos().srefs() == 3, error_code::unexpected_refs_count_in_code);
    parser mycode_parser(mycode.ctos());
    mycode_parser.ldref();
    mycode_parser.ldref();
    auto mycode_salt = mycode_parser.ldrefrtos();
    auto flex_addr = parse<address>(mycode_salt);
    require(flex_addr == int_sender(), error_code::only_flex_may_deploy_me);

    wallet_ = external_wallet;

    tvm_rawreserve(start_balance_.get(), rawreserve_flag::up_to);
    set_int_return_flag(SEND_ALL_GAS);
    return bool_t{true};
  }

  __always_inline
  bool_t setInternalWalletCode(cell wallet_code) {
    check_owner();
    tvm_accept();
    require(!internal_wallet_code_, error_code::cant_override_wallet_code);
    require(__builtin_tvm_hashcu(wallet_code) == internal_wallet_hash,
            error_code::wrong_wallet_code_hash);
    internal_wallet_code_ = wallet_code;

    if constexpr (Internal) {
      auto value_gr = int_value();
      tvm_rawreserve(tvm_balance() - value_gr(), rawreserve_flag::up_to);
      set_int_return_flag(SEND_ALL_GAS);
    }
    return bool_t{true};
  }

  __always_inline
  address deployEmptyWallet(
    uint256     pubkey,
    address_opt internal_owner,
    uint128     crystals
  ) {
    // This protects from spending root balance to deploy message
    auto value = int_value();
    tvm_rawreserve(tvm_balance() - value(), rawreserve_flag::up_to);

    auto [wallet_init, dest] = calc_internal_wallet_init(pubkey, internal_owner);
    ITONTokenWalletPtr dest_handle(dest);
    dest_handle.deploy_noop(wallet_init, Crystals(crystals.get()));

    // sending all rest gas except reserved old balance, processing and deployment costs
    set_int_return_flag(SEND_ALL_GAS);
    return dest;
  }

  // Notification about incoming tokens from Wrapper owned external wallet
  __always_inline
  WrapperRet onTip3Transfer(
    uint128     balance,
    uint128     new_tokens,
    uint256     sender_pubkey,
    address_opt sender_owner,
    cell        payload,
    address     answer_addr
  ) {
    require(int_sender() == wallet_->get(), error_code::not_my_wallet_notifies);

    // to send answer to the original caller (caller->tip3wallet->wrapper->caller)
    set_int_sender(answer_addr);
    set_int_return_value(0);
    set_int_return_flag(SEND_ALL_GAS);

    auto args = parse<FlexDeployWalletArgs>(payload.ctos());

    auto value = int_value();
    tvm_rawreserve(tvm_balance() - value(), rawreserve_flag::up_to);

    auto [wallet_init, dest] = calc_internal_wallet_init(args.pubkey, args.owner);
    ITONTokenWalletPtr dest_handle(dest);
    dest_handle.deploy(wallet_init, Crystals(args.crystals.get())).accept(new_tokens, int_sender(), args.crystals);
    total_granted_ += new_tokens;

    return { uint32(0), dest_handle.get() };
  }

  __always_inline
  void burn(
    uint128     tokens,
    address     answer_addr,
    uint256     sender_pubkey,
    address_opt sender_owner,
    uint256     out_pubkey,
    address_opt out_owner
  ) {
    require(total_granted_ >= tokens, error_code::burn_unallocated);
    auto [sender, value_gr] = int_sender_and_value();
    require(sender == expected_internal_address(sender_pubkey, sender_owner),
            error_code::message_sender_is_not_good_wallet);
    tvm_rawreserve(tvm_balance() - value_gr(), rawreserve_flag::up_to);
    (*wallet_)(Crystals(0), SEND_ALL_GAS).
      transferToRecipient(answer_addr, out_pubkey, out_owner, tokens, uint128(0),
                          bool_t{true}, bool_t{false});
    total_granted_ -= tokens;
  }

  __always_inline
  uint128 requestTotalGranted() {
    auto value = int_value();
    tvm_rawreserve(tvm_balance() - value(), rawreserve_flag::up_to);
    set_int_return_flag(SEND_ALL_GAS);
    return total_granted_;
  }

  // getters
  __always_inline
  wrapper_details_info getDetails() {
    return { getName(), getSymbol(), getDecimals(),
             getRootKey(), getRootOwner(), getTotalGranted(), getInternalWalletCode(),
             getExternalWallet() };
  }

  __always_inline string getName() {
    return name_;
  }

  __always_inline string getSymbol() {
    return symbol_;
  }

  __always_inline uint8 getDecimals() {
    return decimals_;
  }

  __always_inline uint256 getRootKey() {
    return root_pubkey_;
  }

  __always_inline address getRootOwner() {
    return root_owner_ ? *root_owner_ : address::make_std(int8(0), uint256(0));
  }

  __always_inline uint128 getTotalGranted() {
    return total_granted_;
  }

  __always_inline bool_t hasInternalWalletCode() {
    return bool_t{!!internal_wallet_code_};
  }

  __always_inline cell getInternalWalletCode() {
    return internal_wallet_code_.get();
  }

  __always_inline address getExternalWallet() {
    return wallet_->get();
  }

  __always_inline
  address getWalletAddress(uint256 pubkey, address_opt owner) {
    return expected_internal_address(pubkey, owner);
  }

  // received bounced message back
  __always_inline static int _on_bounced(cell /*msg*/, slice msg_body) {
    tvm_accept();

    using Args = args_struct_t<&ITONTokenWallet::accept>;
    parser p(msg_body);
    require(p.ldi(32) == -1, error_code::wrong_bounced_header);
    auto [opt_hdr, =p] = parse_continue<abiv1::internal_msg_header>(p);
    require(opt_hdr && opt_hdr->function_id == id_v<&ITONTokenWallet::accept>,
            error_code::wrong_bounced_header);
    auto args = parse<Args>(p, error_code::wrong_bounced_args);
    auto bounced_val = args.tokens;

    auto [hdr, persist] = load_persistent_data<IWrapper, wrapper_replay_protection_t, DWrapper>();
    require(bounced_val <= persist.total_granted_, error_code::wrong_bounced_args);
    persist.total_granted_ -= bounced_val;
    save_persistent_data<IWrapper, wrapper_replay_protection_t>(hdr, persist);
    return 0;
  }

  __always_inline
  uint256 getInternalWalletCodeHash() {
    return uint256{__builtin_tvm_hashcu(internal_wallet_code_.get())};
  }

  // default processing of unknown messages
  __always_inline static int _fallback(cell /*msg*/, slice /*msg_body*/) {
    return 0;
  }

  // =============== Support functions ==================
  DEFAULT_SUPPORT_FUNCTIONS(IWrapper, wrapper_replay_protection_t)
private:
  __always_inline
  address expected_internal_address(uint256 sender_pubkey, address_opt sender_owner) {
    auto hash = calc_int_wallet_init_hash(
      name_, symbol_, decimals_,
      root_pubkey_, address{tvm_myaddr()},
      sender_pubkey, sender_owner,
      uint256(internal_wallet_hash), uint16(internal_wallet_code_depth),
      workchain_id_
    );
    return address::make_std(workchain_id_, hash);
  }

  __always_inline
  std::pair<StateInit, address> calc_internal_wallet_init(uint256 pubkey,
                                                          address_opt owner_addr) {
    auto [wallet_init, dest_addr] =
      prepare_internal_wallet_state_init_and_addr(
        name_, symbol_, decimals_,
        root_pubkey_, address{tvm_myaddr()},
        pubkey, owner_addr,
        uint256(internal_wallet_hash), uint16(internal_wallet_code_depth),
        workchain_id_, internal_wallet_code_.get());
    address dest = address::make_std(workchain_id_, dest_addr);
    return { wallet_init, dest };
  }

  __always_inline bool is_internal_owner() const { return root_owner_.has_value(); }

  __always_inline
  void check_internal_owner() {
    require(is_internal_owner(), error_code::internal_owner_disabled);
    require(*root_owner_ == int_sender(),
            error_code::message_sender_is_not_my_owner);
  }

  __always_inline
  void check_external_owner() {
    require(!is_internal_owner(), error_code::internal_owner_enabled);
    require(msg_pubkey() == root_pubkey_, error_code::message_sender_is_not_my_owner);
  }

  __always_inline
  void check_owner() {
    if constexpr (Internal)
      check_internal_owner();
    else
      check_external_owner();
  }
};

DEFINE_JSON_ABI(IWrapper, DWrapper, EWrapper);

// ----------------------------- Main entry functions ---------------------- //
DEFAULT_MAIN_ENTRY_FUNCTIONS_TMPL(Wrapper, IWrapper, DWrapper, WRAPPER_TIMESTAMP_DELAY)

