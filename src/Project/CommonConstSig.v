
Require Import UMLang.BasicModuleTypes. 
Require Import CommonTypes. 
 
Module Type ConstsTypesSig (xt: XTypesSig) (sm: StateMonadSig). 
Module Export CommonTypes := Types xt sm .   
 
Import xt. 

(*Проверить типы!!!*)
Parameter FLEX_TIMESTAMP_DELAY : ErrorType . 
Parameter sender_is_not_deployer : ErrorType . 
Parameter unexpected_refs_count_in_code : ErrorType . 
Parameter cant_override_code : ErrorType . 
Parameter sender_is_not_my_owner : ErrorType . 
Parameter not_enough_funds : ErrorType . 
Parameter wrapper_not_requested : ErrorType . 
Parameter trading_pair_not_requested : ErrorType . 
Parameter xchg_pair_not_requested : ErrorType . 
Parameter costs_inconsistency : ErrorType . 
Parameter wrapper_with_such_pubkey_already_requested : ErrorType . 
Parameter trading_pair_with_such_pubkey_already_requested : ErrorType . 
Parameter xchg_pair_with_such_pubkey_already_requested : ErrorType . 

Parameter TIMESTAMP_DELAY : ErrorType . 
Parameter message_sender_is_not_my_owner : ErrorType . 
Parameter missed_ext_wallet_code : ErrorType . 
Parameter missed_flex_wallet_code : ErrorType . 
Parameter missed_flex_wrapper_code : ErrorType . 
Parameter zero_owner_pubkey : ErrorType . 

Parameter SENDER_WANTS_TO_PAY_FEES_SEPARATELY : XUInteger .
Parameter ec_ι_expired : ErrorType .
Parameter ec_ι_out_of_tons : ErrorType .
Parameter ok : ErrorType .
Parameter SEND_ALL_GAS : XUInteger .
Parameter DELETE_ME_IF_I_AM_EMPTY : XUInteger .
Parameter rawreserve_flag_ι_up_to : ErrorType .
Parameter ec_ι_not_enough_tons_to_process : ErrorType .
Parameter ec_ι_unverified_tip3_wallet : ErrorType .
Parameter ec_ι_not_enough_tokens_amount : ErrorType .
Parameter ec_ι_too_big_tokens_amount : ErrorType .

Parameter error_code_ι_internal_owner_disabled : ErrorType .
Parameter error_code_ι_message_sender_is_not_my_owner : ErrorType .
Parameter error_code_ι_internal_owner_enabled : ErrorType .
Parameter error_code_ι_too_big_decimals : ErrorType .
Parameter error_code_ι_cant_override_wallet_code : ErrorType .
Parameter error_code_ι_not_enough_balance : ErrorType .
Parameter error_code_ι_define_pubkey_or_internal_owner : ErrorType .
Parameter error_code_ι_wrong_bounced_header : ErrorType .
Parameter error_code_ι_wrong_bounced_args : ErrorType .
(* Parameter  : ErrorType . *)

Parameter not_enough_tons : ErrorType.
Parameter double_deploy : ErrorType.
Parameter zero_min_amount : ErrorType.

Parameter wrong_wallet_code_hash : ErrorType.
Parameter too_big_decimals : ErrorType.
Parameter not_my_wallet_notifies : ErrorType.
Parameter burn_unallocated : ErrorType.
Parameter message_sender_is_not_good_wallet : ErrorType.
Parameter cant_override_external_wallet : ErrorType.
Parameter only_flex_may_deploy_me : ErrorType.

Parameter error_code_ι_cant_override_external_wallet : ErrorType .
Parameter error_code_ι_bad_incoming_msg : ErrorType .
Parameter error_code_ι_unexpected_refs_count_in_code : ErrorType .
Parameter error_code_ι_only_flex_may_deploy_me : ErrorType . 
Parameter error_code_ι_not_my_wallet_notifies : ErrorType .
Parameter error_code_ι_burn_unallocated : ErrorType .
Parameter error_code_ι_message_sender_is_not_good_wallet : ErrorType .

Parameter deals_limit : XUInteger.
Parameter different_workchain_id : XUInteger.
Parameter canceled : XUInteger.

Parameter only_original_owner_allowed : ErrorType.
Parameter wallet_in_lend_owneship : ErrorType.
Parameter transfer_to_zero_address : ErrorType.
Parameter message_sender_is_not_my_root : ErrorType.
Parameter destroy_non_empty_wallet : ErrorType.
Parameter finish_time_must_be_greater_than_now : ErrorType.
Parameter no_allowance_set : ErrorType.
Parameter wrong_spender : ErrorType.
Parameter not_enough_allowance : ErrorType.
Parameter wrong_public_call : ErrorType.
Parameter non_zero_remaining : ErrorType.
Parameter bad_incoming_msg : ErrorType .
Parameter internal_owner_disabled : ErrorType .

Parameter DEFAULT_MSG_FLAGS : XUInteger .

Parameter safe_delay_period : XUInteger .

Parameter ec : ErrorType .

End ConstsTypesSig.
