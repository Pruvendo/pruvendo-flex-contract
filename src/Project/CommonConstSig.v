
Require Import UMLang.BasicModuleTypes. 
Require Import CommonTypes. 
 
Module Type ConstsTypesSig (xt: XTypesSig) (sm: StateMonadSig). 
Module Export CommonTypes := Types xt sm .   
 
Import xt. 

(*Проверить типы!!!*)
Parameter FLEX_TIMESTAMP_DELAY : XUInteger . 
Parameter sender_is_not_deployer : XUInteger . 
Parameter unexpected_refs_count_in_code : XUInteger . 
Parameter cant_override_code : XUInteger . 
Parameter sender_is_not_my_owner : XUInteger . 
Parameter not_enough_funds : XUInteger . 
Parameter wrapper_not_requested : XUInteger . 
Parameter trading_pair_not_requested : XUInteger . 
Parameter xchg_pair_not_requested : XUInteger . 
Parameter costs_inconsistency : XUInteger . 
Parameter wrapper_with_such_pubkey_already_requested : XUInteger . 
Parameter trading_pair_with_such_pubkey_already_requested : XUInteger . 
Parameter xchg_pair_with_such_pubkey_already_requested : XUInteger . 

Parameter TIMESTAMP_DELAY : XUInteger . 
Parameter message_sender_is_not_my_owner : XUInteger . 
Parameter missed_ext_wallet_code : XUInteger . 
Parameter missed_flex_wallet_code : XUInteger . 
Parameter missed_flex_wrapper_code : XUInteger . 
Parameter zero_owner_pubkey : XUInteger . 

Parameter SENDER_WANTS_TO_PAY_FEES_SEPARATELY : XUInteger .
Parameter ec_ι_expired : XUInteger .
Parameter ec_ι_out_of_tons : XUInteger .
Parameter ok : XUInteger .
Parameter SEND_ALL_GAS : XUInteger .
Parameter DELETE_ME_IF_I_AM_EMPTY : XUInteger .
Parameter rawreserve_flag_ι_up_to : XUInteger .
Parameter ec_ι_not_enough_tons_to_process : XUInteger .
Parameter ec_ι_unverified_tip3_wallet : XUInteger .
Parameter ec_ι_not_enough_tokens_amount : XUInteger .
Parameter ec_ι_too_big_tokens_amount : XUInteger .

Parameter error_code_ι_internal_owner_disabled : XUInteger .
Parameter error_code_ι_message_sender_is_not_my_owner : XUInteger .
Parameter error_code_ι_internal_owner_enabled : XUInteger .
Parameter error_code_ι_too_big_decimals : XUInteger .
Parameter error_code_ι_cant_override_wallet_code : XUInteger .
Parameter error_code_ι_not_enough_balance : XUInteger .
Parameter error_code_ι_define_pubkey_or_internal_owner : XUInteger .
Parameter error_code_ι_wrong_bounced_header : XUInteger .
Parameter error_code_ι_wrong_bounced_args : XUInteger .
(* Parameter  : XUInteger . *)

Parameter not_enough_tons : XUInteger.
Parameter double_deploy : XUInteger.
Parameter zero_min_amount : XUInteger.

Parameter wrong_wallet_code_hash : XUInteger.
Parameter too_big_decimals : XUInteger.
Parameter not_my_wallet_notifies : XUInteger.
Parameter burn_unallocated : XUInteger.
Parameter message_sender_is_not_good_wallet : XUInteger.
Parameter cant_override_external_wallet : XUInteger.
Parameter only_flex_may_deploy_me : XUInteger.


Parameter deals_limit : XUInteger.
Parameter different_workchain_id : XUInteger.
Parameter canceled : XUInteger.

Parameter only_original_owner_allowed : XUInteger.
Parameter wallet_in_lend_owneship : XUInteger.
Parameter transfer_to_zero_address : XUInteger.
Parameter message_sender_is_not_my_root : XUInteger.
Parameter destroy_non_empty_wallet : XUInteger.
Parameter finish_time_must_be_greater_than_now : XUInteger.
Parameter no_allowance_set : XUInteger.
Parameter wrong_spender : XUInteger.
Parameter not_enough_allowance : XUInteger.
Parameter wrong_public_call : XUInteger.
Parameter non_zero_remaining : XUInteger.


End ConstsTypesSig.
