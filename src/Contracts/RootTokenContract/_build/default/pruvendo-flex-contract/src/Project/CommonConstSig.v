
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


End ConstsTypesSig.