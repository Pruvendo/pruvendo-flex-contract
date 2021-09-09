
Require Import UMLang.SolidityNotations2. 

 
Module Type FLeXConstsTypesSig (xt: XTypesSig) (sm: StateMonadSig). 
Module Import SolidityNotations := SolidityNotations xt sm .   
 
Import xt.

Parameter TIMESTAMP_DELAY : XInteger.
Parameter error_code_ι_message_sender_is_not_my_owner : XInteger . 
Parameter error_code_ι_sender_is_not_deployer : XInteger . 
Parameter error_code_ι_unexpected_refs_count_in_code : XInteger . 
Parameter error_code_ι_cant_override_code : XInteger . 

Parameter ok : XInteger . 
Parameter error_code_ι_out_of_tons : XInteger . 
Parameter error_code_ι_deals_limit : XInteger . 
Parameter error_code_ι_not_enough_tons_to_process : XInteger . 
Parameter error_code_ι_not_enough_tokens_amount : XInteger . 
Parameter error_code_ι_too_big_tokens_amount : XInteger . 
Parameter error_code_ι_different_workchain_id : XInteger . 
Parameter error_code_ι_unverified_tip3_wallet : XInteger . 
Parameter error_code_ι_canceled : XInteger . 
Parameter error_code_ι_expired : XInteger . 
Parameter safe_delay_period : XInteger . 

Parameter error_code_ι_not_enough_tons : XInteger . 

Parameter error_code_ι_zero_owner_pubkey : XInteger . 
Parameter error_code_ι_missed_flex_wallet_code : XInteger . 
Parameter error_code_ι_missed_flex_wrapper_code : XInteger . 


End FLeXConstsTypesSig.
