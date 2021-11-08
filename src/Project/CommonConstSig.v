
Require Import UMLang.SolidityNotations2. 

 
Module Type ConstsTypesSig (xt: XTypesSig) (sm: StateMonadSig). 
Module Import SolidityNotations := SolidityNotations xt sm .   
 
Import xt. (* Import sm.  *)

Parameter FLEX_TIMESTAMP_DELAY : XInteger . 
 Parameter sender_is_not_deployer : XInteger . 
 Parameter unexpected_refs_count_in_code : XInteger . 
 Parameter cant_override_code : XInteger . 
 Parameter sender_is_not_my_owner : XInteger . 
 Parameter not_enough_funds : XInteger . 
 Parameter wrapper_not_requested : XInteger . 
 Parameter trading_pair_not_requested : XInteger . 
 Parameter xchg_pair_not_requested : XInteger . 
 Parameter costs_inconsistency : XInteger . 
 Parameter wrapper_with_such_pubkey_already_requested : XInteger . 
 Parameter trading_pair_with_such_pubkey_already_requested : XInteger . 
 Parameter xchg_pair_with_such_pubkey_already_requested : XInteger . 

End ConstsTypesSig.
