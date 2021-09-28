
Require Import UMLang.SolidityNotations2. 

 
Module Type trainConstsTypesSig (xt: XTypesSig) (sm: StateMonadSig). 
Module Import SolidityNotations := SolidityNotations xt sm .   
 
Import xt. (* Import sm.  *)

Parameter const1 : XInteger.
Parameter const2 : XInteger . 
Parameter const3 : XInteger . 

End trainConstsTypesSig.
