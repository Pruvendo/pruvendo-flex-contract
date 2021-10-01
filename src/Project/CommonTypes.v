Require Import UMLang.SolidityNotations2. 

Module Types (xt: XTypesSig) (sm: StateMonadSig).
Export xt. 

Module Export SolidityNotationsForClassTypes := SolidityNotations xt sm.

Definition IFlexNotifyPtr := XAddress. 
 Definition ITONTokenWalletPtr := XAddress. 
 Definition IPricePtr := XAddress. 
 Definition TokensType := XInteger128. 
 Definition WalletGramsType := XInteger128. 
 Definition Grams := XInteger16 . 
                            Definition auto := XInteger . 
 Definition addr_std_compact := XAddress . 
 Definition varuint32 := XInteger32 .

End Types.

