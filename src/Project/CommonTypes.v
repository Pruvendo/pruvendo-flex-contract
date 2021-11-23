(* Require Import UMLang.BasicModuleTypes. 
Require Import UrsusStdLib.stdTypes_cpp.

Module Types (xt: XTypesSig) (sm: StateMonadSig).
Export xt. 

Module Export SolidityNotationsForCommonTypes := stdTypeNotations_cpp xt sm.
 *)
Require Import UMLang.BasicModuleTypes. 

Module Types (xt: XTypesSig) (sm: StateMonadSig).
Export xt.
Module Export BasicTypesForClassTypes := BasicTypes xt sm.

 Definition IFlexNotifyPtr := XAddress. 
 Definition ITONTokenWalletPtr := XAddress. 
 Definition IPricePtr := XAddress.
 Definition TokensType := uint128 (* XInteger128 *). 
 Definition WalletGramsType := XInteger128. 
 Definition Grams := XInteger16 . 
                            Definition auto := XInteger . 
 Definition addr_std_compact := XAddress . 
 Definition varuint32 := XInteger32 .
 Definition address_t := XAddress.
 Definition IWrapperPtr := XAddress .

End Types.

