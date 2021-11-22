Require Import FinProof.Common. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.XchgPair.ClassTypes.
Require Import Contracts.XchgPair.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.

Local Open Scope ursus_scope.

Parameter onDeploy : ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XAddress ) ) -> UExpression XBool true . 
 Parameter getFlexAddr : UExpression XAddress false . 
 Parameter getTip3MajorRoot : UExpression XAddress false . 
 Parameter getTip3MinorRoot : UExpression XAddress false . 
 Parameter getMinAmount : UExpression XInteger128 false . 
 Parameter getNotifyAddr : UExpression XAddress false . 
 Parameter _fallback : ( ( XCell ) ) -> ( ( XSlice ) ) -> UExpression XInteger false . 
 Parameter prepare_xchg_pair_state_init_and_addr : ( ( ContractLRecord ) ) -> ( ( XCell ) ) -> UExpression ( StateInitLRecord # XInteger256 ) false . 


End SpecSig.

End Spec.  