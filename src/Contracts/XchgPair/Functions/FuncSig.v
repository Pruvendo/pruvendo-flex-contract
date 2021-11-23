Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import Contracts.XchgPair.ClassTypes.
Require Import Contracts.XchgPair.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 
(* Module Export stdTypesNotationsModule := stdTypesNotations xt sm LedgerModuleForFuncSig. *)
Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Parameter onDeploy : ( ( uint128 ) ) -> ( ( uint128 ) ) -> ( ( XAddress ) ) -> UExpression XBool true . 
 Parameter getFlexAddr : UExpression XAddress false . 
 Parameter getTip3MajorRoot : UExpression XAddress false . 
 Parameter getTip3MinorRoot : UExpression XAddress false . 
 Parameter getMinAmount : UExpression uint128 false . 
 Parameter getNotifyAddr : UExpression XAddress false . 
 Parameter _fallback : ( ( XCell ) ) -> ( ( XSlice ) ) -> UExpression uint false . 
 Parameter prepare_xchg_pair_state_init_and_addr : ( ( ContractLRecord ) ) -> ( ( XCell ) ) -> UExpression ( StateInitLRecord # uint256 ) false . 


End SpecSig.

End Spec.  