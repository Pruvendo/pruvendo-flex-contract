Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import Contracts.TradingPair.ClassTypes.
Require Import Contracts.TradingPair.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

(* Module Export ClassTypesModuleForFuncSig := ClassTypes xt sm. *)
Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 
(* Module Export stdTypesNotationsModule := stdTypesNotations xt sm LedgerModuleForFuncSig. *)
Module Type SpecSig.
Local Open Scope ucpp_scope.
 Parameter onDeploy : ( ( uint128 ) ) -> ( ( uint128 ) ) -> ( ( XAddress ) ) -> UExpression XBool true . 
 Parameter getFlexAddr : UExpression XAddress false . 
 Parameter getTip3Root : UExpression XAddress false . 
 Parameter getMinAmount : UExpression uint128 false . 
 Parameter getNotifyAddr : UExpression XAddress false . 
 Parameter _fallback : ( ( XCell ) ) -> ( ( XSlice ) ) -> UExpression uint false . 
 Parameter prepare_trading_pair_state_init_and_addr : ( ( ContractLRecord ) ) -> ( ( XCell ) ) -> UExpression ( StateInitLRecord * uint256 ) false . 

End SpecSig.

End Spec.  



