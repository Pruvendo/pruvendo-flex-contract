Require Import FinProof.Common. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.TradingPair.ClassTypes.
Require Import Contracts.TradingPair.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

(* Module Export ClassTypesModuleForFuncSig := ClassTypes xt sm. *)
Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.
 
 Parameter onDeploy : ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XAddress ) ) -> UExpression XBool true . 
 Parameter getFlexAddr : UExpression XAddress false . 
 Parameter getTip3Root : UExpression XAddress false . 
 Parameter getMinAmount : UExpression XInteger128 false . 
 Parameter getNotifyAddr : UExpression XAddress false . 
 Parameter _fallback : ( ( XCell ) ) -> ( ( XSlice ) ) -> UExpression XInteger false . 
 Parameter prepare_trading_pair_state_init_and_addr : ( ( DTradingPairLRecord ) ) -> ( ( XCell ) ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 

End SpecSig.

End Spec.  



