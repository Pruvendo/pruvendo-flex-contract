Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import CommonNotations.
Require Import Contracts.FlexClient.ClassTypes.
Require Import Contracts.FlexClient.Ledger.
Require Import Contracts.FlexClient.ClassTypesNotations.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

(* Module Export ClassTypesModuleForFuncSig := ClassTypes xt sm. *)
Module  LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter constructor :  ( uint256 ) ->  ( XCell ) ->  ( XCell ) -> UExpression PhantomType true . 
 Parameter setFlexCfg :  ( TonsConfigLRecord ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter setExtWalletCode :  ( XCell ) -> UExpression PhantomType true . 
 Parameter setFlexWalletCode :  ( XCell ) -> UExpression PhantomType true . 
 Parameter setFlexWrapperCode :  ( XCell ) -> UExpression PhantomType true . 
 Parameter deployTradingPair :  ( XAddress ) ->  ( uint128 ) ->  ( uint128 ) ->  ( uint128 ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter deployXchgPair :  ( XAddress ) ->  ( XAddress ) ->  ( uint128 ) ->  ( uint128 ) ->  ( uint128 ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter deployPriceWithSell :  ( uint128 ) ->  ( uint128 ) ->  ( uint32 ) ->  ( uint128 ) ->  ( uint8 ) ->  ( uint128 ) ->  ( XCell ) ->  ( XAddress ) ->  ( XAddress ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter deployPriceWithBuy :  ( uint128 ) ->  ( uint128 ) ->  ( uint32 ) ->  ( uint128 ) ->  ( uint8 ) ->  ( uint128 ) ->  ( XCell ) ->  ( XAddress ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter cancelSellOrder :  ( uint128 ) ->  ( uint128 ) ->  ( uint8 ) ->  ( uint128 ) ->  ( XCell ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter cancelBuyOrder :  ( uint128 ) ->  ( uint128 ) ->  ( uint8 ) ->  ( uint128 ) ->  ( XCell ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter cancelXchgOrder :  ( XBool ) ->  ( uint128 ) ->  ( uint128 ) ->  ( uint128 ) ->  ( uint8 ) ->  ( uint128 ) ->  ( XCell ) ->  ( Tip3ConfigLRecord ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter transfer :  ( XAddress ) ->  ( uint128 ) ->  ( XBool ) -> UExpression PhantomType true . 
 Parameter deployPriceXchg :  ( XBool ) ->  ( uint128 ) ->  ( uint128 ) ->  ( uint128 ) ->  ( uint128 ) ->  ( uint32 ) ->  ( uint128 ) ->  ( uint8 ) ->  ( uint128 ) ->  ( XCell ) ->  ( XAddress ) ->  ( XAddress ) ->  ( Tip3ConfigLRecord ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter registerWrapper :  ( uint256 ) ->  ( uint128 ) ->  ( Tip3ConfigLRecord ) -> UExpression PhantomType true . 
 Parameter registerTradingPair :  ( uint256 ) ->  ( uint128 ) ->  ( XAddress ) ->  ( uint128 ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter registerXchgPair :  ( uint256 ) ->  ( uint128 ) ->  ( XAddress ) ->  ( XAddress ) ->  ( uint128 ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter deployEmptyFlexWallet :  ( uint256 ) ->  ( uint128 ) ->  ( Tip3ConfigLRecord ) -> UExpression XAddress true . 
 Parameter burnWallet :  ( uint128 ) ->  ( uint256 ) ->  ( XAddress ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter getOwner : UExpression uint256 false . 
 Parameter getFlex : UExpression XAddress false . 
 Parameter hasExtWalletCode : UExpression XBool false . 
 Parameter hasFlexWalletCode : UExpression XBool false . 
 Parameter hasFlexWrapperCode : UExpression XBool false . 
 Parameter getPayloadForDeployInternalWallet :  ( uint256 ) ->  ( XAddress ) ->  ( uint128 ) -> UExpression XCell false . 
 Parameter _fallback : ( XCell ) -> ( XSlice ) -> UExpression uint false . 
 Parameter preparePrice :  ( uint128 ) ->  ( uint128 ) ->  ( uint8 ) ->  ( XCell ) ->  ( Tip3ConfigLRecord ) ->  ( XCell ) ->  ( XAddress ) -> UExpression ( StateInitLRecord # ( XAddress # uint256 ) )  false . 
 Parameter preparePriceXchg :  ( uint128 ) ->  ( uint128 ) ->  ( uint128 ) ->  ( uint8 ) ->  ( Tip3ConfigLRecord ) ->  ( Tip3ConfigLRecord ) ->  ( XCell ) ->  ( XAddress ) -> UExpression ( StateInitLRecord # ( XAddress # uint256 ) )  false . 


End SpecSig.


End Spec.  