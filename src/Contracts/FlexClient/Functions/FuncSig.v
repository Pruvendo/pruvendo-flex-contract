Require Import FinProof.Common. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.FlexClient.ClassTypes.
Require Import Contracts.FlexClient.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module Export ClassTypesModuleForFuncSig := ClassTypes xt sm.
Module  LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.
Local Open Scope ursus_scope.


Parameter constructor :  ( XInteger256 ) ->  ( XCell ) ->  ( XCell ) -> UExpression PhantomType true . 
 Parameter setFlexCfg :  ( TonsConfigLRecord ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter setExtWalletCode :  ( XCell ) -> UExpression PhantomType true . 
 Parameter setFlexWalletCode :  ( XCell ) -> UExpression PhantomType true . 
 Parameter setFlexWrapperCode :  ( XCell ) -> UExpression PhantomType true . 
 Parameter deployTradingPair :  ( XAddress ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter deployXchgPair :  ( XAddress ) ->  ( XAddress ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter deployPriceWithSell :  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger32 ) ->  ( XInteger128 ) ->  ( XInteger8 ) ->  ( XInteger128 ) ->  ( XCell ) ->  ( XAddress ) ->  ( XAddress ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter deployPriceWithBuy :  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger32 ) ->  ( XInteger128 ) ->  ( XInteger8 ) ->  ( XInteger128 ) ->  ( XCell ) ->  ( XAddress ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter cancelSellOrder :  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger8 ) ->  ( XInteger128 ) ->  ( XCell ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter cancelBuyOrder :  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger8 ) ->  ( XInteger128 ) ->  ( XCell ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter cancelXchgOrder :  ( XBool ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger8 ) ->  ( XInteger128 ) ->  ( XCell ) ->  ( Tip3ConfigLRecord ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter transfer :  ( XAddress ) ->  ( XInteger128 ) ->  ( XBool ) -> UExpression PhantomType true . 
 Parameter deployPriceXchg :  ( XBool ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger32 ) ->  ( XInteger128 ) ->  ( XInteger8 ) ->  ( XInteger128 ) ->  ( XCell ) ->  ( XAddress ) ->  ( XAddress ) ->  ( Tip3ConfigLRecord ) ->  ( Tip3ConfigLRecord ) ->  ( XAddress ) -> UExpression XAddress true . 
 Parameter registerWrapper :  ( XInteger256 ) ->  ( XInteger128 ) ->  ( Tip3ConfigLRecord ) -> UExpression PhantomType true . 
 Parameter registerTradingPair :  ( XInteger256 ) ->  ( XInteger128 ) ->  ( XAddress ) ->  ( XInteger128 ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter registerXchgPair :  ( XInteger256 ) ->  ( XInteger128 ) ->  ( XAddress ) ->  ( XAddress ) ->  ( XInteger128 ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter deployEmptyFlexWallet :  ( XInteger256 ) ->  ( XInteger128 ) ->  ( Tip3ConfigLRecord ) -> UExpression XAddress true . 
 Parameter burnWallet :  ( XInteger128 ) ->  ( XInteger256 ) ->  ( XAddress ) ->  ( XAddress ) -> UExpression PhantomType true . 
 Parameter getOwner : UExpression XInteger256 false . 
 Parameter getFlex : UExpression XAddress false . 
 Parameter hasExtWalletCode : UExpression XBool false . 
 Parameter hasFlexWalletCode : UExpression XBool false . 
 Parameter hasFlexWrapperCode : UExpression XBool false . 
 Parameter getPayloadForDeployInternalWallet :  ( XInteger256 ) ->  ( XAddress ) ->  ( XInteger128 ) -> UExpression XCell false . 
 Parameter _fallback : ( XCell ) -> ( XSlice ) -> UExpression XInteger false . 
 Parameter preparePrice :  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger8 ) ->  ( XCell ) ->  ( Tip3ConfigLRecord ) ->  ( XCell ) ->  ( XAddress ) -> UExpression ( StateInitLRecord # ( XAddress # XInteger256 ) )  false . 
 Parameter preparePriceXchg :  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger128 ) ->  ( XInteger8 ) ->  ( Tip3ConfigLRecord ) ->  ( Tip3ConfigLRecord ) ->  ( XCell ) ->  ( XAddress ) -> UExpression ( StateInitLRecord # ( XAddress # XInteger256 ) )  false . 


End SpecSig.


End Spec.  