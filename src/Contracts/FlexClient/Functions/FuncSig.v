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

Parameter constructor : URValue XInteger256 false -> URValue XCell false -> URValue XCell false -> UExpression PhantomType true . 
 Parameter setFlexCfg : URValue TonsConfigLRecord false -> URValue XAddress false -> UExpression PhantomType true . 
 Parameter setExtWalletCode : URValue XCell false -> UExpression PhantomType true . 
 Parameter setFlexWalletCode : URValue XCell false -> UExpression PhantomType true . 
 Parameter setFlexWrapperCode : URValue XCell false -> UExpression PhantomType true . 
 Parameter deployTradingPair : URValue XAddress false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XAddress false -> UExpression XAddress true . 
 Parameter deployXchgPair : URValue address_t false -> URValue address_t false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue address_t false -> UExpression XAddress true . 
 Parameter preparePrice : URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger8 false -> URValue XCell false -> URValue Tip3ConfigLRecord false -> URValue XCell false -> URValue address_t false -> UExpression ( StateInitLRecord # XAddress # XInteger256 )%sol false . 
 Parameter deployPriceWithSell : URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger32 false -> URValue XInteger128 false -> URValue XInteger8 false -> URValue XInteger128 false -> URValue XCell false -> URValue XAddress false -> URValue XAddress false -> URValue Tip3ConfigLRecord false -> URValue XAddress false -> UExpression XAddress true . 
 Parameter deployPriceWithBuy : URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger32 false -> URValue XInteger128 false -> URValue XInteger8 false -> URValue XInteger128 false -> URValue XCell false -> URValue address_t false -> URValue Tip3ConfigLRecord false -> URValue address_t false -> UExpression XAddress true . 
 Parameter cancelSellOrder : URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger8 false -> URValue XInteger128 false -> URValue XCell false -> URValue Tip3ConfigLRecord false -> URValue address_t false -> UExpression PhantomType true . 
 Parameter cancelBuyOrder : URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger8 false -> URValue XInteger128 false -> URValue XCell false -> URValue Tip3ConfigLRecord false -> URValue address_t false -> UExpression PhantomType true . 
 Parameter preparePriceXchg : URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger8 false -> URValue Tip3ConfigLRecord false -> URValue Tip3ConfigLRecord false -> URValue XCell false -> URValue address_t false -> UExpression ( StateInitLRecord # XAddress # XInteger256 )%sol false . 
 Parameter cancelXchgOrder : URValue XBool false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger8 false -> URValue XInteger128 false -> URValue XCell false -> URValue Tip3ConfigLRecord false -> URValue Tip3ConfigLRecord false -> URValue address_t false -> UExpression PhantomType true . 
 Parameter transfer : URValue address_t false -> URValue XInteger128 false -> URValue XBool false -> UExpression PhantomType true . 
 Parameter deployPriceXchg : URValue XBool false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger32 false -> URValue XInteger128 false -> URValue XInteger8 false -> URValue XInteger128 false -> URValue XCell false -> URValue XAddress false -> URValue XAddress false -> URValue Tip3ConfigLRecord false -> URValue Tip3ConfigLRecord false -> URValue XAddress false -> UExpression XAddress true . 
 Parameter deployWrapperWithWallet : URValue XInteger256 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue Tip3ConfigLRecord false -> UExpression XAddress true . 
 Parameter deployEmptyFlexWallet : URValue XInteger256 false -> URValue XInteger128 false -> URValue Tip3ConfigLRecord false -> UExpression XAddress true . 
 Parameter burnWallet : URValue XInteger128 false -> URValue XInteger256 false -> URValue address_t false -> URValue address_t false -> UExpression PhantomType true . 
 Parameter getOwner : UExpression XInteger256 false . 
 Parameter getFlex : UExpression XAddress false . 
 Parameter hasExtWalletCode : UExpression XBool false . 
 Parameter hasFlexWalletCode : UExpression XBool false . 
 Parameter hasFlexWrapperCode : UExpression XBool false . 
 Parameter getPayloadForDeployInternalWallet : URValue XInteger256 false -> URValue address_t false -> URValue XInteger128 false -> UExpression XCell false . 
 Parameter _fallback : URValue XCell false -> URValue XSlice false -> UExpression XInteger false . 

End SpecSig.


End Spec.  