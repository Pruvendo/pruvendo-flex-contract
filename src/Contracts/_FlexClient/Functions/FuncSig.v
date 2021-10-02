Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.FlexClient.ClassTypes.
Require Import Contracts.FlexClient.Ledger .

Module FlexClientSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export ClassTypesModule := ClassTypes xt sm . 
Module Export LedgerModule := FlexClientClass xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModule.


Module Type FlexClientSpecSig.

 Parameter FlexClient_Ф_constructor : XInteger256 -> XCell -> XCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setFlexCfg : TonsConfigStateLRecord -> addr_std_compact -> addr_std_compact -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setExtWalletCode : XCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setFlexWalletCode : XCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setFlexWrapperCode : XCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_deployTradingPair : addr_std_compact -> XInteger128 -> XInteger128 -> XInteger128 -> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployXchgPair : addr_std_compact -> addr_std_compact -> XInteger128 -> XInteger128 -> XInteger128 -> UExpression XAddress true .
 Parameter FlexClient_Ф_preparePrice : XInteger128 -> XInteger128 -> XInteger8 -> XCell -> Tip3ConfigStateLRecord-> XCell -> UExpression ( StateInitStateLRecord # XAddress # XInteger256 )%sol false . 
 Parameter FlexClient_Ф_deployPriceWithSell : XInteger128 -> XInteger128 -> XInteger32 -> XInteger128 -> XInteger8 -> XInteger128 -> XCell -> addr_std_compact -> addr_std_compact -> Tip3ConfigStateLRecord-> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployPriceWithBuy : XInteger128 -> XInteger128 -> XInteger32 -> XInteger128 -> XInteger8 -> XInteger128 -> XCell -> addr_std_compact -> Tip3ConfigStateLRecord-> UExpression XAddress true . 
 Parameter FlexClient_Ф_cancelSellOrder : XInteger128 -> XInteger128 -> XInteger8 -> XInteger128 -> XCell -> Tip3ConfigStateLRecord-> UExpression PhantomType true . 
 Parameter FlexClient_Ф_cancelBuyOrder : XInteger128 -> XInteger128 -> XInteger8 -> XInteger128 -> XCell -> Tip3ConfigStateLRecord-> UExpression PhantomType true . 
 Parameter FlexClient_Ф_preparePriceXchg : XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> Tip3ConfigStateLRecord-> Tip3ConfigStateLRecord-> XCell -> UExpression ( StateInitStateLRecord # XAddress # XInteger256 )%sol false . 
 Parameter FlexClient_Ф_cancelXchgOrder : XBool -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XInteger128 -> XCell -> Tip3ConfigStateLRecord-> Tip3ConfigStateLRecord-> UExpression PhantomType true . 
 Parameter FlexClient_Ф_transfer : addr_std_compact -> XInteger128 -> XBool -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_deployPriceXchg : XBool -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger32 -> XInteger128 -> XInteger8 -> XInteger128 -> XCell -> addr_std_compact -> addr_std_compact -> Tip3ConfigStateLRecord-> Tip3ConfigStateLRecord-> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployWrapperWithWallet : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> Tip3ConfigStateLRecord-> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployEmptyFlexWallet : XInteger256 -> XInteger128 -> Tip3ConfigStateLRecord-> UExpression XAddress true . 
 Parameter FlexClient_Ф_burnWallet : XInteger128 -> XInteger256 -> addr_std_compact -> addr_std_compact -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_getOwner : UExpression XInteger256 false . 
 Parameter FlexClient_Ф_getFlex : UExpression XAddress false . 
 Parameter FlexClient_Ф_hasExtWalletCode : UExpression XBool false . 
 Parameter FlexClient_Ф_hasFlexWalletCode : UExpression XBool false . 
 Parameter FlexClient_Ф_hasFlexWrapperCode : UExpression XBool false . 
 Parameter FlexClient_Ф_getPayloadForDeployInternalWallet : XInteger256 -> addr_std_compact -> XInteger128 -> UExpression XCell false . 
 Parameter FlexClient_Ф__fallback : XCell -> UExpression XInteger false . 


End FlexClientSpecSig.


End FlexClientSpec.  