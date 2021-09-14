Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG26.

Require Import FLeXClientClass.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdFuncNotations.
Require Import UrsusStdLib.stdNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Module specFlexClientSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export LedgerClassModule := LedgerFLeXClientClass xt sm . 

Module Export tvmNotationsModule := tvmNotations xt sm LedgerClassModule.

Module Type specFLeXClientSig.



Parameter FlexClient_Ф_constructor : XInteger256 -> TvmCell -> TvmCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setFlexCfg : TonsConfig -> addr_std_compact -> addr_std_compact -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setExtWalletCode : TvmCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setFlexWalletCode : TvmCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setFlexWrapperCode : TvmCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_deployTradingPair : addr_std_compact -> XInteger128 -> XInteger128 -> XInteger128 -> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployXchgPair : addr_std_compact -> addr_std_compact -> XInteger128 -> XInteger128 -> XInteger128 -> UExpression XAddress true . 
(*  Parameter FlexClient_Ф_preparePrice : XInteger128 -> XInteger128 -> XInteger8 -> TvmCell -> Tip3Config -> TvmCell -> UExpression ( StateInit # XAddress # XInteger256 )%type false .  *)
 Parameter FlexClient_Ф_deployPriceWithSell : XInteger128 -> XInteger128 -> XInteger32 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> addr_std_compact -> addr_std_compact -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployPriceWithBuy : XInteger128 -> XInteger128 -> XInteger32 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> addr_std_compact -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_cancelSellOrder : XInteger128 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> Tip3Config -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_cancelBuyOrder : XInteger128 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> Tip3Config -> UExpression PhantomType true . 
(*  Parameter FlexClient_Ф_preparePriceXchg : XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> Tip3Config -> Tip3Config -> TvmCell -> UExpression ( StateInit # XAddress # XInteger256 )%type false .  *)
 Parameter FlexClient_Ф_cancelXchgOrder : XBool -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> Tip3Config -> Tip3Config -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_transfer : addr_std_compact -> XInteger128 -> XBool -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_deployPriceXchg : XBool -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger32 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> addr_std_compact -> addr_std_compact -> Tip3Config -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployWrapperWithWallet : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployEmptyFlexWallet : XInteger256 -> XInteger128 -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_burnWallet : XInteger128 -> XInteger256 -> addr_std_compact -> addr_std_compact -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_getOwner : UExpression XInteger256 false . 
 Parameter FlexClient_Ф_getFlex : UExpression XAddress false . 
 Parameter FlexClient_Ф_hasExtWalletCode : UExpression XBool false . 
 Parameter FlexClient_Ф_hasFlexWalletCode : UExpression XBool false . 
 Parameter FlexClient_Ф_hasFlexWrapperCode : UExpression XBool false . 
 Parameter FlexClient_Ф_getPayloadForDeployInternalWallet : XInteger256 -> addr_std_compact -> XInteger128 -> UExpression TvmCell false . 
 Parameter FlexClient_Ф__fallback : UExpression TvmCell false -> UExpression XInteger false . 

End specFLeXClientSig.

End specFlexClientSpec.
