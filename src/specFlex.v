Require Import UMLang.SolidityNotations2.
Require Import flexContract.classFlex.


Module specFlex (xt: XTypesSig) (sm: StateMonadSig).
Module Import LedgerClass := LedgerClass xt sm . 

Module Type specFlexSig.
Import xt. Import sm.
 
Parameter DFLeXClient_Ф_constructor : XInteger256 -> TvmCell -> TvmCell -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeXClient_Ф_setFLeXCfg : TonsConfig -> XAddress -> XAddress -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeXClient_Ф_deployTradingPair : XAddress -> XInteger128 -> XInteger128 -> SMLExpression (S:=Ledger)  XAddress false . 
Parameter DFLeXClient_Ф_deployXchgPair : XAddress -> XAddress -> XInteger128 -> XInteger128 -> SMLExpression (S:=Ledger)  XAddress false . 
Parameter DFLeXClient_Ф_deployPriceWithSell : TvmCell -> SMLExpression (S:=Ledger)  XAddress false . 
Parameter DFLeXClient_Ф_deployPriceWithBuy : TvmCell -> SMLExpression (S:=Ledger)  XAddress false . 
Parameter DFLeXClient_Ф_cancelSellOrder : TvmCell -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeXClient_Ф_cancelBuyOrder : TvmCell -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeXClient_Ф_cancelXchgOrder : TvmCell -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeXClient_Ф_transfer : XAddress -> XInteger128 -> XBool -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeXClient_Ф_deployPriceXchg : TvmCell -> SMLExpression (S:=Ledger)  XAddress false . 
Parameter DFLeXClient_Ф_getOwner : SMLExpression (S:=Ledger)  XInteger256 false . 
Parameter DFLeXClient_Ф_getFLeX : SMLExpression (S:=Ledger)  XAddress false . 
Parameter DFLeXClient_Ф__fallback : SMLExpression (S:=Ledger)  XInteger false . 
(* Parameter DFLeXClient_Ф_preparePrice : XInteger128 -> XInteger128 -> XInteger8 -> TvmCell -> Tip3Config -> TvmCell -> SMLExpression (S:=Ledger)  ( StateInit # XAddress # XInteger256 )%sol false .  *)
(* Parameter DFLeXClient_Ф_preparePriceXchg : XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> TvmCell -> Tip3Config -> Tip3Config -> TvmCell -> SMLExpression (S:=Ledger)  ( StateInit # XAddress # XInteger256 )%sol false .  *)
Parameter DFLeX_Ф_constructor : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XAddress -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeX_Ф_setPairCode : TvmCell -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeX_Ф_setXchgPairCode : TvmCell -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeX_Ф_setPriceCode : TvmCell -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeX_Ф_setXchgPriceCode : TvmCell -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DFLeX_Ф_isFullyInitialized : SMLExpression (S:=Ledger)  XBool false . 
Parameter DFLeX_Ф_getTonsCfg : SMLExpression (S:=Ledger)  TonsConfig false . 
Parameter DFLeX_Ф_getTradingPairCode : SMLExpression (S:=Ledger)  TvmCell false . 
Parameter DFLeX_Ф_getXchgPairCode : SMLExpression (S:=Ledger)  TvmCell false . 
Parameter DFLeX_Ф_getSellPriceCode : XAddress -> SMLExpression (S:=Ledger)  TvmCell false . 
Parameter DFLeX_Ф_getXchgPriceCode : XAddress -> XAddress -> SMLExpression (S:=Ledger)  TvmCell false . 
Parameter DFLeX_Ф_getSellTradingPair : XAddress -> SMLExpression (S:=Ledger)  XAddress false . 
Parameter DFLeX_Ф_getXchgTradingPair : XAddress -> XAddress -> SMLExpression (S:=Ledger)  XAddress false . 
Parameter DFLeX_Ф_getMinAmount : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DFLeX_Ф_getDealsLimit : SMLExpression (S:=Ledger)  XInteger8 false . 
Parameter DFLeX_Ф_getNotifyAddr : SMLExpression (S:=Ledger)  XAddress false . 
Parameter DFLeX_Ф__fallback : SMLExpression (S:=Ledger)  XInteger false . 
Parameter dealer_Ф_make_deal : OrderInfo -> OrderInfo -> SMLExpression (S:=Ledger)  ( XBool # XBool # XInteger128 )%sol false . 
(* Parameter dealer_Ф_extract_active_order : XMaybe OrderInfoWithIdx -> XQueue OrderInfo -> XInteger128 -> XBool -> SMLExpression (S:=Ledger)  ( XQueue OrderInfo ) false .  *)
Parameter dealer_Ф_process_queue : XInteger -> XInteger -> SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DPrice_Ф_onTip3LendOwnership : XInteger128 -> XInteger32 -> XInteger256 -> XInteger256 -> TvmCell -> XAddress -> SMLExpression (S:=Ledger)  OrderRet false . 
Parameter DPrice_Ф_buyTip3 : XInteger128 -> XAddress -> XInteger32 -> SMLExpression (S:=Ledger)  OrderRet false . 
Parameter DPrice_Ф_processQueue : SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DPrice_Ф_cancelSell : SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DPrice_Ф_cancelBuy : SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DPrice_Ф_getDetails : SMLExpression (S:=Ledger)  DetailsInfo false . 
Parameter DPrice_Ф_getPrice : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPrice_Ф_getMinimumAmount : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPrice_Ф_getTonsCfg : SMLExpression (S:=Ledger)  TonsConfig false . 
(* Parameter DPrice_Ф_getSells : SMLExpression (S:=Ledger)  ( XDictArray ) false .  *)
(* Parameter DPrice_Ф_getBuys : SMLExpression (S:=Ledger)  ( XDictArray ) false .  *)
Parameter DPrice_Ф_getSellAmount : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPrice_Ф_getBuyAmount : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPrice_Ф__fallback : SMLExpression (S:=Ledger)  XInteger false . 
Parameter DPrice_Ф_onTip3LendOwnershipMinValue : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPrice_Ф_buyTip3MinValue : XInteger128 -> SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPrice_Ф_verify_tip3_addr : XAddress -> XInteger256 -> XInteger256 -> SMLExpression (S:=Ledger)  XBool false . 
Parameter DPrice_Ф_expected_wallet_address : XInteger256 -> XInteger256 -> SMLExpression (S:=Ledger)  XInteger256 false . 
(* Parameter DPrice_Ф_on_sell_fail : XInteger -> ITONTokenWalletPtr -> SMLExpression (S:=Ledger)  OrderRetP false .  *)
(* Parameter dealer_Ф_extract_active_order : XMaybe OrderInfoXchgWithIdx -> XInteger128 -> XBool -> SMLExpression (S:=Ledger)  false .  *)
Parameter DPriceXchg_Ф_onTip3LendOwnership : XInteger128 -> XInteger32 -> XInteger256 -> XInteger256 -> TvmCell -> XAddress -> SMLExpression (S:=Ledger)  OrderRet false . 
Parameter DPriceXchg_Ф_processQueue : SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DPriceXchg_Ф_cancelSell : SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DPriceXchg_Ф_cancelBuy : SMLExpression (S:=Ledger)  PhantomType false . 
Parameter DPriceXchg_Ф_getDetails : SMLExpression (S:=Ledger)  DetailsInfoXchg false . 
Parameter DPriceXchg_Ф_getPriceNum : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPriceXchg_Ф_getPriceDenum : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPriceXchg_Ф_getMinimumAmount : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPriceXchg_Ф_getTonsCfg : SMLExpression (S:=Ledger)  TonsConfig false . 
(* Parameter DPriceXchg_Ф_getSells : SMLExpression (S:=Ledger)  ( XDictArray ) false .  *)
(* Parameter DPriceXchg_Ф_getBuys : SMLExpression (S:=Ledger)  ( XDictArray ) false .  *)
Parameter DPriceXchg_Ф_getSellAmount : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPriceXchg_Ф_getBuyAmount : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPriceXchg_Ф__fallback : SMLExpression (S:=Ledger)  XInteger false . 
Parameter DPriceXchg_Ф_onTip3LendOwnershipMinValue : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter DPriceXchg_Ф_verify_tip3_addr : Tip3Config -> XAddress -> XInteger256 -> XInteger256 -> SMLExpression (S:=Ledger)  XBool false . 
Parameter DPriceXchg_Ф_expected_wallet_address : Tip3Config -> XInteger256 -> XInteger256 -> SMLExpression (S:=Ledger)  XInteger256 false . 
(* Parameter DPriceXchg_Ф_on_ord_fail : XInteger -> ITONTokenWalletPtr -> SMLExpression (S:=Ledger)  OrderRetP false .  *)
Parameter DTradingPair_Ф_onDeploy : SMLExpression (S:=Ledger)  XBool false . 
Parameter DTradingPair_Ф_getFLeXAddr : SMLExpression (S:=Ledger)  XAddress false . 
Parameter DTradingPair_Ф_getTip3Root : SMLExpression (S:=Ledger)  XAddress false . 
Parameter DTradingPair_Ф__fallback : SMLExpression (S:=Ledger)  XInteger false . 
Parameter DXchgPair_Ф_onDeploy : SMLExpression (S:=Ledger)  XBool false . 
Parameter DXchgPair_Ф_getFLeXAddr : SMLExpression (S:=Ledger)  XAddress false . 
Parameter DXchgPair_Ф_getTip3MajorRoot : SMLExpression (S:=Ledger)  XAddress false . 
Parameter DXchgPair_Ф_getTip3MinorRoot : SMLExpression (S:=Ledger)  XAddress false . 
Parameter DXchgPair_Ф__fallback : SMLExpression (S:=Ledger)  XInteger false . 
Parameter Ф_is_active_time : XInteger32 -> SMLExpression (S:=Ledger)  XBool false . 
Parameter Ф_calc_cost : XInteger128 -> XInteger128 -> SMLExpression (S:=Ledger)  ( XMaybe XInteger128 ) false . 
(* Parameter Ф_process_queue_impl : XAddress -> IFLeXNotifyPtr -> XInteger128 -> XInteger8 -> TonsConfig -> XInteger -> XInteger -> XInteger128 -> XQueue OrderInfo -> XInteger128 -> XQueue OrderInfo -> SMLExpression (S:=Ledger)  process_retP false .  *)
(* Parameter Ф_cancel_order_impl : XQueue OrderInfo -> addr_std_fixed -> XInteger128 -> XBool -> Grams -> Grams -> Grams -> SMLExpression (S:=Ledger)  ( XQueue OrderInfoP ) false .  *)
(* Parameter Ф_prepare_price_state_init_and_addr : DPrice -> TvmCell -> SMLExpression (S:=Ledger)  ( StateInit # XInteger256 )%sol false .  *)
Parameter Ф_minor_cost : XInteger128 -> RationalPrice -> SMLExpression (S:=Ledger)  ( XMaybe XInteger128 ) false . 
(* Parameter Ф_process_queue_impl : XAddress -> XAddress -> IFLeXNotifyPtr -> price_t -> XInteger8 -> TonsConfig -> XInteger -> XInteger -> XInteger128 -> XInteger128 -> SMLExpression (S:=Ledger)  process_retP false .  *)
(* Parameter Ф_cancel_order_impl : addr_std_fixed -> XInteger128 -> XBool -> Grams -> Grams -> Grams -> SMLExpression (S:=Ledger)  false .  *)
Parameter Ф_numerator : SMLExpression (S:=Ledger)  XInteger128 false . 
Parameter Ф_denominator : SMLExpression (S:=Ledger)  XInteger128 false . 
(* Parameter Ф_prepare_price_xchg_state_init_and_addr : DPriceXchg -> TvmCell -> SMLExpression (S:=Ledger)  ( StateInit # XInteger256 )%sol false . 
Parameter Ф_prepare_trading_pair_state_init_and_addr : DTradingPair -> TvmCell -> SMLExpression (S:=Ledger)  ( StateInit # XInteger256 )%sol false . 
Parameter Ф_prepare_xchg_pair_state_init_and_addr : DXchgPair -> TvmCell -> SMLExpression (S:=Ledger)  ( StateInit # XInteger256 )%sol false . 
 *)
End specFlexSig.

End specFlex.
