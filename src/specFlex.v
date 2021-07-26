Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG25.
Require Import classFlex.

Module specFlexSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export LedgerClass := LedgerClass xt sm . 
(* Import SolidityNotationsClass. *)
Module Export URSUS := SML xt sm LedgerClass.

Module Type specFLeXSig.
(* Import xt. Import sm. *)

Parameter FLeXClient_Ф_constructor : XInteger256 -> TvmCell -> TvmCell -> SMLExpression PhantomType false . 
Parameter FLeXClient_Ф_setFLeXCfg : TonsConfig -> XAddress -> XAddress -> SMLExpression PhantomType false . 
Parameter FLeXClient_Ф_deployTradingPair : XAddress -> XInteger128 -> XInteger128 -> SMLExpression XAddress false . 
Parameter FLeXClient_Ф_deployXchgPair : XAddress -> XAddress -> XInteger128 -> XInteger128 -> SMLExpression XAddress false . 
Parameter FLeXClient_Ф_deployPriceWithSell : TvmCell -> SMLExpression XAddress false . 
Parameter FLeXClient_Ф_deployPriceWithBuy : TvmCell -> SMLExpression XAddress false . 
Parameter FLeXClient_Ф_cancelSellOrder : TvmCell -> SMLExpression PhantomType false . 
Parameter FLeXClient_Ф_cancelBuyOrder : TvmCell -> SMLExpression PhantomType false . 
Parameter FLeXClient_Ф_cancelXchgOrder : TvmCell -> SMLExpression PhantomType false . 
Parameter FLeXClient_Ф_transfer : XAddress -> XInteger128 -> XBool -> SMLExpression PhantomType false . 
Parameter FLeXClient_Ф_deployPriceXchg : TvmCell -> SMLExpression XAddress false . 
Parameter FLeXClient_Ф_getOwner : SMLExpression XInteger256 false . 
Parameter FLeXClient_Ф_getFLeX : SMLExpression XAddress false . 
Parameter FLeXClient_Ф__fallback : SMLExpression XInteger false . 
(* Parameter FLeXClient_Ф_preparePrice : XInteger128 -> XInteger128 -> XInteger8 -> TvmCell -> Tip3Config -> TvmCell -> SMLExpression ( StateInit # XAddress # XInteger256 )%sol false .  *)
(* Parameter FLeXClient_Ф_preparePriceXchg : XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> TvmCell -> Tip3Config -> Tip3Config -> TvmCell -> SMLExpression ( StateInit # XAddress # XInteger256 )%sol false .  *)
Parameter FLeX_Ф_constructor : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XAddress -> SMLExpression PhantomType false . 
Parameter FLeX_Ф_setPairCode : TvmCell -> SMLExpression PhantomType false . 
Parameter FLeX_Ф_setXchgPairCode : TvmCell -> SMLExpression PhantomType false . 
Parameter FLeX_Ф_setPriceCode : TvmCell -> SMLExpression PhantomType false . 
Parameter FLeX_Ф_setXchgPriceCode : TvmCell -> SMLExpression PhantomType false . 
Parameter FLeX_Ф_isFullyInitialized : SMLExpression XBool false . 
Parameter FLeX_Ф_getTonsCfg : SMLExpression TonsConfig false . 
Parameter FLeX_Ф_getTradingPairCode : SMLExpression TvmCell false . 
Parameter FLeX_Ф_getXchgPairCode : SMLExpression TvmCell false . 
Parameter FLeX_Ф_getSellPriceCode : XAddress -> SMLExpression TvmCell false . 
Parameter FLeX_Ф_getXchgPriceCode : XAddress -> XAddress -> SMLExpression TvmCell false . 
Parameter FLeX_Ф_getSellTradingPair : XAddress -> SMLExpression XAddress false . 
Parameter FLeX_Ф_getXchgTradingPair : XAddress -> XAddress -> SMLExpression XAddress false . 
Parameter FLeX_Ф_getMinAmount : SMLExpression XInteger128 false . 
Parameter FLeX_Ф_getDealsLimit : SMLExpression XInteger8 false . 
Parameter FLeX_Ф_getNotifyAddr : SMLExpression XAddress false . 
Parameter FLeX_Ф__fallback : SMLExpression XInteger false . 
Parameter dealer_Ф_make_deal : OrderInfo -> OrderInfo -> SMLExpression ( XBool # XBool # XInteger128 )%sol false . 
(* Parameter dealer_Ф_extract_active_order : XMaybe OrderInfoWithIdx -> XQueue OrderInfo -> XInteger128 -> XBool -> SMLExpression ( XQueue OrderInfo ) false .  *)
Parameter dealer_Ф_process_queue : XInteger -> XInteger -> SMLExpression PhantomType false . 
Parameter Price_Ф_onTip3LendOwnership : XInteger128 -> XInteger32 -> XInteger256 -> XInteger256 -> TvmCell -> XAddress -> SMLExpression OrderRet false . 
Parameter Price_Ф_buyTip3 : XInteger128 -> XAddress -> XInteger32 -> SMLExpression OrderRet false . 
Parameter Price_Ф_processQueue : SMLExpression PhantomType false . 
Parameter Price_Ф_cancelSell : SMLExpression PhantomType false . 
Parameter Price_Ф_cancelBuy : SMLExpression PhantomType false . 
Parameter Price_Ф_getDetails : SMLExpression DetailsInfo false . 
Parameter Price_Ф_getPrice : SMLExpression XInteger128 false . 
Parameter Price_Ф_getMinimumAmount : SMLExpression XInteger128 false . 
Parameter Price_Ф_getTonsCfg : SMLExpression TonsConfig false . 
(* Parameter Price_Ф_getSells : SMLExpression ( XDictArray ) false .  *)
(* Parameter Price_Ф_getBuys : SMLExpression ( XDictArray ) false .  *)
Parameter Price_Ф_getSellAmount : SMLExpression XInteger128 false . 
Parameter Price_Ф_getBuyAmount : SMLExpression XInteger128 false . 
Parameter Price_Ф__fallback : SMLExpression XInteger false . 
Parameter Price_Ф_onTip3LendOwnershipMinValue : SMLExpression XInteger128 false . 
Parameter Price_Ф_buyTip3MinValue : XInteger128 -> SMLExpression XInteger128 false . 
Parameter Price_Ф_verify_tip3_addr : XAddress -> XInteger256 -> XInteger256 -> SMLExpression XBool false . 
Parameter Price_Ф_expected_wallet_address : XInteger256 -> XInteger256 -> SMLExpression XInteger256 false . 
(* Parameter DPrice_Ф_on_sell_fail : XInteger -> ITONTokenWalletPtr -> SMLExpression OrderRetP false .  *)
(* Parameter dealer_Ф_extract_active_order : XMaybe OrderInfoXchgWithIdx -> XInteger128 -> XBool -> SMLExpression false .  *)
Parameter PriceXchg_Ф_onTip3LendOwnership : XInteger128 -> XInteger32 -> XInteger256 -> XInteger256 -> TvmCell -> XAddress -> SMLExpression OrderRet false . 
Parameter PriceXchg_Ф_processQueue : SMLExpression PhantomType false . 
Parameter PriceXchg_Ф_cancelSell : SMLExpression PhantomType false . 
Parameter PriceXchg_Ф_cancelBuy : SMLExpression PhantomType false . 
Parameter PriceXchg_Ф_getDetails : SMLExpression DetailsInfoXchg false . 
Parameter PriceXchg_Ф_getPriceNum : SMLExpression XInteger128 false . 
Parameter PriceXchg_Ф_getPriceDenum : SMLExpression XInteger128 false . 
Parameter PriceXchg_Ф_getMinimumAmount : SMLExpression XInteger128 false . 
Parameter PriceXchg_Ф_getTonsCfg : SMLExpression TonsConfig false . 
(* Parameter DPriceXchg_Ф_getSells : SMLExpression ( XDictArray ) false .  *)
(* Parameter DPriceXchg_Ф_getBuys : SMLExpression ( XDictArray ) false .  *)
Parameter PriceXchg_Ф_getSellAmount : SMLExpression XInteger128 false . 
Parameter PriceXchg_Ф_getBuyAmount : SMLExpression XInteger128 false . 
Parameter PriceXchg_Ф__fallback : SMLExpression XInteger false . 
Parameter PriceXchg_Ф_onTip3LendOwnershipMinValue : SMLExpression XInteger128 false . 
Parameter PriceXchg_Ф_verify_tip3_addr : Tip3Config -> XAddress -> XInteger256 -> XInteger256 -> SMLExpression XBool false . 
Parameter PriceXchg_Ф_expected_wallet_address : Tip3Config -> XInteger256 -> XInteger256 -> SMLExpression XInteger256 false . 
(* Parameter PriceXchg_Ф_on_ord_fail : XInteger -> ITONTokenWalletPtr -> SMLExpression OrderRetP false .  *)
Parameter TradingPair_Ф_onDeploy : SMLExpression XBool false . 
Parameter TradingPair_Ф_getFLeXAddr : SMLExpression XAddress false . 
Parameter TradingPair_Ф_getTip3Root : SMLExpression XAddress false . 
Parameter TradingPair_Ф__fallback : SMLExpression XInteger false . 
Parameter XchgPair_Ф_onDeploy : SMLExpression XBool false . 
Parameter XchgPair_Ф_getFLeXAddr : SMLExpression XAddress false . 
Parameter XchgPair_Ф_getTip3MajorRoot : SMLExpression XAddress false . 
Parameter XchgPair_Ф_getTip3MinorRoot : SMLExpression XAddress false . 
Parameter XchgPair_Ф__fallback : SMLExpression XInteger false . 
Parameter Ф_is_active_time : XInteger32 -> SMLExpression XBool false . 
Parameter Ф_calc_cost : XInteger128 -> XInteger128 -> SMLExpression ( XMaybe XInteger128 ) false . 
(* Parameter Ф_process_queue_impl : XAddress -> IFLeXNotifyPtr -> XInteger128 -> XInteger8 -> TonsConfig -> XInteger -> XInteger -> XInteger128 -> XQueue OrderInfo -> XInteger128 -> XQueue OrderInfo -> SMLExpression process_retP false .  *)
(* Parameter Ф_cancel_order_impl : XQueue OrderInfo -> addr_std_fixed -> XInteger128 -> XBool -> Grams -> Grams -> Grams -> SMLExpression ( XQueue OrderInfoP ) false .  *)
(* Parameter Ф_prepare_price_state_init_and_addr : DPrice -> TvmCell -> SMLExpression ( StateInit # XInteger256 )%sol false .  *)
Parameter Ф_minor_cost : XInteger128 -> RationalPrice -> SMLExpression ( XMaybe XInteger128 ) false . 
(* Parameter Ф_process_queue_impl : XAddress -> XAddress -> IFLeXNotifyPtr -> price_t -> XInteger8 -> TonsConfig -> XInteger -> XInteger -> XInteger128 -> XInteger128 -> SMLExpression process_retP false .  *)
(* Parameter Ф_cancel_order_impl : addr_std_fixed -> XInteger128 -> XBool -> Grams -> Grams -> Grams -> SMLExpression false .  *)
Parameter Ф_numerator : SMLExpression XInteger128 false . 
Parameter Ф_denominator : SMLExpression XInteger128 false . 
(* Parameter Ф_prepare_price_xchg_state_init_and_addr : DPriceXchg -> TvmCell -> SMLExpression ( StateInit # XInteger256 )%sol false . 
Parameter Ф_prepare_trading_pair_state_init_and_addr : DTradingPair -> TvmCell -> SMLExpression ( StateInit # XInteger256 )%sol false . 
Parameter Ф_prepare_xchg_pair_state_init_and_addr : DXchgPair -> TvmCell -> SMLExpression ( StateInit # XInteger256 )%sol false . 
 *)
End specFLeXSig.

End specFlexSpec.
