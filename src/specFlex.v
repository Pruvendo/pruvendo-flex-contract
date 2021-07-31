Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG25.
Require Import classFlex.

Require Import stdFunc.
Require Import stdFuncNotations.

Module specFlexSpec (xt: XTypesSig) (sm: StateMonadSig).

Module Export LedgerClassModule := LedgerClass xt sm . 
Module Export stdFuncNotationsModule := stdFuncNotations xt sm LedgerClassModule.

Module Type specFLeXSig.
(* Import xt. Import sm. *)


Parameter FLeXClient_Ф_constructor : XInteger256 -> TvmCell -> TvmCell -> UExpression PhantomType false . 
Parameter FLeXClient_Ф_setFLeXCfg : TonsConfig -> XAddress -> XAddress -> UExpression PhantomType false . 
Parameter FLeXClient_Ф_deployTradingPair : XAddress -> XInteger128 -> XInteger128 -> UExpression XAddress false . 
Parameter FLeXClient_Ф_deployXchgPair : XAddress -> XAddress -> XInteger128 -> XInteger128 -> UExpression XAddress false . 
Parameter FLeXClient_Ф_deployPriceWithSell : TvmCell -> UExpression XAddress false . 
Parameter FLeXClient_Ф_deployPriceWithBuy : TvmCell -> UExpression XAddress false . 
Parameter FLeXClient_Ф_cancelSellOrder : TvmCell -> UExpression PhantomType false . 
Parameter FLeXClient_Ф_cancelBuyOrder : TvmCell -> UExpression PhantomType false . 
Parameter FLeXClient_Ф_cancelXchgOrder : TvmCell -> UExpression PhantomType false . 
Parameter FLeXClient_Ф_transfer : XAddress -> XInteger128 -> XBool -> UExpression PhantomType false . 
Parameter FLeXClient_Ф_deployPriceXchg : TvmCell -> UExpression XAddress false . 
Parameter FLeXClient_Ф_getOwner : UExpression XInteger256 false . 
Parameter FLeXClient_Ф_getFLeX : UExpression XAddress false . 
Parameter FLeXClient_Ф__fallback : UExpression XInteger false . 
(* Parameter FLeXClient_Ф_preparePrice : XInteger128 -> XInteger128 -> XInteger8 -> TvmCell -> Tip3Config -> TvmCell -> UExpression ( StateInit # XAddress # XInteger256 )%sol false .  *)
(* Parameter FLeXClient_Ф_preparePriceXchg : XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> TvmCell -> Tip3Config -> Tip3Config -> TvmCell -> UExpression ( StateInit # XAddress # XInteger256 )%sol false .  *)
Parameter FLeX_Ф_constructor : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XAddress -> UExpression PhantomType false . 
Parameter FLeX_Ф_setPairCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_setXchgPairCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_setPriceCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_setXchgPriceCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_isFullyInitialized : UExpression XBool false . 
Parameter FLeX_Ф_getTonsCfg : UExpression TonsConfig false . 
Parameter FLeX_Ф_getTradingPairCode : UExpression TvmCell false . 
Parameter FLeX_Ф_getXchgPairCode : UExpression TvmCell false . 
Parameter FLeX_Ф_getSellPriceCode : XAddress -> UExpression TvmCell false . 
Parameter FLeX_Ф_getXchgPriceCode : XAddress -> XAddress -> UExpression TvmCell false . 
Parameter FLeX_Ф_getSellTradingPair : XAddress -> UExpression XAddress false . 
Parameter FLeX_Ф_getXchgTradingPair : XAddress -> XAddress -> UExpression XAddress false . 
Parameter FLeX_Ф_getMinAmount : UExpression XInteger128 false . 
Parameter FLeX_Ф_getDealsLimit : UExpression XInteger8 false . 
Parameter FLeX_Ф_getNotifyAddr : UExpression XAddress false . 
Parameter FLeX_Ф__fallback : UExpression XInteger false . 
Parameter dealer_Ф_make_deal : OrderInfo -> OrderInfo -> UExpression ( XBool # XBool # XInteger128 )%sol false . 
(* Parameter dealer_Ф_extract_active_order : XMaybe OrderInfoWithIdx -> XQueue OrderInfo -> XInteger128 -> XBool -> UExpression ( XQueue OrderInfo ) false .  *)
Parameter dealer_Ф_process_queue : XInteger -> XInteger -> UExpression PhantomType false . 
Parameter Price_Ф_onTip3LendOwnership : XInteger128 -> XInteger32 -> XInteger256 -> XInteger256 -> TvmCell -> XAddress -> UExpression OrderRet false . 
Parameter Price_Ф_buyTip3 : XInteger128 -> XAddress -> XInteger32 -> UExpression OrderRet false . 
Parameter Price_Ф_processQueue : UExpression PhantomType false . 
Parameter Price_Ф_cancelSell : UExpression PhantomType false . 
Parameter Price_Ф_cancelBuy : UExpression PhantomType false . 
Parameter Price_Ф_getDetails : UExpression DetailsInfo false . 
Parameter Price_Ф_getPrice : UExpression XInteger128 false . 
Parameter Price_Ф_getMinimumAmount : UExpression XInteger128 false . 
Parameter Price_Ф_getTonsCfg : UExpression TonsConfig false . 
(* Parameter Price_Ф_getSells : UExpression ( XDictArray ) false .  *)
(* Parameter Price_Ф_getBuys : UExpression ( XDictArray ) false .  *)
Parameter Price_Ф_getSellAmount : UExpression XInteger128 false . 
Parameter Price_Ф_getBuyAmount : UExpression XInteger128 false . 
Parameter Price_Ф__fallback : UExpression XInteger false . 
Parameter Price_Ф_onTip3LendOwnershipMinValue : UExpression XInteger128 false . 
Parameter Price_Ф_buyTip3MinValue : XInteger128 -> UExpression XInteger128 false . 
Parameter Price_Ф_verify_tip3_addr : XAddress -> XInteger256 -> XInteger256 -> UExpression XBool false . 
Parameter Price_Ф_expected_wallet_address : XInteger256 -> XInteger256 -> UExpression XInteger256 false . 
(* Parameter DPrice_Ф_on_sell_fail : XInteger -> ITONTokenWalletPtr -> UExpression OrderRetP false .  *)
(* Parameter dealer_Ф_extract_active_order : XMaybe OrderInfoXchgWithIdx -> XInteger128 -> XBool -> UExpression false .  *)
Parameter PriceXchg_Ф_onTip3LendOwnership : XInteger128 -> XInteger32 -> XInteger256 -> XInteger256 -> TvmCell -> XAddress -> UExpression OrderRet false . 
Parameter PriceXchg_Ф_processQueue : UExpression PhantomType false . 
Parameter PriceXchg_Ф_cancelSell : UExpression PhantomType false . 
Parameter PriceXchg_Ф_cancelBuy : UExpression PhantomType false . 
Parameter PriceXchg_Ф_getDetails : UExpression DetailsInfoXchg false . 
Parameter PriceXchg_Ф_getPriceNum : UExpression XInteger128 false . 
Parameter PriceXchg_Ф_getPriceDenum : UExpression XInteger128 false . 
Parameter PriceXchg_Ф_getMinimumAmount : UExpression XInteger128 false . 
Parameter PriceXchg_Ф_getTonsCfg : UExpression TonsConfig false . 
(* Parameter DPriceXchg_Ф_getSells : UExpression ( XDictArray ) false .  *)
(* Parameter DPriceXchg_Ф_getBuys : UExpression ( XDictArray ) false .  *)
Parameter PriceXchg_Ф_getSellAmount : UExpression XInteger128 false . 
Parameter PriceXchg_Ф_getBuyAmount : UExpression XInteger128 false . 
Parameter PriceXchg_Ф__fallback : UExpression XInteger false . 
Parameter PriceXchg_Ф_onTip3LendOwnershipMinValue : UExpression XInteger128 false . 
Parameter PriceXchg_Ф_verify_tip3_addr : Tip3Config -> XAddress -> XInteger256 -> XInteger256 -> UExpression XBool false . 
Parameter PriceXchg_Ф_expected_wallet_address : Tip3Config -> XInteger256 -> XInteger256 -> UExpression XInteger256 false . 
(* Parameter PriceXchg_Ф_on_ord_fail : XInteger -> ITONTokenWalletPtr -> UExpression OrderRetP false .  *)
Parameter TradingPair_Ф_onDeploy : UExpression XBool false . 
Parameter TradingPair_Ф_getFLeXAddr : UExpression XAddress false . 
Parameter TradingPair_Ф_getTip3Root : UExpression XAddress false . 
Parameter TradingPair_Ф__fallback : UExpression XInteger false . 
Parameter XchgPair_Ф_onDeploy : UExpression XBool false . 
Parameter XchgPair_Ф_getFLeXAddr : UExpression XAddress false . 
Parameter XchgPair_Ф_getTip3MajorRoot : UExpression XAddress false . 
Parameter XchgPair_Ф_getTip3MinorRoot : UExpression XAddress false . 
Parameter XchgPair_Ф__fallback : UExpression XInteger false . 
Parameter Ф_is_active_time : XInteger32 -> UExpression XBool false . 
Parameter Ф_calc_cost : XInteger128 -> XInteger128 -> UExpression ( XMaybe XInteger128 ) false . 
(* Parameter Ф_process_queue_impl : XAddress -> IFLeXNotifyPtr -> XInteger128 -> XInteger8 -> TonsConfig -> XInteger -> XInteger -> XInteger128 -> XQueue OrderInfo -> XInteger128 -> XQueue OrderInfo -> UExpression process_retP false .  *)
(* Parameter Ф_cancel_order_impl : XQueue OrderInfo -> addr_std_fixed -> XInteger128 -> XBool -> Grams -> Grams -> Grams -> UExpression ( XQueue OrderInfoP ) false .  *)
(* Parameter Ф_prepare_price_state_init_and_addr : DPrice -> TvmCell -> UExpression ( StateInit # XInteger256 )%sol false .  *)
Parameter Ф_minor_cost : XInteger128 -> RationalPrice -> UExpression ( XMaybe XInteger128 ) false . 
(* Parameter Ф_process_queue_impl : XAddress -> XAddress -> IFLeXNotifyPtr -> price_t -> XInteger8 -> TonsConfig -> XInteger -> XInteger -> XInteger128 -> XInteger128 -> UExpression process_retP false .  *)
(* Parameter Ф_cancel_order_impl : addr_std_fixed -> XInteger128 -> XBool -> Grams -> Grams -> Grams -> UExpression false .  *)
Parameter Ф_numerator : UExpression XInteger128 false . 
Parameter Ф_denominator : UExpression XInteger128 false . 
(* Parameter Ф_prepare_price_xchg_state_init_and_addr : DPriceXchg -> TvmCell -> UExpression ( StateInit # XInteger256 )%sol false . 
Parameter Ф_prepare_trading_pair_state_init_and_addr : DTradingPair -> TvmCell -> UExpression ( StateInit # XInteger256 )%sol false . 
Parameter Ф_prepare_xchg_pair_state_init_and_addr : DXchgPair -> TvmCell -> UExpression ( StateInit # XInteger256 )%sol false . 
 *)
End specFLeXSig.

End specFlexSpec.
