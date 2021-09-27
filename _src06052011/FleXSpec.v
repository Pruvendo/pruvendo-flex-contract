Parameter dealer_Ф_make_deal : SellInfoP -> BuyInfoP -> SMLExpression (S:=Ledger) false ( XBool # XBool # XInteger128 ) XInteger . 
Parameter dealer_Ф_process_queue : XInteger -> XInteger -> SMLExpression (S:=Ledger) false True XInteger . 
Parameter DPrice_Ф_onTip3LendOwnership : XInteger128 -> XInteger32 -> XInteger256 -> XInteger256 -> XCell -> XAddress -> SMLExpression (S:=Ledger) false OrderRetP XInteger . 
Parameter DPrice_Ф_buyTip3 : XInteger128 -> XAddress -> SMLExpression (S:=Ledger) false OrderRetP XInteger . 
Parameter DPrice_Ф_processQueue : SMLExpression (S:=Ledger) false True XInteger . 
Parameter DPrice_Ф_cancelSell : SMLExpression (S:=Ledger) false True XInteger . 
Parameter DPrice_Ф_cancelBuy : SMLExpression (S:=Ledger) false True XInteger . 
Parameter DPrice_Ф_getDetails : SMLExpression (S:=Ledger) false DetailsInfoP XInteger . 
Parameter DPrice_Ф_getPrice : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getMinimumAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getTonsCfg : SMLExpression (S:=Ledger) false TonsConfigP XInteger . 
Parameter DPrice_Ф_getSells : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getBuys : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getSellAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getBuyAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getPrice : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getMinimumAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getTonsCfg : SMLExpression (S:=Ledger) false TonsConfigP XInteger . 
Parameter DPrice_Ф_getSells : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getBuys : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getSellAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getBuyAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getMinimumAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getTonsCfg : SMLExpression (S:=Ledger) false TonsConfigP XInteger . 
Parameter DPrice_Ф_getSells : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getBuys : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getSellAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getBuyAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getTonsCfg : SMLExpression (S:=Ledger) false TonsConfigP XInteger . 
Parameter DPrice_Ф_getSells : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getBuys : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getSellAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getBuyAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getSells : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getBuys : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getSellAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getBuyAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getBuys : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger . 
Parameter DPrice_Ф_getSellAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getBuyAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getSellAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getBuyAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф_getBuyAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DPrice_Ф__fallback : XCell -> XSlice -> SMLExpression (S:=Ledger) false XInteger XInteger . 
Parameter DPrice_Ф_verify_tip3_addr : XAddress -> XInteger256 -> XInteger256 -> SMLExpression (S:=Ledger) false XBool XInteger . 
Parameter DPrice_Ф_expected_wallet_address : XInteger256 -> XInteger256 -> SMLExpression (S:=Ledger) false XInteger256 XInteger . 
Parameter DPrice_Ф_is_active_time : XInteger32 -> SMLExpression (S:=Ledger) false XBool XInteger . 
Parameter DPrice_Ф_on_sell_fail : XInteger -> ITONTokenWalletPtrP -> SMLExpression (S:=Ledger) false OrderRetP XInteger . 
Parameter DStock_Ф_constructor : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XAddress -> SMLExpression (S:=Ledger) false True XInteger . 
Parameter DStock_Ф_setPairCode : XCell -> SMLExpression (S:=Ledger) false True XInteger . 
Parameter DStock_Ф_setPriceCode : XCell -> SMLExpression (S:=Ledger) false True XInteger . 
Parameter DStock_Ф_isFullyInitialized : SMLExpression (S:=Ledger) false XBool XInteger . 
Parameter DStock_Ф_getTonsCfg : SMLExpression (S:=Ledger) false TonsConfigP XInteger . 
Parameter DStock_Ф_getTradingPairCode : SMLExpression (S:=Ledger) false XCell XInteger . 
Parameter DStock_Ф_isFullyInitialized : SMLExpression (S:=Ledger) false XBool XInteger . 
Parameter DStock_Ф_getTonsCfg : SMLExpression (S:=Ledger) false TonsConfigP XInteger . 
Parameter DStock_Ф_getTradingPairCode : SMLExpression (S:=Ledger) false XCell XInteger . 
Parameter DStock_Ф_getTonsCfg : SMLExpression (S:=Ledger) false TonsConfigP XInteger . 
Parameter DStock_Ф_getTradingPairCode : SMLExpression (S:=Ledger) false XCell XInteger . 
Parameter DStock_Ф_getTradingPairCode : SMLExpression (S:=Ledger) false XCell XInteger . 
Parameter DStock_Ф_getSellPriceCode : XAddress -> SMLExpression (S:=Ledger) false XCell XInteger . 
Parameter DStock_Ф_getXchgPriceCode : XAddress -> XAddress -> SMLExpression (S:=Ledger) false XCell XInteger . 
Parameter DStock_Ф_getSellTradingPair : XAddress -> SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DStock_Ф_getMinAmount : SMLExpression (S:=Ledger) false XInteger128 XInteger . 
Parameter DStock_Ф_getDealsLimit : SMLExpression (S:=Ledger) false XInteger8 XInteger . 
Parameter DStock_Ф_getNotifyAddr : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DStock_Ф_getDealsLimit : SMLExpression (S:=Ledger) false XInteger8 XInteger . 
Parameter DStock_Ф_getNotifyAddr : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DStock_Ф_getNotifyAddr : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DStock_Ф__fallback : XCell -> XSlice -> SMLExpression (S:=Ledger) false XInteger XInteger . 
Parameter DTradingPair_Ф_onDeploy : SMLExpression (S:=Ledger) false XBool XInteger . 
Parameter DTradingPair_Ф_getStockAddr : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DTradingPair_Ф_getTip3Root : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DTradingPair_Ф_onDeploy : SMLExpression (S:=Ledger) false XBool XInteger . 
Parameter DTradingPair_Ф_getStockAddr : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DTradingPair_Ф_getTip3Root : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DTradingPair_Ф_getStockAddr : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DTradingPair_Ф_getTip3Root : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DTradingPair_Ф_getTip3Root : SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DTradingPair_Ф__fallback : XCell -> XSlice -> SMLExpression (S:=Ledger) false XInteger XInteger . 
Parameter DFLeXClient_Ф_constructor : XInteger256 -> XCell -> SMLExpression (S:=Ledger) false True XInteger . 
Parameter DFLeXClient_Ф_setStockCfg : TonsConfigP -> XAddress -> XAddress -> SMLExpression (S:=Ledger) false True XInteger . 
Parameter DFLeXClient_Ф_deployTradingPair : XAddress -> XAddress -> XInteger128 -> XInteger128 -> SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DFLeXClient_Ф_deployPriceWithSell : XCell -> SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DFLeXClient_Ф_deployPriceWithBuy : XCell -> SMLExpression (S:=Ledger) false XAddress XInteger . 
Parameter DFLeXClient_Ф_cancelSellOrder : XCell -> SMLExpression (S:=Ledger) false True XInteger . 
Parameter DFLeXClient_Ф_cancelBuyOrder : XCell -> SMLExpression (S:=Ledger) false True XInteger . 
Parameter DFLeXClient_Ф_getOwner : SMLExpression (S:=Ledger) false XInteger256 XInteger . 
Parameter DFLeXClient_Ф__fallback : XCell -> XSlice -> SMLExpression (S:=Ledger) false XInteger XInteger . 
Parameter DFLeXClient_Ф_preparePrice : XInteger128 -> XInteger128 -> XInteger8 -> Tip3ConfigP -> XCell -> SMLExpression (S:=Ledger) false ( StateInitP # XAddress # XInteger256 ) XInteger . 
Parameter Ф_prepare_price_state_init_and_addr : DPriceP -> XCell -> SMLExpression (S:=Ledger) false ( StateInitP # XInteger256 ) XInteger . 
Parameter Ф_prepare_trading_pair_state_init_and_addr : DTradingPairP -> XCell -> SMLExpression (S:=Ledger) false ( StateInitP # XInteger256 ) XInteger . 
Parameter Ф_calc_cost : XInteger128 -> XInteger128 -> SMLExpression (S:=Ledger) false ( XMaybe XInteger128 ) XInteger . 
Parameter Ф_process_queue_impl : XAddress -> IStockNotifyPtrP -> XInteger128 -> XInteger8 -> TonsConfigP -> XInteger -> XInteger -> XInteger128 -> ( XQueue SellInfoP -> XInteger128 -> ( XQueue BuyInfoP -> SMLExpression (S:=Ledger) false process_retP XInteger . 

