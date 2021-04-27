Inductive Tip3Config := 
| Tip3Config_ι_name 
| Tip3Config_ι_symbol 
| Tip3Config_ι_decimals 
| Tip3Config_ι_root_public_key 
| Tip3Config_ι_root_address 
| Tip3Config_ι_code 

. 
Definition Tip3ConfigP := ( 
S * S * I8 * I256 * A * C )%type . 

 
Definition Tip3Config_get : forall (f: Tip3Config)(r: Tip3ConfigP ) , 
match f with 
| Tip3Config_ι_name => S 
| Tip3Config_ι_symbol => S 
| Tip3Config_ι_decimals => I8 
| Tip3Config_ι_root_public_key => I256 
| Tip3Config_ι_root_address => A 
| Tip3Config_ι_code => C 

end . 
 intros f r. 
 destruct r as  ((((( d1 , d2 ), d3), d4), d5), d6) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. 
 refine d6. Defined. 

 
Coercion Tip3Config_get : Tip3Config >-> Funclass. 

 
Inductive OrderRet := 
| OrderRet_ι_err_code 
| OrderRet_ι_processed 
| OrderRet_ι_enqueued 

. 
Definition OrderRetP := ( 
I32 * I128 * I128 )%type . 

 
Definition OrderRet_get : forall (f: OrderRet)(r: OrderRetP ) , 
match f with 
| OrderRet_ι_err_code => I32 
| OrderRet_ι_processed => I128 
| OrderRet_ι_enqueued => I128 

end . 
 intros f r. 
 destruct r as  (( d1 , d2 ), d3) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. Defined. 

 
Coercion OrderRet_get : OrderRet >-> Funclass. 

 
Inductive SellArgs := 
| SellArgs_ι_amount 
| SellArgs_ι_receive_wallet 

. 
Definition SellArgsP := ( 
I128 * addr_std_fixedP )%type . 

 
Definition SellArgs_get : forall (f: SellArgs)(r: SellArgsP ) , 
match f with 
| SellArgs_ι_amount => I128 
| SellArgs_ι_receive_wallet => addr_std_fixedP 

end . 
 intros f r. 
 destruct r as  ( d1 , d2 ) . 
 destruct f. 

 refine d1. 
 refine d2. Defined. 

 
Coercion SellArgs_get : SellArgs >-> Funclass. 

 
Inductive SellInfo := 
| SellInfo_ι_original_amount 
| SellInfo_ι_amount 
| SellInfo_ι_account 
| SellInfo_ι_tip3_wallet 
| SellInfo_ι_receive_wallet 
| SellInfo_ι_lend_finish_time 

. 
Definition SellInfoP := ( 
I128 * I128 * I128 * addr_std_fixedP * addr_std_fixedP * I32 )%type . 

 
Definition SellInfo_get : forall (f: SellInfo)(r: SellInfoP ) , 
match f with 
| SellInfo_ι_original_amount => I128 
| SellInfo_ι_amount => I128 
| SellInfo_ι_account => I128 
| SellInfo_ι_tip3_wallet => addr_std_fixedP 
| SellInfo_ι_receive_wallet => addr_std_fixedP 
| SellInfo_ι_lend_finish_time => I32 

end . 
 intros f r. 
 destruct r as  ((((( d1 , d2 ), d3), d4), d5), d6) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. 
 refine d6. Defined. 

 
Coercion SellInfo_get : SellInfo >-> Funclass. 

 
Inductive BuyInfo := 
| BuyInfo_ι_original_amount 
| BuyInfo_ι_amount 
| BuyInfo_ι_account 
| BuyInfo_ι_receive_tip3_wallet 
| BuyInfo_ι_answer_addr 

. 
Definition BuyInfoP := ( 
I128 * I128 * I128 * addr_std_fixedP * addr_std_fixedP )%type . 

 
Definition BuyInfo_get : forall (f: BuyInfo)(r: BuyInfoP ) , 
match f with 
| BuyInfo_ι_original_amount => I128 
| BuyInfo_ι_amount => I128 
| BuyInfo_ι_account => I128 
| BuyInfo_ι_receive_tip3_wallet => addr_std_fixedP 
| BuyInfo_ι_answer_addr => addr_std_fixedP 

end . 
 intros f r. 
 destruct r as  (((( d1 , d2 ), d3), d4), d5) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. Defined. 

 
Coercion BuyInfo_get : BuyInfo >-> Funclass. 

 
Inductive DetailsInfo := 
| DetailsInfo_ι_price 
| DetailsInfo_ι_min_amount 
| DetailsInfo_ι_sell_amount 
| DetailsInfo_ι_buy_amount 

. 
Definition DetailsInfoP := ( 
I128 * I128 * I128 * I128 )%type . 

 
Definition DetailsInfo_get : forall (f: DetailsInfo)(r: DetailsInfoP ) , 
match f with 
| DetailsInfo_ι_price => I128 
| DetailsInfo_ι_min_amount => I128 
| DetailsInfo_ι_sell_amount => I128 
| DetailsInfo_ι_buy_amount => I128 

end . 
 intros f r. 
 destruct r as  ((( d1 , d2 ), d3), d4) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. Defined. 

 
Coercion DetailsInfo_get : DetailsInfo >-> Funclass. 

 
Inductive DPrice := 
| DPrice_ι_price_ 
| DPrice_ι_sells_amount_ 
| DPrice_ι_buys_amount_ 
| DPrice_ι_stock_ 
| DPrice_ι_min_amount_ 
| DPrice_ι_deals_limit_ 
| DPrice_ι_notify_addr_ 
| DPrice_ι_workchain_id_ 
| DPrice_ι_tons_cfg_ 
| DPrice_ι_tip3cfg_ 

. 
Definition DPriceP := ( 
I128 * I128 * I128 * addr_std_fixedP * I128 * I8 * IStockNotifyPtrP * I8 * TonsConfigP * Tip3ConfigP )%type . 

 
Definition DPrice_get : forall (f: DPrice)(r: DPriceP ) , 
match f with 
| DPrice_ι_price_ => I128 
| DPrice_ι_sells_amount_ => I128 
| DPrice_ι_buys_amount_ => I128 
| DPrice_ι_stock_ => addr_std_fixedP 
| DPrice_ι_min_amount_ => I128 
| DPrice_ι_deals_limit_ => I8 
| DPrice_ι_notify_addr_ => IStockNotifyPtrP 
| DPrice_ι_workchain_id_ => I8 
| DPrice_ι_tons_cfg_ => TonsConfigP 
| DPrice_ι_tip3cfg_ => Tip3ConfigP 

end . 
 intros f r. 
 destruct r as  ((((((((( d1 , d2 ), d3), d4), d5), d6), d7), d8), d9), d10) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. 
 refine d6. 
 refine d7. 
 refine d8. 
 refine d9. 
 refine d10. Defined. 

 
Coercion DPrice_get : DPrice >-> Funclass. 

 
Inductive TonsConfig := 
| TonsConfig_ι_transfer_tip3 
| TonsConfig_ι_return_ownership 
| TonsConfig_ι_trading_pair_deploy 
| TonsConfig_ι_order_answer 
| TonsConfig_ι_process_queue 
| TonsConfig_ι_send_notify 

. 
Definition TonsConfigP := ( 
I128 * I128 * I128 * I128 * I128 * I128 )%type . 

 
Definition TonsConfig_get : forall (f: TonsConfig)(r: TonsConfigP ) , 
match f with 
| TonsConfig_ι_transfer_tip3 => I128 
| TonsConfig_ι_return_ownership => I128 
| TonsConfig_ι_trading_pair_deploy => I128 
| TonsConfig_ι_order_answer => I128 
| TonsConfig_ι_process_queue => I128 
| TonsConfig_ι_send_notify => I128 

end . 
 intros f r. 
 destruct r as  ((((( d1 , d2 ), d3), d4), d5), d6) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. 
 refine d6. Defined. 

 
Coercion TonsConfig_get : TonsConfig >-> Funclass. 

 
Inductive DStock := 
| DStock_ι_deployer_pubkey_ 
| DStock_ι_tons_cfg_ 
| DStock_ι_min_amount_ 
| DStock_ι_deals_limit_ 
| DStock_ι_notify_addr_ 

. 
Definition DStockP := ( 
I256 * TonsConfigP * I128 * I8 * A )%type . 

 
Definition DStock_get : forall (f: DStock)(r: DStockP ) , 
match f with 
| DStock_ι_deployer_pubkey_ => I256 
| DStock_ι_tons_cfg_ => TonsConfigP 
| DStock_ι_min_amount_ => I128 
| DStock_ι_deals_limit_ => I8 
| DStock_ι_notify_addr_ => A 

end . 
 intros f r. 
 destruct r as  (((( d1 , d2 ), d3), d4), d5) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. Defined. 

 
Coercion DStock_get : DStock >-> Funclass. 

 
Inductive DTradingPair := 
| DTradingPair_ι_stock_addr_ 
| DTradingPair_ι_tip3_root_ 
| DTradingPair_ι_deploy_value_ 

. 
Definition DTradingPairP := ( 
A * A * I128 )%type . 

 
Definition DTradingPair_get : forall (f: DTradingPair)(r: DTradingPairP ) , 
match f with 
| DTradingPair_ι_stock_addr_ => A 
| DTradingPair_ι_tip3_root_ => A 
| DTradingPair_ι_deploy_value_ => I128 

end . 
 intros f r. 
 destruct r as  (( d1 , d2 ), d3) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. Defined. 

 
Coercion DTradingPair_get : DTradingPair >-> Funclass. 

 
Inductive FLeXSellArgsAddrs := 
| FLeXSellArgsAddrs_ι_my_tip3_addr 
| FLeXSellArgsAddrs_ι_receive_wallet 

. 
Definition FLeXSellArgsAddrsP := ( 
A * A )%type . 

 
Definition FLeXSellArgsAddrs_get : forall (f: FLeXSellArgsAddrs)(r: FLeXSellArgsAddrsP ) , 
match f with 
| FLeXSellArgsAddrs_ι_my_tip3_addr => A 
| FLeXSellArgsAddrs_ι_receive_wallet => A 

end . 
 intros f r. 
 destruct r as  ( d1 , d2 ) . 
 destruct f. 

 refine d1. 
 refine d2. Defined. 

 
Coercion FLeXSellArgsAddrs_get : FLeXSellArgsAddrs >-> Funclass. 

 
Inductive FLeXSellArgs := 
| FLeXSellArgs_ι_price 
| FLeXSellArgs_ι_amount 
| FLeXSellArgs_ι_lend_finish_time 
| FLeXSellArgs_ι_min_amount 
| FLeXSellArgs_ι_deals_limit 
| FLeXSellArgs_ι_tons_value 
| FLeXSellArgs_ι_price_code 

. 
Definition FLeXSellArgsP := ( 
I128 * I128 * I32 * I128 * I8 * I128 * C )%type . 

 
Definition FLeXSellArgs_get : forall (f: FLeXSellArgs)(r: FLeXSellArgsP ) , 
match f with 
| FLeXSellArgs_ι_price => I128 
| FLeXSellArgs_ι_amount => I128 
| FLeXSellArgs_ι_lend_finish_time => I32 
| FLeXSellArgs_ι_min_amount => I128 
| FLeXSellArgs_ι_deals_limit => I8 
| FLeXSellArgs_ι_tons_value => I128 
| FLeXSellArgs_ι_price_code => C 

end . 
 intros f r. 
 destruct r as  (((((( d1 , d2 ), d3), d4), d5), d6), d7) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. 
 refine d6. 
 refine d7. Defined. 

 
Coercion FLeXSellArgs_get : FLeXSellArgs >-> Funclass. 

 
Inductive FLeXBuyArgs := 
| FLeXBuyArgs_ι_price 
| FLeXBuyArgs_ι_amount 
| FLeXBuyArgs_ι_min_amount 
| FLeXBuyArgs_ι_deals_limit 
| FLeXBuyArgs_ι_deploy_value 
| FLeXBuyArgs_ι_price_code 
| FLeXBuyArgs_ι_my_tip3_addr 

. 
Definition FLeXBuyArgsP := ( 
I128 * I128 * I128 * I8 * I128 * C * A )%type . 

 
Definition FLeXBuyArgs_get : forall (f: FLeXBuyArgs)(r: FLeXBuyArgsP ) , 
match f with 
| FLeXBuyArgs_ι_price => I128 
| FLeXBuyArgs_ι_amount => I128 
| FLeXBuyArgs_ι_min_amount => I128 
| FLeXBuyArgs_ι_deals_limit => I8 
| FLeXBuyArgs_ι_deploy_value => I128 
| FLeXBuyArgs_ι_price_code => C 
| FLeXBuyArgs_ι_my_tip3_addr => A 

end . 
 intros f r. 
 destruct r as  (((((( d1 , d2 ), d3), d4), d5), d6), d7) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. 
 refine d6. 
 refine d7. Defined. 

 
Coercion FLeXBuyArgs_get : FLeXBuyArgs >-> Funclass. 

 
Inductive FLeXCancelArgs := 
| FLeXCancelArgs_ι_price 
| FLeXCancelArgs_ι_min_amount 
| FLeXCancelArgs_ι_deals_limit 
| FLeXCancelArgs_ι_value 
| FLeXCancelArgs_ι_price_code 

. 
Definition FLeXCancelArgsP := ( 
I128 * I128 * I8 * I128 * C )%type . 

 
Definition FLeXCancelArgs_get : forall (f: FLeXCancelArgs)(r: FLeXCancelArgsP ) , 
match f with 
| FLeXCancelArgs_ι_price => I128 
| FLeXCancelArgs_ι_min_amount => I128 
| FLeXCancelArgs_ι_deals_limit => I8 
| FLeXCancelArgs_ι_value => I128 
| FLeXCancelArgs_ι_price_code => C 

end . 
 intros f r. 
 destruct r as  (((( d1 , d2 ), d3), d4), d5) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. Defined. 

 
Coercion FLeXCancelArgs_get : FLeXCancelArgs >-> Funclass. 

 
Inductive DFLeXClient := 
| DFLeXClient_ι_owner_ 
| DFLeXClient_ι_trading_pair_code_ 
| DFLeXClient_ι_workchain_id_ 
| DFLeXClient_ι_tons_cfg_ 
| DFLeXClient_ι_stock_ 
| DFLeXClient_ι_notify_addr_ 

. 
Definition DFLeXClientP := ( 
I256 * C * I8 * TonsConfigP * A * A )%type . 

 
Definition DFLeXClient_get : forall (f: DFLeXClient)(r: DFLeXClientP ) , 
match f with 
| DFLeXClient_ι_owner_ => I256 
| DFLeXClient_ι_trading_pair_code_ => C 
| DFLeXClient_ι_workchain_id_ => I8 
| DFLeXClient_ι_tons_cfg_ => TonsConfigP 
| DFLeXClient_ι_stock_ => A 
| DFLeXClient_ι_notify_addr_ => A 

end . 
 intros f r. 
 destruct r as  ((((( d1 , d2 ), d3), d4), d5), d6) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. 
 refine d6. Defined. 

 
Coercion DFLeXClient_get : DFLeXClient >-> Funclass. 

 
Inductive process_ret := 
| process_ret_ι_sells_amount 
| process_ret_ι_buys_amount 

. 
Definition process_retP := ( 
I128 * I128 )%type . 

 
Definition process_ret_get : forall (f: process_ret)(r: process_retP ) , 
match f with 
| process_ret_ι_sells_amount => I128 
| process_ret_ι_buys_amount => I128 

end . 
 intros f r. 
 destruct r as  ( d1 , d2 ) . 
 destruct f. 

 refine d1. 
 refine d2. Defined. 

 
Coercion process_ret_get : process_ret >-> Funclass. 

 
Inductive dealer := 
| dealer_ι_tip3root_ 
| dealer_ι_notify_addr_ 
| dealer_ι_price_ 
| dealer_ι_deals_limit_ 
| dealer_ι_tons_cfg_ 
| dealer_ι_sells_amount_ 
| dealer_ι_buys_amount_ 

. 
Definition dealerP := ( 
A * IStockNotifyPtrP * I128 * I * TonsConfigP * I128 * I128 )%type . 

 
Definition dealer_get : forall (f: dealer)(r: dealerP ) , 
match f with 
| dealer_ι_tip3root_ => A 
| dealer_ι_notify_addr_ => IStockNotifyPtrP 
| dealer_ι_price_ => I128 
| dealer_ι_deals_limit_ => I 
| dealer_ι_tons_cfg_ => TonsConfigP 
| dealer_ι_sells_amount_ => I128 
| dealer_ι_buys_amount_ => I128 

end . 
 intros f r. 
 destruct r as  (((((( d1 , d2 ), d3), d4), d5), d6), d7) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. 
 refine d5. 
 refine d6. 
 refine d7. Defined. 

 
Coercion dealer_get : dealer >-> Funclass. 

 
Inductive Stock := 
| Stock_ι_> 

. 
Definition StockP := ( 
TIMESTAMP_DELAYP )%type . 

 
Definition Stock_get : forall (f: Stock)(r: StockP ) , 
match f with 
| Stock_ι_> => TIMESTAMP_DELAYP 

end . 
 intros f r. 
 destruct r as  ( d1 , d2 ) . 
 destruct f. 

 refine d1. Defined. 

 
Coercion Stock_get : Stock >-> Funclass. 

 
Inductive FLeXClient := 
| FLeXClient_ι_> 
| FLeXClient_ι_) 
| FLeXClient_ι_) 
| FLeXClient_ι_} 

. 
Definition FLeXClientP := ( 
TIMESTAMP_DELAYP * price_codeP * std_addrP * std_addrP )%type . 

 
Definition FLeXClient_get : forall (f: FLeXClient)(r: FLeXClientP ) , 
match f with 
| FLeXClient_ι_> => TIMESTAMP_DELAYP 
| FLeXClient_ι_) => price_codeP 
| FLeXClient_ι_) => std_addrP 
| FLeXClient_ι_} => std_addrP 

end . 
 intros f r. 
 destruct r as  ((( d1 , d2 ), d3), d4) . 
 destruct f. 

 refine d1. 
 refine d2. 
 refine d3. 
 refine d4. Defined. 

 
Coercion FLeXClient_get : FLeXClient >-> Funclass. 

 
Class PruvendoRecord R F :=
{
  field_type: F -> Type;
  getPruvendoRecord: forall (f: F), R -> field_type f;
  setPruvendoRecord: forall (f: F), field_type f -> R -> R;
}. 
Definition Tip3Config_set : forall (f: Tip3Config)  
( v : match f with 
| Tip3Config_ι_name => S 
| Tip3Config_ι_symbol => S 
| Tip3Config_ι_decimals => I8 
| Tip3Config_ι_root_public_key => I256 
| Tip3Config_ι_root_address => A 
| Tip3Config_ι_code => C 

end) (r:  Tip3ConfigP ) , Tip3ConfigP. 
 intros. 
 destruct r as  ((((( d1 , d2 ), d3), d4), d5), d6) . 
 destruct f. 
refine (v, d2, d3, d4, d5, d6) .
 refine (d1, v, d3, d4, d5, d6) .
 refine (d1, d2, v, d4, d5, d6) .
 refine (d1, d2, d3, v, d5, d6) .
 refine (d1, d2, d3, d4, v, d6) .
 refine (d1, d2, d3, d4, d5, v) .
 Defined. 
Instance Tip3Config_set_Record : PruvendoRecord Tip3ConfigP Tip3Config :=
{
  field_type := fun f => match f with 
| Tip3Config_ι_name => S 
| Tip3Config_ι_symbol => S 
| Tip3Config_ι_decimals => I8 
| Tip3Config_ι_root_public_key => I256 
| Tip3Config_ι_root_address => A 
| Tip3Config_ι_code => C 

end;
  getPruvendoRecord := @Tip3Config ;
  setPruvendoRecord := @Tip3Config ;
}. 
Definition OrderRet_set : forall (f: OrderRet)  
( v : match f with 
| OrderRet_ι_err_code => I32 
| OrderRet_ι_processed => I128 
| OrderRet_ι_enqueued => I128 

end) (r:  OrderRetP ) , OrderRetP. 
 intros. 
 destruct r as  (( d1 , d2 ), d3) . 
 destruct f. 
refine (v, d2, d3) .
 refine (d1, v, d3) .
 refine (d1, d2, v) .
 Defined. 
Instance OrderRet_set_Record : PruvendoRecord OrderRetP OrderRet :=
{
  field_type := fun f => match f with 
| OrderRet_ι_err_code => I32 
| OrderRet_ι_processed => I128 
| OrderRet_ι_enqueued => I128 

end;
  getPruvendoRecord := @OrderRet ;
  setPruvendoRecord := @OrderRet ;
}. 
Definition SellArgs_set : forall (f: SellArgs)  
( v : match f with 
| SellArgs_ι_amount => I128 
| SellArgs_ι_receive_wallet => addr_std_fixedP 

end) (r:  SellArgsP ) , SellArgsP. 
 intros. 
 destruct r as  ( d1 , d2 ) . 
 destruct f. 
refine (v, d2) .
 refine (d1, v) .
 Defined. 
Instance SellArgs_set_Record : PruvendoRecord SellArgsP SellArgs :=
{
  field_type := fun f => match f with 
| SellArgs_ι_amount => I128 
| SellArgs_ι_receive_wallet => addr_std_fixedP 

end;
  getPruvendoRecord := @SellArgs ;
  setPruvendoRecord := @SellArgs ;
}. 
Definition SellInfo_set : forall (f: SellInfo)  
( v : match f with 
| SellInfo_ι_original_amount => I128 
| SellInfo_ι_amount => I128 
| SellInfo_ι_account => I128 
| SellInfo_ι_tip3_wallet => addr_std_fixedP 
| SellInfo_ι_receive_wallet => addr_std_fixedP 
| SellInfo_ι_lend_finish_time => I32 

end) (r:  SellInfoP ) , SellInfoP. 
 intros. 
 destruct r as  ((((( d1 , d2 ), d3), d4), d5), d6) . 
 destruct f. 
refine (v, d2, d3, d4, d5, d6) .
 refine (d1, v, d3, d4, d5, d6) .
 refine (d1, d2, v, d4, d5, d6) .
 refine (d1, d2, d3, v, d5, d6) .
 refine (d1, d2, d3, d4, v, d6) .
 refine (d1, d2, d3, d4, d5, v) .
 Defined. 
Instance SellInfo_set_Record : PruvendoRecord SellInfoP SellInfo :=
{
  field_type := fun f => match f with 
| SellInfo_ι_original_amount => I128 
| SellInfo_ι_amount => I128 
| SellInfo_ι_account => I128 
| SellInfo_ι_tip3_wallet => addr_std_fixedP 
| SellInfo_ι_receive_wallet => addr_std_fixedP 
| SellInfo_ι_lend_finish_time => I32 

end;
  getPruvendoRecord := @SellInfo ;
  setPruvendoRecord := @SellInfo ;
}. 
Definition BuyInfo_set : forall (f: BuyInfo)  
( v : match f with 
| BuyInfo_ι_original_amount => I128 
| BuyInfo_ι_amount => I128 
| BuyInfo_ι_account => I128 
| BuyInfo_ι_receive_tip3_wallet => addr_std_fixedP 
| BuyInfo_ι_answer_addr => addr_std_fixedP 

end) (r:  BuyInfoP ) , BuyInfoP. 
 intros. 
 destruct r as  (((( d1 , d2 ), d3), d4), d5) . 
 destruct f. 
refine (v, d2, d3, d4, d5) .
 refine (d1, v, d3, d4, d5) .
 refine (d1, d2, v, d4, d5) .
 refine (d1, d2, d3, v, d5) .
 refine (d1, d2, d3, d4, v) .
 Defined. 
Instance BuyInfo_set_Record : PruvendoRecord BuyInfoP BuyInfo :=
{
  field_type := fun f => match f with 
| BuyInfo_ι_original_amount => I128 
| BuyInfo_ι_amount => I128 
| BuyInfo_ι_account => I128 
| BuyInfo_ι_receive_tip3_wallet => addr_std_fixedP 
| BuyInfo_ι_answer_addr => addr_std_fixedP 

end;
  getPruvendoRecord := @BuyInfo ;
  setPruvendoRecord := @BuyInfo ;
}. 
Definition DetailsInfo_set : forall (f: DetailsInfo)  
( v : match f with 
| DetailsInfo_ι_price => I128 
| DetailsInfo_ι_min_amount => I128 
| DetailsInfo_ι_sell_amount => I128 
| DetailsInfo_ι_buy_amount => I128 

end) (r:  DetailsInfoP ) , DetailsInfoP. 
 intros. 
 destruct r as  ((( d1 , d2 ), d3), d4) . 
 destruct f. 
refine (v, d2, d3, d4) .
 refine (d1, v, d3, d4) .
 refine (d1, d2, v, d4) .
 refine (d1, d2, d3, v) .
 Defined. 
Instance DetailsInfo_set_Record : PruvendoRecord DetailsInfoP DetailsInfo :=
{
  field_type := fun f => match f with 
| DetailsInfo_ι_price => I128 
| DetailsInfo_ι_min_amount => I128 
| DetailsInfo_ι_sell_amount => I128 
| DetailsInfo_ι_buy_amount => I128 

end;
  getPruvendoRecord := @DetailsInfo ;
  setPruvendoRecord := @DetailsInfo ;
}. 
Definition DPrice_set : forall (f: DPrice)  
( v : match f with 
| DPrice_ι_price_ => I128 
| DPrice_ι_sells_amount_ => I128 
| DPrice_ι_buys_amount_ => I128 
| DPrice_ι_stock_ => addr_std_fixedP 
| DPrice_ι_min_amount_ => I128 
| DPrice_ι_deals_limit_ => I8 
| DPrice_ι_notify_addr_ => IStockNotifyPtrP 
| DPrice_ι_workchain_id_ => I8 
| DPrice_ι_tons_cfg_ => TonsConfigP 
| DPrice_ι_tip3cfg_ => Tip3ConfigP 

end) (r:  DPriceP ) , DPriceP. 
 intros. 
 destruct r as  ((((((((( d1 , d2 ), d3), d4), d5), d6), d7), d8), d9), d10) . 
 destruct f. 
refine (v, d2, d3, d4, d5, d6, d7, d8, d9, d10) .
 refine (d1, v, d3, d4, d5, d6, d7, d8, d9, d10) .
 refine (d1, d2, v, d4, d5, d6, d7, d8, d9, d10) .
 refine (d1, d2, d3, v, d5, d6, d7, d8, d9, d10) .
 refine (d1, d2, d3, d4, v, d6, d7, d8, d9, d10) .
 refine (d1, d2, d3, d4, d5, v, d7, d8, d9, d10) .
 refine (d1, d2, d3, d4, d5, d6, v, d8, d9, d10) .
 refine (d1, d2, d3, d4, d5, d6, d7, v, d9, d10) .
 refine (d1, d2, d3, d4, d5, d6, d7, d8, v, d10) .
 refine (d1, d2, d3, d4, d5, d6, d7, d8, d9, v) .
 Defined. 
Instance DPrice_set_Record : PruvendoRecord DPriceP DPrice :=
{
  field_type := fun f => match f with 
| DPrice_ι_price_ => I128 
| DPrice_ι_sells_amount_ => I128 
| DPrice_ι_buys_amount_ => I128 
| DPrice_ι_stock_ => addr_std_fixedP 
| DPrice_ι_min_amount_ => I128 
| DPrice_ι_deals_limit_ => I8 
| DPrice_ι_notify_addr_ => IStockNotifyPtrP 
| DPrice_ι_workchain_id_ => I8 
| DPrice_ι_tons_cfg_ => TonsConfigP 
| DPrice_ι_tip3cfg_ => Tip3ConfigP 

end;
  getPruvendoRecord := @DPrice ;
  setPruvendoRecord := @DPrice ;
}. 
Definition TonsConfig_set : forall (f: TonsConfig)  
( v : match f with 
| TonsConfig_ι_transfer_tip3 => I128 
| TonsConfig_ι_return_ownership => I128 
| TonsConfig_ι_trading_pair_deploy => I128 
| TonsConfig_ι_order_answer => I128 
| TonsConfig_ι_process_queue => I128 
| TonsConfig_ι_send_notify => I128 

end) (r:  TonsConfigP ) , TonsConfigP. 
 intros. 
 destruct r as  ((((( d1 , d2 ), d3), d4), d5), d6) . 
 destruct f. 
refine (v, d2, d3, d4, d5, d6) .
 refine (d1, v, d3, d4, d5, d6) .
 refine (d1, d2, v, d4, d5, d6) .
 refine (d1, d2, d3, v, d5, d6) .
 refine (d1, d2, d3, d4, v, d6) .
 refine (d1, d2, d3, d4, d5, v) .
 Defined. 
Instance TonsConfig_set_Record : PruvendoRecord TonsConfigP TonsConfig :=
{
  field_type := fun f => match f with 
| TonsConfig_ι_transfer_tip3 => I128 
| TonsConfig_ι_return_ownership => I128 
| TonsConfig_ι_trading_pair_deploy => I128 
| TonsConfig_ι_order_answer => I128 
| TonsConfig_ι_process_queue => I128 
| TonsConfig_ι_send_notify => I128 

end;
  getPruvendoRecord := @TonsConfig ;
  setPruvendoRecord := @TonsConfig ;
}. 
Definition DStock_set : forall (f: DStock)  
( v : match f with 
| DStock_ι_deployer_pubkey_ => I256 
| DStock_ι_tons_cfg_ => TonsConfigP 
| DStock_ι_min_amount_ => I128 
| DStock_ι_deals_limit_ => I8 
| DStock_ι_notify_addr_ => A 

end) (r:  DStockP ) , DStockP. 
 intros. 
 destruct r as  (((( d1 , d2 ), d3), d4), d5) . 
 destruct f. 
refine (v, d2, d3, d4, d5) .
 refine (d1, v, d3, d4, d5) .
 refine (d1, d2, v, d4, d5) .
 refine (d1, d2, d3, v, d5) .
 refine (d1, d2, d3, d4, v) .
 Defined. 
Instance DStock_set_Record : PruvendoRecord DStockP DStock :=
{
  field_type := fun f => match f with 
| DStock_ι_deployer_pubkey_ => I256 
| DStock_ι_tons_cfg_ => TonsConfigP 
| DStock_ι_min_amount_ => I128 
| DStock_ι_deals_limit_ => I8 
| DStock_ι_notify_addr_ => A 

end;
  getPruvendoRecord := @DStock ;
  setPruvendoRecord := @DStock ;
}. 
Definition DTradingPair_set : forall (f: DTradingPair)  
( v : match f with 
| DTradingPair_ι_stock_addr_ => A 
| DTradingPair_ι_tip3_root_ => A 
| DTradingPair_ι_deploy_value_ => I128 

end) (r:  DTradingPairP ) , DTradingPairP. 
 intros. 
 destruct r as  (( d1 , d2 ), d3) . 
 destruct f. 
refine (v, d2, d3) .
 refine (d1, v, d3) .
 refine (d1, d2, v) .
 Defined. 
Instance DTradingPair_set_Record : PruvendoRecord DTradingPairP DTradingPair :=
{
  field_type := fun f => match f with 
| DTradingPair_ι_stock_addr_ => A 
| DTradingPair_ι_tip3_root_ => A 
| DTradingPair_ι_deploy_value_ => I128 

end;
  getPruvendoRecord := @DTradingPair ;
  setPruvendoRecord := @DTradingPair ;
}. 
Definition FLeXSellArgsAddrs_set : forall (f: FLeXSellArgsAddrs)  
( v : match f with 
| FLeXSellArgsAddrs_ι_my_tip3_addr => A 
| FLeXSellArgsAddrs_ι_receive_wallet => A 

end) (r:  FLeXSellArgsAddrsP ) , FLeXSellArgsAddrsP. 
 intros. 
 destruct r as  ( d1 , d2 ) . 
 destruct f. 
refine (v, d2) .
 refine (d1, v) .
 Defined. 
Instance FLeXSellArgsAddrs_set_Record : PruvendoRecord FLeXSellArgsAddrsP FLeXSellArgsAddrs :=
{
  field_type := fun f => match f with 
| FLeXSellArgsAddrs_ι_my_tip3_addr => A 
| FLeXSellArgsAddrs_ι_receive_wallet => A 

end;
  getPruvendoRecord := @FLeXSellArgsAddrs ;
  setPruvendoRecord := @FLeXSellArgsAddrs ;
}. 
Definition FLeXSellArgs_set : forall (f: FLeXSellArgs)  
( v : match f with 
| FLeXSellArgs_ι_price => I128 
| FLeXSellArgs_ι_amount => I128 
| FLeXSellArgs_ι_lend_finish_time => I32 
| FLeXSellArgs_ι_min_amount => I128 
| FLeXSellArgs_ι_deals_limit => I8 
| FLeXSellArgs_ι_tons_value => I128 
| FLeXSellArgs_ι_price_code => C 

end) (r:  FLeXSellArgsP ) , FLeXSellArgsP. 
 intros. 
 destruct r as  (((((( d1 , d2 ), d3), d4), d5), d6), d7) . 
 destruct f. 
refine (v, d2, d3, d4, d5, d6, d7) .
 refine (d1, v, d3, d4, d5, d6, d7) .
 refine (d1, d2, v, d4, d5, d6, d7) .
 refine (d1, d2, d3, v, d5, d6, d7) .
 refine (d1, d2, d3, d4, v, d6, d7) .
 refine (d1, d2, d3, d4, d5, v, d7) .
 refine (d1, d2, d3, d4, d5, d6, v) .
 Defined. 
Instance FLeXSellArgs_set_Record : PruvendoRecord FLeXSellArgsP FLeXSellArgs :=
{
  field_type := fun f => match f with 
| FLeXSellArgs_ι_price => I128 
| FLeXSellArgs_ι_amount => I128 
| FLeXSellArgs_ι_lend_finish_time => I32 
| FLeXSellArgs_ι_min_amount => I128 
| FLeXSellArgs_ι_deals_limit => I8 
| FLeXSellArgs_ι_tons_value => I128 
| FLeXSellArgs_ι_price_code => C 

end;
  getPruvendoRecord := @FLeXSellArgs ;
  setPruvendoRecord := @FLeXSellArgs ;
}. 
Definition FLeXBuyArgs_set : forall (f: FLeXBuyArgs)  
( v : match f with 
| FLeXBuyArgs_ι_price => I128 
| FLeXBuyArgs_ι_amount => I128 
| FLeXBuyArgs_ι_min_amount => I128 
| FLeXBuyArgs_ι_deals_limit => I8 
| FLeXBuyArgs_ι_deploy_value => I128 
| FLeXBuyArgs_ι_price_code => C 
| FLeXBuyArgs_ι_my_tip3_addr => A 

end) (r:  FLeXBuyArgsP ) , FLeXBuyArgsP. 
 intros. 
 destruct r as  (((((( d1 , d2 ), d3), d4), d5), d6), d7) . 
 destruct f. 
refine (v, d2, d3, d4, d5, d6, d7) .
 refine (d1, v, d3, d4, d5, d6, d7) .
 refine (d1, d2, v, d4, d5, d6, d7) .
 refine (d1, d2, d3, v, d5, d6, d7) .
 refine (d1, d2, d3, d4, v, d6, d7) .
 refine (d1, d2, d3, d4, d5, v, d7) .
 refine (d1, d2, d3, d4, d5, d6, v) .
 Defined. 
Instance FLeXBuyArgs_set_Record : PruvendoRecord FLeXBuyArgsP FLeXBuyArgs :=
{
  field_type := fun f => match f with 
| FLeXBuyArgs_ι_price => I128 
| FLeXBuyArgs_ι_amount => I128 
| FLeXBuyArgs_ι_min_amount => I128 
| FLeXBuyArgs_ι_deals_limit => I8 
| FLeXBuyArgs_ι_deploy_value => I128 
| FLeXBuyArgs_ι_price_code => C 
| FLeXBuyArgs_ι_my_tip3_addr => A 

end;
  getPruvendoRecord := @FLeXBuyArgs ;
  setPruvendoRecord := @FLeXBuyArgs ;
}. 
Definition FLeXCancelArgs_set : forall (f: FLeXCancelArgs)  
( v : match f with 
| FLeXCancelArgs_ι_price => I128 
| FLeXCancelArgs_ι_min_amount => I128 
| FLeXCancelArgs_ι_deals_limit => I8 
| FLeXCancelArgs_ι_value => I128 
| FLeXCancelArgs_ι_price_code => C 

end) (r:  FLeXCancelArgsP ) , FLeXCancelArgsP. 
 intros. 
 destruct r as  (((( d1 , d2 ), d3), d4), d5) . 
 destruct f. 
refine (v, d2, d3, d4, d5) .
 refine (d1, v, d3, d4, d5) .
 refine (d1, d2, v, d4, d5) .
 refine (d1, d2, d3, v, d5) .
 refine (d1, d2, d3, d4, v) .
 Defined. 
Instance FLeXCancelArgs_set_Record : PruvendoRecord FLeXCancelArgsP FLeXCancelArgs :=
{
  field_type := fun f => match f with 
| FLeXCancelArgs_ι_price => I128 
| FLeXCancelArgs_ι_min_amount => I128 
| FLeXCancelArgs_ι_deals_limit => I8 
| FLeXCancelArgs_ι_value => I128 
| FLeXCancelArgs_ι_price_code => C 

end;
  getPruvendoRecord := @FLeXCancelArgs ;
  setPruvendoRecord := @FLeXCancelArgs ;
}. 
Definition DFLeXClient_set : forall (f: DFLeXClient)  
( v : match f with 
| DFLeXClient_ι_owner_ => I256 
| DFLeXClient_ι_trading_pair_code_ => C 
| DFLeXClient_ι_workchain_id_ => I8 
| DFLeXClient_ι_tons_cfg_ => TonsConfigP 
| DFLeXClient_ι_stock_ => A 
| DFLeXClient_ι_notify_addr_ => A 

end) (r:  DFLeXClientP ) , DFLeXClientP. 
 intros. 
 destruct r as  ((((( d1 , d2 ), d3), d4), d5), d6) . 
 destruct f. 
refine (v, d2, d3, d4, d5, d6) .
 refine (d1, v, d3, d4, d5, d6) .
 refine (d1, d2, v, d4, d5, d6) .
 refine (d1, d2, d3, v, d5, d6) .
 refine (d1, d2, d3, d4, v, d6) .
 refine (d1, d2, d3, d4, d5, v) .
 Defined. 
Instance DFLeXClient_set_Record : PruvendoRecord DFLeXClientP DFLeXClient :=
{
  field_type := fun f => match f with 
| DFLeXClient_ι_owner_ => I256 
| DFLeXClient_ι_trading_pair_code_ => C 
| DFLeXClient_ι_workchain_id_ => I8 
| DFLeXClient_ι_tons_cfg_ => TonsConfigP 
| DFLeXClient_ι_stock_ => A 
| DFLeXClient_ι_notify_addr_ => A 

end;
  getPruvendoRecord := @DFLeXClient ;
  setPruvendoRecord := @DFLeXClient ;
}. 
Definition process_ret_set : forall (f: process_ret)  
( v : match f with 
| process_ret_ι_sells_amount => I128 
| process_ret_ι_buys_amount => I128 

end) (r:  process_retP ) , process_retP. 
 intros. 
 destruct r as  ( d1 , d2 ) . 
 destruct f. 
refine (v, d2) .
 refine (d1, v) .
 Defined. 
Instance process_ret_set_Record : PruvendoRecord process_retP process_ret :=
{
  field_type := fun f => match f with 
| process_ret_ι_sells_amount => I128 
| process_ret_ι_buys_amount => I128 

end;
  getPruvendoRecord := @process_ret ;
  setPruvendoRecord := @process_ret ;
}. 
Definition dealer_set : forall (f: dealer)  
( v : match f with 
| dealer_ι_tip3root_ => A 
| dealer_ι_notify_addr_ => IStockNotifyPtrP 
| dealer_ι_price_ => I128 
| dealer_ι_deals_limit_ => I 
| dealer_ι_tons_cfg_ => TonsConfigP 
| dealer_ι_sells_amount_ => I128 
| dealer_ι_buys_amount_ => I128 

end) (r:  dealerP ) , dealerP. 
 intros. 
 destruct r as  (((((( d1 , d2 ), d3), d4), d5), d6), d7) . 
 destruct f. 
refine (v, d2, d3, d4, d5, d6, d7) .
 refine (d1, v, d3, d4, d5, d6, d7) .
 refine (d1, d2, v, d4, d5, d6, d7) .
 refine (d1, d2, d3, v, d5, d6, d7) .
 refine (d1, d2, d3, d4, v, d6, d7) .
 refine (d1, d2, d3, d4, d5, v, d7) .
 refine (d1, d2, d3, d4, d5, d6, v) .
 Defined. 
Instance dealer_set_Record : PruvendoRecord dealerP dealer :=
{
  field_type := fun f => match f with 
| dealer_ι_tip3root_ => A 
| dealer_ι_notify_addr_ => IStockNotifyPtrP 
| dealer_ι_price_ => I128 
| dealer_ι_deals_limit_ => I 
| dealer_ι_tons_cfg_ => TonsConfigP 
| dealer_ι_sells_amount_ => I128 
| dealer_ι_buys_amount_ => I128 

end;
  getPruvendoRecord := @dealer ;
  setPruvendoRecord := @dealer ;
}. 
Definition Stock_set : forall (f: Stock)  
( v : match f with 
| Stock_ι_> => TIMESTAMP_DELAYP 

end) (r:  StockP ) , StockP. 
 intros. 
 destruct r as  ( d1 , d2 ) . 
 destruct f. 
refine (v) .
 Defined. 
Instance Stock_set_Record : PruvendoRecord StockP Stock :=
{
  field_type := fun f => match f with 
| Stock_ι_> => TIMESTAMP_DELAYP 

end;
  getPruvendoRecord := @Stock ;
  setPruvendoRecord := @Stock ;
}. 
Definition FLeXClient_set : forall (f: FLeXClient)  
( v : match f with 
| FLeXClient_ι_> => TIMESTAMP_DELAYP 
| FLeXClient_ι_) => price_codeP 
| FLeXClient_ι_) => std_addrP 
| FLeXClient_ι_} => std_addrP 

end) (r:  FLeXClientP ) , FLeXClientP. 
 intros. 
 destruct r as  ((( d1 , d2 ), d3), d4) . 
 destruct f. 
refine (v, d2, d3, d4) .
 refine (d1, v, d3, d4) .
 refine (d1, d2, v, d4) .
 refine (d1, d2, d3, v) .
 Defined. 
Instance FLeXClient_set_Record : PruvendoRecord FLeXClientP FLeXClient :=
{
  field_type := fun f => match f with 
| FLeXClient_ι_> => TIMESTAMP_DELAYP 
| FLeXClient_ι_) => price_codeP 
| FLeXClient_ι_) => std_addrP 
| FLeXClient_ι_} => std_addrP 

end;
  getPruvendoRecord := @FLeXClient ;
  setPruvendoRecord := @FLeXClient ;
}. 
Notation "'{$$' r 'With' y ':=' v '$$}'" := (@setPruvendoRecord _ _ _ y v r) : struct_scope.
 
Lemma no_Tip3Config_eq : forall (f1 f2: Tip3Config) (v2: field_type f2) (r : Tip3ConfigP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma Tip3Config_eq : forall (f2: Tip3Config) (v2: field_type f2) (r : Tip3ConfigP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_OrderRet_eq : forall (f1 f2: OrderRet) (v2: field_type f2) (r : OrderRetP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma OrderRet_eq : forall (f2: OrderRet) (v2: field_type f2) (r : OrderRetP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_SellArgs_eq : forall (f1 f2: SellArgs) (v2: field_type f2) (r : SellArgsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma SellArgs_eq : forall (f2: SellArgs) (v2: field_type f2) (r : SellArgsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_SellInfo_eq : forall (f1 f2: SellInfo) (v2: field_type f2) (r : SellInfoP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma SellInfo_eq : forall (f2: SellInfo) (v2: field_type f2) (r : SellInfoP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_BuyInfo_eq : forall (f1 f2: BuyInfo) (v2: field_type f2) (r : BuyInfoP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma BuyInfo_eq : forall (f2: BuyInfo) (v2: field_type f2) (r : BuyInfoP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DetailsInfo_eq : forall (f1 f2: DetailsInfo) (v2: field_type f2) (r : DetailsInfoP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DetailsInfo_eq : forall (f2: DetailsInfo) (v2: field_type f2) (r : DetailsInfoP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DPrice_eq : forall (f1 f2: DPrice) (v2: field_type f2) (r : DPriceP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DPrice_eq : forall (f2: DPrice) (v2: field_type f2) (r : DPriceP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_TonsConfig_eq : forall (f1 f2: TonsConfig) (v2: field_type f2) (r : TonsConfigP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma TonsConfig_eq : forall (f2: TonsConfig) (v2: field_type f2) (r : TonsConfigP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DStock_eq : forall (f1 f2: DStock) (v2: field_type f2) (r : DStockP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DStock_eq : forall (f2: DStock) (v2: field_type f2) (r : DStockP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DTradingPair_eq : forall (f1 f2: DTradingPair) (v2: field_type f2) (r : DTradingPairP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DTradingPair_eq : forall (f2: DTradingPair) (v2: field_type f2) (r : DTradingPairP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_FLeXSellArgsAddrs_eq : forall (f1 f2: FLeXSellArgsAddrs) (v2: field_type f2) (r : FLeXSellArgsAddrsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma FLeXSellArgsAddrs_eq : forall (f2: FLeXSellArgsAddrs) (v2: field_type f2) (r : FLeXSellArgsAddrsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_FLeXSellArgs_eq : forall (f1 f2: FLeXSellArgs) (v2: field_type f2) (r : FLeXSellArgsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma FLeXSellArgs_eq : forall (f2: FLeXSellArgs) (v2: field_type f2) (r : FLeXSellArgsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_FLeXBuyArgs_eq : forall (f1 f2: FLeXBuyArgs) (v2: field_type f2) (r : FLeXBuyArgsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma FLeXBuyArgs_eq : forall (f2: FLeXBuyArgs) (v2: field_type f2) (r : FLeXBuyArgsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_FLeXCancelArgs_eq : forall (f1 f2: FLeXCancelArgs) (v2: field_type f2) (r : FLeXCancelArgsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma FLeXCancelArgs_eq : forall (f2: FLeXCancelArgs) (v2: field_type f2) (r : FLeXCancelArgsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DFLeXClient_eq : forall (f1 f2: DFLeXClient) (v2: field_type f2) (r : DFLeXClientP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DFLeXClient_eq : forall (f2: DFLeXClient) (v2: field_type f2) (r : DFLeXClientP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 

Lemma no_process_ret_eq : forall (f1 f2: process_ret) (v2: field_type f2) (r : process_retP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma process_ret_eq : forall (f2: process_ret) (v2: field_type f2) (r : process_retP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 



Lemma no_dealer_eq : forall (f1 f2: dealer) (v2: field_type f2) (r : dealerP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma dealer_eq : forall (f2: dealer) (v2: field_type f2) (r : dealerP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 

Lemma no_Stock_eq : forall (f1 f2: Stock) (v2: field_type f2) (r : StockP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma Stock_eq : forall (f2: Stock) (v2: field_type f2) (r : StockP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 

Lemma no_FLeXClient_eq : forall (f1 f2: FLeXClient) (v2: field_type f2) (r : FLeXClientP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma FLeXClient_eq : forall (f2: FLeXClient) (v2: field_type f2) (r : FLeXClientP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 

