Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdNotations.
Require Import UrsusStdLib.stdFuncNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.
Require Import FinProof.ProgrammingWith.  
Require Import UMLang.ClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.



(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock | TickTock_ι_a .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 1 *) Inductive anycast_infoFields := | anycast_info_ι_rewrite_pfx | anycast_info_ι_a | anycast_info_ι_b .
(* 1 *) Inductive addr_stdFields := | addr_std_ι_kind | addr_std_ι_Anycast | addr_std_ι_workchain_id | addr_std_ι_address .
(* 1 *) Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address | addr_std_fixed_ι_a .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet | SellArgs_ι_a .
(* 1 *) Inductive FlexBurnWalletArgsFields := | FlexBurnWalletArgs_ι_tons_value | FlexBurnWalletArgs_ι_out_pubkey | FlexBurnWalletArgs_ι_out_internal_owner | FlexBurnWalletArgs_ι_my_tip3_addr .
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 1 *) Inductive FlexSellArgsAddrsFields := | FlexSellArgsAddrs_ι_my_tip3_addr | FlexSellArgsAddrs_ι_a | FlexSellArgsAddrs_ι_foo .
(* 1 *) Inductive FlexSellArgsFields := | FlexSellArgs_ι_price | FlexSellArgs_ι_amount | FlexSellArgs_ι_lend_finish_time | FlexSellArgs_ι_min_amount | FlexSellArgs_ι_deals_limit | FlexSellArgs_ι_tons_value | FlexSellArgs_ι_price_code | FlexSellArgs_ι_addrs | FlexSellArgs_ι_tip3_code | FlexSellArgs_ι_tip3cfg .
(* 1 *) Inductive FlexBuyArgsFields := | FlexBuyArgs_ι_price | FlexBuyArgs_ι_amount | FlexBuyArgs_ι_order_finish_time | FlexBuyArgs_ι_min_amount | FlexBuyArgs_ι_deals_limit | FlexBuyArgs_ι_deploy_value | FlexBuyArgs_ι_price_code | FlexBuyArgs_ι_my_tip3_addr | FlexBuyArgs_ι_tip3_code | FlexBuyArgs_ι_tip3cfg .
(* 1 *) Inductive FlexXchgCfgsFields := | FlexXchgCfgs_ι_major_tip3cfg | FlexXchgCfgs_ι_minor_tip3cfg | FlexXchgCfgs_ι_a .
(* 1 *) Inductive FlexXchgArgsFields := | FlexXchgArgs_ι_sell | FlexXchgArgs_ι_price_num | FlexXchgArgs_ι_price_denum | FlexXchgArgs_ι_amount | FlexXchgArgs_ι_lend_amount | FlexXchgArgs_ι_lend_finish_time | FlexXchgArgs_ι_min_amount | FlexXchgArgs_ι_deals_limit | FlexXchgArgs_ι_tons_value | FlexXchgArgs_ι_xchg_price_code | FlexXchgArgs_ι_addrs | FlexXchgArgs_ι_tip3_code | FlexXchgArgs_ι_tip3cfgs .
(* 1 *) Inductive FlexCancelArgsFields := | FlexCancelArgs_ι_price | FlexCancelArgs_ι_min_amount | FlexCancelArgs_ι_deals_limit | FlexCancelArgs_ι_value | FlexCancelArgs_ι_price_code | FlexCancelArgs_ι_tip3_code | FlexCancelArgs_ι_tip3cfg .
(* 1 *) Inductive FlexXchgCancelArgsFields := | FlexXchgCancelArgs_ι_sell | FlexXchgCancelArgs_ι_price_num | FlexXchgCancelArgs_ι_price_denum | FlexXchgCancelArgs_ι_min_amount | FlexXchgCancelArgs_ι_deals_limit | FlexXchgCancelArgs_ι_value | FlexXchgCancelArgs_ι_xchg_price_code | FlexXchgCancelArgs_ι_tip3_code | FlexXchgCancelArgs_ι_tip3cfgs .
(* 1 *) Inductive XchgPairFields := | XchgPair_ι_flex_addr_ | XchgPair_ι_tip3_major_root_ | XchgPair_ι_tip3_minor_root_ | XchgPair_ι_deploy_value_ .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 1 *) Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address .
(* 1 *) Inductive DPriceFields := | DPrice_ι_price_ | DPrice_ι_sells_amount_ | DPrice_ι_buys_amount_ | DPrice_ι_flex_ 
                                  | DPrice_ι_min_amount_ | DPrice_ι_deals_limit_ | DPrice_ι_notify_addr_ 
                                  | DPrice_ι_workchain_id_ | DPrice_ι_tons_cfg_ | DPrice_ι_tip3_code_ | DPrice_ι_tip3cfg_ .
(* 1 *) Inductive RationalPriceFields := | RationalPrice_ι_num | RationalPrice_ι_denum | RationalPrice_ι_a .
(* 1 *) Inductive DPriceXchgFields := | DPriceXchg_ι_price_ | DPriceXchg_ι_sells_amount_ | DPriceXchg_ι_buys_amount_ 
                                      | DPriceXchg_ι_flex_ | DPriceXchg_ι_min_amount_ | DPriceXchg_ι_deals_limit_ 
                                      | DPriceXchg_ι_notify_addr_ | DPriceXchg_ι_workchain_id_ | DPriceXchg_ι_tons_cfg_ 
                                      | DPriceXchg_ι_tip3_code_ | DPriceXchg_ι_major_tip3cfg_ | DPriceXchg_ι_minor_tip3cfg_ .
(* 1 *) Inductive TradingPairFields := | TradingPair_ι_flex_addr_ | TradingPair_ι_tip3_root_ | TradingPair_ι_deploy_value_ .
(* 1 *) Inductive PayloadArgsFields := | PayloadArgs_ι_sell | PayloadArgs_ι_amount | PayloadArgs_ι_receive_tip3_wallet | PayloadArgs_ι_client_addr .


(* 2 *) Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord TickTockL TickTockFields . 
 
(* 2 *) Definition StateInitL : list Type := 
 [ ( XMaybe XInteger ) : Type ; 
 ( XMaybe TickTockLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ] .
GeneratePruvendoRecord StateInitL StateInitFields . 

(* 2 *) Definition anycast_infoL : list Type := 
 [ ( varuint32 ) : Type ; 
 ( XInteger ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord anycast_infoL anycast_infoFields . 

(* 2 *) Definition addr_stdL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XMaybe anycast_infoLRecord ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ] .
GeneratePruvendoRecord addr_stdL addr_stdFields . 
 
(* 2 *) Definition addr_std_fixedL : list Type := 
 [ ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord addr_std_fixedL addr_std_fixedFields . 
 
(* 2 *) Definition SellArgsL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord SellArgsL SellArgsFields . 

(* 2 *) Definition FlexBurnWalletArgsL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexBurnWalletArgsL FlexBurnWalletArgsFields . 
 
(* 2 *) Definition TonsConfigL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ] .
GeneratePruvendoRecord TonsConfigL TonsConfigFields . 
 
(* 2 *) Definition FlexSellArgsAddrsL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XInteger ) : Type ;
(XBool) : Type ] .
GeneratePruvendoRecord FlexSellArgsAddrsL FlexSellArgsAddrsFields . 
 
(* 2 *) Definition FlexSellArgsL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger32 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexSellArgsL FlexSellArgsFields . 
 
(* 2 *) Definition FlexBuyArgsL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger32 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexBuyArgsL FlexBuyArgsFields . 
 
(* 2 *) Definition FlexXchgCfgsL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord FlexXchgCfgsL FlexXchgCfgsFields . 
 
(* 2 *) Definition FlexXchgArgsL : list Type := 
 [ ( XBool ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger32 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexXchgArgsL FlexXchgArgsFields . 
 
(* 2 *) Definition FlexCancelArgsL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexCancelArgsL FlexCancelArgsFields . 
 
(* 2 *) Definition FlexXchgCancelArgsL : list Type := 
 [ ( XBool ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexXchgCancelArgsL FlexXchgCancelArgsFields . 

(* 2 *) Definition XchgPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
GeneratePruvendoRecord XchgPairL XchgPairFields . 

(* 2 *) Definition OrderInfoL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XInteger32 ) : Type ] .
GeneratePruvendoRecord OrderInfoL OrderInfoFields . 
 
(* 2 *) Definition Tip3ConfigL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord Tip3ConfigL Tip3ConfigFields .

(* 2 *) Definition DPriceL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( IFlexNotifyPtr ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ] .
Opaque Tip3ConfigLRecord.
GeneratePruvendoRecord DPriceL DPriceFields . 
 
(* 2 *) Definition RationalPriceL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord RationalPriceL RationalPriceFields . 
 
(* 2 *) Definition DPriceXchgL : list Type := 
 [ ( RationalPriceLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( IFlexNotifyPtr ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ] .
GeneratePruvendoRecord DPriceXchgL DPriceXchgFields . 
 
(* 2 *) Definition TradingPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
GeneratePruvendoRecord TradingPairL TradingPairFields . 
 
(* 2 *) Definition PayloadArgsL : list Type := 
 [ ( XBool ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord PayloadArgsL PayloadArgsFields . 


End ClassTypes .
 