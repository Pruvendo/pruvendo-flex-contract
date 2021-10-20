Require Import Coq.Program.Basics. 
Require Import String. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 


Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdNotations.
Require Import UrsusStdLib.stdFuncNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.
Require Import FinProof.ProgrammingWith.  
Require Import UMLang.ClassGenerator.ClassGenerator.

(* Require Export Project.CommonTypes. *)
Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
(* Module Export CommonTypes := Types xt sm. *)
Export xt.
Local Open Scope xlist_scope.

 
Inductive f1000  := | _int | _intIndex . 
 Definition t1000 := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord t1000 f1000  . 
 Opaque t1000Record . 
 
 Inductive f1001  := | _optcell | _optcellIndex . 
 Definition t1001 := [ ( XHMap (string*nat) ( XMaybe XCell ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord t1001 f1001  . 
 Opaque t1001Record . 
 
 Inductive f1010  := | _tpladdressaddress | _tpladdressaddressIndex . 
 Definition t1010 := [ ( XHMap (string*nat) ( XInteger * XInteger ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord t1010 f1010  . 
 Opaque t1010Record . 
 
 Inductive f1011  := | _uint256 | _uint256Index . 
 Definition t1011 := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord t1011 f1011  . 
 Opaque t1011Record . 
 
 Inductive f1100  := | _uint128 | _uint128Index . 
 Definition t1100 := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord t1100 f1100  . 
 Opaque t1100Record . 
 
 Inductive f1101  := | _uint8 | _uint8Index . 
 Definition t1101 := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord t1101 f1101  . 
 Opaque t1101Record . 
 
 Inductive f1110  := | _address | _addressIndex . 
 Definition t1110 := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord t1110 f1110  . 
 Opaque t1110Record . 
 
 Inductive f1111  := | _cell | _cellIndex . 
 Definition t1111 := [ ( XHMap (string*nat) XCell ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord t1111 f1111  . 
 Opaque t1111Record . 
 
 
 Inductive f_100 := | f1000_ | f1001_ . 
 Definition t100 := [ t1000Record ; t1001Record ] . 
 GeneratePruvendoRecord t100 f_100 . 
 Opaque t100Record . 
 
 Inductive f_101 := | f1010_ | f1011_ . 
 Definition t101 := [ t1010Record ; t1011Record ] . 
 GeneratePruvendoRecord t101 f_101 . 
 Opaque t101Record . 
 
 Inductive f_110 := | f1100_ | f1101_ . 
 Definition t110 := [ t1100Record ; t1101Record ] . 
 GeneratePruvendoRecord t110 f_110 . 
 Opaque t110Record . 
 
 Inductive f_111 := | f1110_ | f1111_ . 
 Definition t111 := [ t1110Record ; t1111Record ] . 
 GeneratePruvendoRecord t111 f_111 . 
 Opaque t111Record . 
 
 
 Inductive f_10 := | f100_ | f101_ . 
 Definition t10 := [ t100Record ; t101Record ] . 
 GeneratePruvendoRecord t10 f_10 . 
 Opaque t10Record . 
 
 Inductive f_11 := | f110_ | f111_ . 
 Definition t11 := [ t110Record ; t111Record ] . 
 GeneratePruvendoRecord t11 f_11 . 
 Opaque t11Record . 
 
 
 Inductive f_1 := | f10_ | f11_ . 
 Definition t1 := [ t10Record ; t11Record ] . 
 GeneratePruvendoRecord t1 f_1 . 
 Opaque t1Record . 








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


(* 2 *) Definition TickTockStateL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord TickTockStateL TickTockFields . 
 
(* 2 *) Definition StateInitStateL : list Type := 
 [ ( XMaybe XInteger ) : Type ; 
 ( XMaybe TickTockStateLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ] .
GeneratePruvendoRecord StateInitStateL StateInitFields . 

(* 2 *) Definition anycast_infoStateL : list Type := 
 [ ( varuint32 ) : Type ; 
 ( XInteger ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord anycast_infoStateL anycast_infoFields . 

(* 2 *) Definition addr_stdStateL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XMaybe anycast_infoStateLRecord ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ] .
GeneratePruvendoRecord addr_stdStateL addr_stdFields . 
 
(* 2 *) Definition addr_std_fixedStateL : list Type := 
 [ ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord addr_std_fixedStateL addr_std_fixedFields . 
 
(* 2 *) Definition SellArgsStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord SellArgsStateL SellArgsFields . 
 
(* 2 *) Definition FlexBurnWalletArgsStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexBurnWalletArgsStateL FlexBurnWalletArgsFields . 
 
(* 2 *) Definition TonsConfigStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ] .
GeneratePruvendoRecord TonsConfigStateL TonsConfigFields . 
 
(* 2 *) Definition FlexSellArgsAddrsStateL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XInteger ) : Type ;
(XBool) : Type ] .
GeneratePruvendoRecord FlexSellArgsAddrsStateL FlexSellArgsAddrsFields . 
 
(* 2 *) Definition FlexSellArgsStateL : list Type := 
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
GeneratePruvendoRecord FlexSellArgsStateL FlexSellArgsFields . 
 
(* 2 *) Definition FlexBuyArgsStateL : list Type := 
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
GeneratePruvendoRecord FlexBuyArgsStateL FlexBuyArgsFields . 
 
(* 2 *) Definition FlexXchgCfgsStateL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord FlexXchgCfgsStateL FlexXchgCfgsFields . 
 
(* 2 *) Definition FlexXchgArgsStateL : list Type := 
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
GeneratePruvendoRecord FlexXchgArgsStateL FlexXchgArgsFields . 
 
(* 2 *) Definition FlexCancelArgsStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexCancelArgsStateL FlexCancelArgsFields . 
 
(* 2 *) Definition FlexXchgCancelArgsStateL : list Type := 
 [ ( XBool ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexXchgCancelArgsStateL FlexXchgCancelArgsFields . 

(* 2 *) Definition XchgPairStateL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
GeneratePruvendoRecord XchgPairStateL XchgPairFields . 

(* 2 *) Definition OrderInfoStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( XInteger32 ) : Type ] .
GeneratePruvendoRecord OrderInfoStateL OrderInfoFields . 
 
(* 2 *) Definition Tip3ConfigStateL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord Tip3ConfigStateL Tip3ConfigFields .

(* 2 *) Definition DPriceStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( IFlexNotifyPtr ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TonsConfigStateLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigStateLRecord ) : Type ] .
Opaque Tip3ConfigStateLRecord.
GeneratePruvendoRecord DPriceStateL DPriceFields . 
 
(* 2 *) Definition RationalPriceStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger ) : Type ] .
GeneratePruvendoRecord RationalPriceStateL RationalPriceFields . 
 
(* 2 *) Definition DPriceXchgStateL : list Type := 
 [ ( RationalPriceStateLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( IFlexNotifyPtr ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TonsConfigStateLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigStateLRecord ) : Type ; 
 ( Tip3ConfigStateLRecord ) : Type ] .
GeneratePruvendoRecord DPriceXchgStateL DPriceXchgFields . 
 
(* 2 *) Definition TradingPairStateL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
GeneratePruvendoRecord TradingPairStateL TradingPairFields . 
 
(* 2 *) Definition PayloadArgsStateL : list Type := 
 [ ( XBool ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord PayloadArgsStateL PayloadArgsFields . 


End ClassTypes .
 