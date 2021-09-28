Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdNotations.
Require Import UrsusStdLib.stdFuncNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.


Module FlexClientClassTypes (xt: XTypesSig) .

(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 1 *) Inductive anycast_infoFields := | anycast_info_ι_rewrite_pfx .
(* 1 *) Inductive addr_stdFields := | addr_std_ι_kind | addr_std_ι_Anycast | addr_std_ι_workchain_id | addr_std_ι_address .
(* 1 *) Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
(* 1 *) Inductive FlexBurnWalletArgsFields := | FlexBurnWalletArgs_ι_tons_value | FlexBurnWalletArgs_ι_out_pubkey | FlexBurnWalletArgs_ι_out_internal_owner | FlexBurnWalletArgs_ι_my_tip3_addr .
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 1 *) Inductive FLeXSellArgsAddrsFields := | FLeXSellArgsAddrs_ι_my_tip3_addr .
(* 1 *) Inductive FLeXSellArgsFields := | FLeXSellArgs_ι_price | FLeXSellArgs_ι_amount | FLeXSellArgs_ι_lend_finish_time | FLeXSellArgs_ι_min_amount | FLeXSellArgs_ι_deals_limit | FLeXSellArgs_ι_tons_value | FLeXSellArgs_ι_price_code | FLeXSellArgs_ι_addrs | FLeXSellArgs_ι_tip3_code | FLeXSellArgs_ι_tip3cfg .
(* 1 *) Inductive FLeXBuyArgsFields := | FLeXBuyArgs_ι_price | FLeXBuyArgs_ι_amount | FLeXBuyArgs_ι_order_finish_time | FLeXBuyArgs_ι_min_amount | FLeXBuyArgs_ι_deals_limit | FLeXBuyArgs_ι_deploy_value | FLeXBuyArgs_ι_price_code | FLeXBuyArgs_ι_my_tip3_addr | FLeXBuyArgs_ι_tip3_code | FLeXBuyArgs_ι_tip3cfg .
(* 1 *) Inductive FLeXXchgCfgsFields := | FLeXXchgCfgs_ι_major_tip3cfg | FLeXXchgCfgs_ι_minor_tip3cfg .
(* 1 *) Inductive FLeXXchgArgsFields := | FLeXXchgArgs_ι_sell | FLeXXchgArgs_ι_price_num | FLeXXchgArgs_ι_price_denum | FLeXXchgArgs_ι_amount | FLeXXchgArgs_ι_lend_amount | FLeXXchgArgs_ι_lend_finish_time | FLeXXchgArgs_ι_min_amount | FLeXXchgArgs_ι_deals_limit | FLeXXchgArgs_ι_tons_value | FLeXXchgArgs_ι_xchg_price_code | FLeXXchgArgs_ι_addrs | FLeXXchgArgs_ι_tip3_code | FLeXXchgArgs_ι_tip3cfgs .
(* 1 *) Inductive FLeXCancelArgsFields := | FLeXCancelArgs_ι_price | FLeXCancelArgs_ι_min_amount | FLeXCancelArgs_ι_deals_limit | FLeXCancelArgs_ι_value | FLeXCancelArgs_ι_price_code | FLeXCancelArgs_ι_tip3_code | FLeXCancelArgs_ι_tip3cfg .
(* 1 *) Inductive FLeXXchgCancelArgsFields := | FLeXXchgCancelArgs_ι_sell | FLeXXchgCancelArgs_ι_price_num | FLeXXchgCancelArgs_ι_price_denum | FLeXXchgCancelArgs_ι_min_amount | FLeXXchgCancelArgs_ι_deals_limit | FLeXXchgCancelArgs_ι_value | FLeXXchgCancelArgs_ι_xchg_price_code | FLeXXchgCancelArgs_ι_tip3_code | FLeXXchgCancelArgs_ι_tip3cfgs .
(* 1 *) Inductive XchgPairFields := | XchgPair_ι_flex_addr_ | XchgPair_ι_tip3_major_root_ | XchgPair_ι_tip3_minor_root_ | XchgPair_ι_deploy_value_ .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 1 *) Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address .
(* 1 *) Inductive PriceFields := | Price_ι_price_ | Price_ι_sells_amount_ | Price_ι_buys_amount_ | Price_ι_flex_ | Price_ι_min_amount_ | Price_ι_deals_limit_ | Price_ι_notify_addr_ | Price_ι_workchain_id_ | Price_ι_tons_cfg_ | Price_ι_tip3_code_ | Price_ι_tip3cfg_ .
(* 1 *) Inductive RationalPriceFields := | RationalPrice_ι_num | RationalPrice_ι_denum .
(* 1 *) Inductive PriceXchgFields := | PriceXchg_ι_price_ | PriceXchg_ι_sells_amount_ | PriceXchg_ι_buys_amount_ | PriceXchg_ι_flex_ | PriceXchg_ι_min_amount_ | PriceXchg_ι_deals_limit_ | PriceXchg_ι_notify_addr_ | PriceXchg_ι_workchain_id_ | PriceXchg_ι_tons_cfg_ | PriceXchg_ι_tip3_code_ | PriceXchg_ι_major_tip3cfg_ | PriceXchg_ι_minor_tip3cfg_ .
(* 1 *) Inductive TradingPairFields := | TradingPair_ι_flex_addr_ | TradingPair_ι_tip3_root_ | TradingPair_ι_deploy_value_ .
(* 1 *) Inductive PayloadArgsFields := | PayloadArgs_ι_sell | PayloadArgs_ι_amount | PayloadArgs_ι_receive_tip3_wallet | PayloadArgs_ι_client_addr .



End FlexClientClassTypes .
 