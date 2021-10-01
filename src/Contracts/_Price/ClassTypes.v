Require Import Coq.Program.Basics. 
Require Import String. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 

Require Import FinProof.ProgrammingWith.  
Require Import UMLang.SML_NG28. 
Require Import UMLang.SolidityNotations2. 
Require Import UMLang.ClassGenerator.ClassGenerator.
Require Import UrsusTVM.tvmFunc. 

Require Import Project.CommonTypes.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope xlist_scope.

Module PriceClassTypes (xt: XTypesSig) .
Import xt. 

(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 2 *) Definition TickTock := 
 ( XBool * 
 XBool )%type .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 2 *) Definition StateInit := 
 ( XMaybe XInteger * 
 XMaybe TickTock * 
 XMaybe XCell * 
 XMaybe XCell * 
 XMaybe XCell )%type .
(* 1 *) Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address .

(* 2 *) Definition addr_std_fixed := 
 ( XInteger8 * 
 XInteger256 )%type .
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 2 *) Definition TonsConfig := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 )%type .
(* 1 *) Inductive OrderRetFields := | OrderRet_ι_err_code | OrderRet_ι_processed | OrderRet_ι_enqueued .
(* 2 *) Definition OrderRet := 
 ( XInteger32 * 
 XInteger128 * 
 XInteger128 )%type .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
(* 2 *) Definition SellArgs := 
 ( XInteger128 * 
 XAddress )%type .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 2 *) Definition OrderInfo := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 addr_std_fixed * 
 addr_std_fixed * 
 XInteger32 )%type .
(* 1 *) Inductive DetailsInfoFields := | DetailsInfo_ι_price | DetailsInfo_ι_min_amount | DetailsInfo_ι_sell_amount | DetailsInfo_ι_buy_amount .
(* 2 *) Definition DetailsInfo := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 )%type .
(* 1 *) Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address .
(* 2 *) Definition Tip3Config := 
 ( XString * 
 XString * 
 XInteger8 * 
 XInteger256 * 
 XAddress )%type .

(* 1 *) Inductive dealerFields := | dealer_ι_tip3root_ | dealer_ι_notify_addr_ | dealer_ι_price_ | dealer_ι_deals_limit_ | dealer_ι_tons_cfg_ | dealer_ι_sells_amount_ | dealer_ι_sells_ | dealer_ι_buys_amount_ | dealer_ι_buys_ | dealer_ι_ret_ .
(* 2 *) Definition dealer := 
 ( XAddress * 
 XAddress * 
 XInteger128 * 
 XInteger * 
 TonsConfig * 
 XInteger128 * 
 XList OrderInfo * 
 XInteger128 * 
 XList OrderInfo * 
 XMaybe OrderRet )%type .
(* 1 *) Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_sells_ | process_ret_ι_buys_amount | process_ret_ι_buys_ | process_ret_ι_ret_ .
(* 2 *) Definition process_ret := 
 ( XInteger128 * 
 XList OrderInfo * 
 XInteger128 * 
 XList OrderInfo * 
 XMaybe OrderRet )%type .
(* 1 *) Inductive lend_ownership_infoFields := | lend_ownership_info_ι_owner | lend_ownership_info_ι_lend_balance | lend_ownership_info_ι_lend_finish_time .
(* 2 *) Definition lend_ownership_info := 
 ( XAddress * 
 TokensType * 
 XInteger32 )%type .
(* 1 *) Inductive allowance_infoFields := | allowance_info_ι_spender | allowance_info_ι_remainingTokens .
(* 2 *) Definition allowance_info := 
 ( XAddress * 
 TokensType )%type .
(* 1 *) Inductive TONTokenWalletFields := | TONTokenWallet_ι_name_ | TONTokenWallet_ι_symbol_ | TONTokenWallet_ι_decimals_ | TONTokenWallet_ι_balance_ | TONTokenWallet_ι_root_public_key_ | TONTokenWallet_ι_wallet_public_key_ | TONTokenWallet_ι_root_address_ | TONTokenWallet_ι_owner_address_ | TONTokenWallet_ι_lend_ownership_ | TONTokenWallet_ι_code_ | TONTokenWallet_ι_allowance_ | TONTokenWallet_ι_workchain_id_ .
(* 2 *) Definition TONTokenWallet := 
 ( XList XInteger8 * 
 XList XInteger8 * 
 XInteger8 * 
 TokensType * 
 XInteger256 * 
 XInteger256 * 
 XAddress * 
 XMaybe XAddress * 
 XMaybe lend_ownership_info * 
 XCell * 
 XMaybe allowance_info * 
 XInteger8 )%type .
(* 1 *) Inductive OrderInfoXchgFields := | OrderInfoXchg_ι_original_amount | OrderInfoXchg_ι_amount | OrderInfoXchg_ι_account | OrderInfoXchg_ι_tip3_wallet_provide | OrderInfoXchg_ι_tip3_wallet_receive | OrderInfoXchg_ι_client_addr | OrderInfoXchg_ι_order_finish_time .
(* 2 *) Definition OrderInfoXchg := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 addr_std_fixed * 
 addr_std_fixed * 
 addr_std_fixed * 
 XInteger32 )%type .


End PriceClassTypes .
 