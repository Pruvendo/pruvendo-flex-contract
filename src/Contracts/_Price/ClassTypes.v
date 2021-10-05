
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
Module Import CommonTypes := Types xt sm.

Local Open Scope xlist_scope.

(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock | TickTok_ι_1 .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 1 *) Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address | addr_std_fixed_ι_1 .
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 1 *) Inductive OrderRetFields := | OrderRet_ι_err_code | OrderRet_ι_processed | OrderRet_ι_enqueued .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet | SellArgs_ι_1 .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 1 *) Inductive DetailsInfoFields := | DetailsInfo_ι_price | DetailsInfo_ι_min_amount | DetailsInfo_ι_sell_amount | DetailsInfo_ι_buy_amount .
(* 1 *) Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address .
(* 1 *) Inductive dealerFields := | dealer_ι_tip3root_ | dealer_ι_notify_addr_ | dealer_ι_price_ | dealer_ι_deals_limit_ | dealer_ι_tons_cfg_ | dealer_ι_sells_amount_ | dealer_ι_buys_amount_ | dealer_ι_ret_ .
(* 1 *) Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_buys_amount | process_ret_ι_ret_ .
(* 1 *) Inductive lend_ownership_infoFields := | lend_ownership_info_ι_owner | lend_ownership_info_ι_lend_balance | lend_ownership_info_ι_lend_finish_time .
(* 1 *) Inductive allowance_infoFields := | allowance_info_ι_spender | allowance_info_ι_remainingTokens | allowance_info_ι_1 .
(* 1 *) Inductive TONTokenWalletFields := | TONTokenWallet_ι_name_ | TONTokenWallet_ι_symbol_ | TONTokenWallet_ι_decimals_ | TONTokenWallet_ι_balance_ | TONTokenWallet_ι_root_public_key_ | TONTokenWallet_ι_wallet_public_key_ | TONTokenWallet_ι_root_address_ | TONTokenWallet_ι_owner_address_ | TONTokenWallet_ι_lend_ownership_ | TONTokenWallet_ι_code_ | TONTokenWallet_ι_allowance_ | TONTokenWallet_ι_workchain_id_ .
(* 1 *) Inductive OrderInfoXchgFields := | OrderInfoXchg_ι_original_amount | OrderInfoXchg_ι_amount | OrderInfoXchg_ι_account | OrderInfoXchg_ι_tip3_wallet_provide | OrderInfoXchg_ι_tip3_wallet_receive | OrderInfoXchg_ι_client_addr | OrderInfoXchg_ι_order_finish_time .


(* 2 *) Definition TickTockStateL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ;
(XBool):Type ] .
Elpi GeneratePruvendoRecord TickTockStateL TickTockFields . 
 Opaque TickTockStateLRecord . 

(* 2 *) Definition StateInitStateL : list Type := 
 [ ( XMaybe XInteger ) : Type ; 
 ( XMaybe TickTockStateLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ] .
Elpi GeneratePruvendoRecord StateInitStateL StateInitFields . 
 Opaque StateInitStateLRecord . 

(* 2 *) Definition addr_std_fixedStateL : list Type := 
 [ ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ;
(XBool):Type ] . 
Elpi GeneratePruvendoRecord addr_std_fixedStateL addr_std_fixedFields . 
 Opaque addr_std_fixedStateLRecord . 

(* 2 *) Definition TonsConfigStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord TonsConfigStateL TonsConfigFields . 
 Opaque TonsConfigStateLRecord . 

(* 2 *) Definition OrderRetStateL : list Type := 
 [ ( XInteger32 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord OrderRetStateL OrderRetFields . 
 Opaque OrderRetStateLRecord . 

(* 2 *) Definition SellArgsStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ;
(XBool):Type] .
Elpi GeneratePruvendoRecord SellArgsStateL SellArgsFields . 
 Opaque SellArgsStateLRecord . 

(* 2 *) Definition OrderInfoStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( XInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord OrderInfoStateL OrderInfoFields . 
 Opaque OrderInfoStateLRecord . 

(* 2 *) Definition DetailsInfoStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord DetailsInfoStateL DetailsInfoFields . 
 Opaque DetailsInfoStateLRecord . 

(* 2 *) Definition Tip3ConfigStateL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord Tip3ConfigStateL Tip3ConfigFields . 
 Opaque Tip3ConfigStateLRecord . 

(* 2 *) Definition dealerStateL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger ) : Type ; 
 ( TonsConfigStateLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XMaybe OrderRetStateLRecord ) : Type ] .
Elpi GeneratePruvendoRecord dealerStateL dealerFields . 
 Opaque dealerStateLRecord . 

(* 2 *) Definition process_retStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XMaybe OrderRetStateLRecord ) : Type ] .
Elpi GeneratePruvendoRecord process_retStateL process_retFields . 
 Opaque process_retStateLRecord . 

(* 2 *) Definition lend_ownership_infoStateL : list Type := 
 [ ( XAddress ) : Type ; 
 ( TokensType ) : Type ; 
 ( XInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord lend_ownership_infoStateL lend_ownership_infoFields . 
 Opaque lend_ownership_infoStateLRecord . 

(* 2 *) Definition allowance_infoStateL : list Type := 
 [ ( XAddress ) : Type ; 
 ( TokensType ) : Type ;
(XBool):Type] .
Elpi GeneratePruvendoRecord allowance_infoStateL allowance_infoFields . 
 Opaque allowance_infoStateLRecord . 

(* 2 *) Definition TONTokenWalletStateL : list Type := 
 [ ( XList XInteger8 ) : Type ; 
 ( XList XInteger8 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TokensType ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XMaybe XAddress ) : Type ; 
 ( XMaybe lend_ownership_infoStateLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( XMaybe allowance_infoStateLRecord ) : Type ; 
 ( XInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord TONTokenWalletStateL TONTokenWalletFields . 
 Opaque TONTokenWalletStateLRecord . 

(* 2 *) Definition OrderInfoXchgStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( XInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord OrderInfoXchgStateL OrderInfoXchgFields . 
 Opaque OrderInfoXchgStateLRecord . 




End ClassTypes .
 