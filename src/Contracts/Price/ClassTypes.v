Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdFunc.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdFuncNotations.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import FinProof.ProgrammingWith.  
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) (* Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock . *)
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 1 *) (* Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address . *)
(* 1 *) (* Мы забрали отсюда тонс конфиг и оставили его в соммон тайпс *)
(* 1 *) Inductive OrderRetFields := | OrderRet_ι_err_code | OrderRet_ι_processed | OrderRet_ι_enqueued .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 1 *) Inductive DetailsInfoFields := | DetailsInfo_ι_price | DetailsInfo_ι_min_amount | DetailsInfo_ι_sell_amount | DetailsInfo_ι_buy_amount .
(* 1 *) (* Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address | Tip3Config_ι_workchain_id_. *)
(* 1 *) Inductive dealerFields := | dealer_ι_tip3root_ | dealer_ι_notify_addr_ | dealer_ι_price_ | dealer_ι_deals_limit_ | dealer_ι_tons_cfg_ | dealer_ι_sells_amount_ | dealer_ι_sells_ | dealer_ι_buys_amount_ | dealer_ι_buys_ | dealer_ι_ret_ .
(* 1 *) Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_sells_ | process_ret_ι_buys_amount | process_ret_ι_buys_ | process_ret_ι_ret_ .
(* 1 *) Inductive lend_ownership_infoFields := | lend_ownership_info_ι_owner | lend_ownership_info_ι_lend_balance | lend_ownership_info_ι_lend_finish_time .
(* 1 *) Inductive allowance_infoFields := | allowance_info_ι_spender | allowance_info_ι_remainingTokens .
(* 1 *) Inductive TONTokenWalletFields := | TONTokenWallet_ι_name_ | TONTokenWallet_ι_symbol_ | TONTokenWallet_ι_decimals_ | TONTokenWallet_ι_balance_ | TONTokenWallet_ι_root_public_key_ | TONTokenWallet_ι_wallet_public_key_ | TONTokenWallet_ι_root_address_ | TONTokenWallet_ι_owner_address_ | TONTokenWallet_ι_lend_ownership_ | TONTokenWallet_ι_code_ | TONTokenWallet_ι_allowance_ | TONTokenWallet_ι_workchain_id_ .
(* 1 *) Inductive OrderInfoXchgFields := | OrderInfoXchg_ι_original_amount | OrderInfoXchg_ι_amount | OrderInfoXchg_ι_account | OrderInfoXchg_ι_tip3_wallet_provide | OrderInfoXchg_ι_tip3_wallet_receive | OrderInfoXchg_ι_client_addr | OrderInfoXchg_ι_order_finish_time .
(* 1 *) Inductive DTONTokenWalletInternalFields := | DTONTokenWalletInternal_ι_name_ | DTONTokenWalletInternal_ι_symbol_ | DTONTokenWalletInternal_ι_decimals_ | DTONTokenWalletInternal_ι_balance_ | DTONTokenWalletInternal_ι_root_public_key_ | DTONTokenWalletInternal_ι_wallet_public_key_ | DTONTokenWalletInternal_ι_root_address_ | DTONTokenWalletInternal_ι_owner_address_ | DTONTokenWalletInternal_ι_lend_ownership_ | DTONTokenWalletInternal_ι_code_ | DTONTokenWalletInternal_ι_workchain_id_ .
(* 1 *) Inductive lend_recordFields := | lend_record_ι_lend_balance | lend_record_ι_lend_finish_time .

(* 2 *)(*  Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 Opaque TickTockLRecord . *)

(* 2 *) Definition StateInitL : list Type := 
 [ ( XMaybe XUInteger ) : Type ; 
 ( XMaybe TickTockLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
 Opaque StateInitLRecord . 

(* 2 *) (* Definition addr_std_fixedL : list Type := 
 [ ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ] .
Elpi GeneratePruvendoRecord addr_std_fixedL addr_std_fixedFields . 
 Opaque addr_std_fixedLRecord . *) 

(* 2 *) Definition OrderRetL : list Type := 
 [ ( XUInteger32 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord OrderRetL OrderRetFields . 
 Opaque OrderRetLRecord . 

(* 2 *) Definition SellArgsL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord SellArgsL SellArgsFields . 
 Opaque SellArgsLRecord . 

(* 2 *) Definition OrderInfoL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XUInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord OrderInfoL OrderInfoFields . 
 Opaque OrderInfoLRecord . 

(* 2 *) Definition DetailsInfoL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord DetailsInfoL DetailsInfoFields . 
 Opaque DetailsInfoLRecord . 

(* 2 *) (* Definition Tip3ConfigL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ; 
 ( XAddress ) : Type ;
 ( XUInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord Tip3ConfigL Tip3ConfigFields . 
 Opaque Tip3ConfigLRecord . *)

(* 2 *) Definition dealerL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress (* IFlexNotifyPtr *) ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( ( XMaybe OrderRetLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord dealerL dealerFields . 
 Opaque dealerLRecord . 

(* 2 *) Definition process_retL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( ( XMaybe OrderRetLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord process_retL process_retFields . 
 Opaque process_retLRecord .

(* 2 *) Definition lend_recordL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord lend_recordL lend_recordFields . 
 Opaque lend_recordLRecord . 

(* 2 *) Definition DTONTokenWalletInternalL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger256 ) : Type ; 
 ( XUInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( XHMap addr_std_fixedLRecord lend_recordLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( XUInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletInternalL DTONTokenWalletInternalFields . 
 Opaque DTONTokenWalletInternalLRecord . 

End ClassTypes .
 