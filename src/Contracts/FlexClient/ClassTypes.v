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

Locate XBool.

(* 1 *) (* Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address . *)
(* 1 *) (* Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock . *)
(* 1 *) (* Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address . *)
(* 1 *) Inductive PayloadArgsFields := | PayloadArgs_ι_sell | PayloadArgs_ι_amount | PayloadArgs_ι_receive_tip3_wallet | PayloadArgs_ι_client_addr .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 1 *) Inductive DXchgPairFields := | DXchgPair_ι_flex_addr_ | DXchgPair_ι_tip3_major_root_ | DXchgPair_ι_tip3_minor_root_ | DXchgPair_ι_min_amount_ | DXchgPair_ι_notify_addr_ .
(* 1 *) (* Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify . *)
(* 1 *) (* Inductive DTradingPairFields := 
| DTradingPair_ι_flex_addr_ 
| DTradingPair_ι_tip3_root_ 
| DTradingPair_ι_deploy_value_ 
| DTradingPair_ι_notify_addr_ . *)
(* 1 *) Inductive DPriceFields := | DPrice_ι_price_ | DPrice_ι_sells_amount_ | DPrice_ι_buys_amount_ | DPrice_ι_flex_ | DPrice_ι_min_amount_ | DPrice_ι_deals_limit_ | DPrice_ι_notify_addr_ | DPrice_ι_workchain_id_ | DPrice_ι_tons_cfg_ | DPrice_ι_tip3_code_ | DPrice_ι_tip3cfg_ | DPrice_ι_sells_ | DPrice_ι_buys_ .
(* 1 *) Inductive DPriceXchgFields := | DPriceXchg_ι_price_ | DPriceXchg_ι_sells_amount_ | DPriceXchg_ι_buys_amount_ | DPriceXchg_ι_flex_ | DPriceXchg_ι_min_amount_ | DPriceXchg_ι_deals_limit_ | DPriceXchg_ι_notify_addr_ | DPriceXchg_ι_workchain_id_ | DPriceXchg_ι_tons_cfg_ | DPriceXchg_ι_tip3_code_ | DPriceXchg_ι_major_tip3cfg_ | DPriceXchg_ι_minor_tip3cfg_ | DPriceXchg_ι_sells_ | DPriceXchg_ι_buys_ .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 1 *) Inductive OrderInfoXchgFields := | OrderInfoXchg_ι_original_amount | OrderInfoXchg_ι_amount | OrderInfoXchg_ι_account | OrderInfoXchg_ι_tip3_wallet_provide | OrderInfoXchg_ι_tip3_wallet_receive | OrderInfoXchg_ι_client_addr | OrderInfoXchg_ι_order_finish_time .
(* 1 *) Inductive RationalPriceFields := | RationalPrice_ι_num | RationalPrice_ι_denum .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
(* 1 *) Inductive DWrapperFields := | DWrapper_ι_name_ | DWrapper_ι_symbol_ | DWrapper_ι_decimals_ | DWrapper_ι_workchain_id_ | DWrapper_ι_root_public_key_ | DWrapper_ι_total_granted_ | DWrapper_ι_internal_wallet_code_ | DWrapper_ι_owner_address_ | DWrapper_ι_start_balance_ | DWrapper_ι_external_wallet_ .
(* 1 *) Inductive DTONTokenWalletInternalFields := | DTONTokenWalletInternal_ι_name_ | DTONTokenWalletInternal_ι_symbol_ | DTONTokenWalletInternal_ι_decimals_ | DTONTokenWalletInternal_ι_balance_ | DTONTokenWalletInternal_ι_root_public_key_ | DTONTokenWalletInternal_ι_wallet_public_key_ | DTONTokenWalletInternal_ι_root_address_ | DTONTokenWalletInternal_ι_owner_address_ | DTONTokenWalletInternal_ι_lend_ownership_ | DTONTokenWalletInternal_ι_code_ | DTONTokenWalletInternal_ι_workchain_id_ .
(* 1 *) Inductive lend_recordFields := | lend_record_ι_lend_balance | lend_record_ι_lend_finish_time .

(* 2 *) (* Definition Tip3ConfigL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord Tip3ConfigL Tip3ConfigFields . 
 Opaque Tip3ConfigLRecord .  *)
(* 2 *) (* Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 Opaque TickTockLRecord .  *)

(* 2 *) (* Definition addr_std_fixedL : list Type := 
 [ ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ] .
Elpi GeneratePruvendoRecord addr_std_fixedL addr_std_fixedFields . 
 Opaque addr_std_fixedLRecord .  *)

(* 2 *) Definition PayloadArgsL : list Type := 
 [ ( XBool ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ] .
Elpi GeneratePruvendoRecord PayloadArgsL PayloadArgsFields . 
 Opaque PayloadArgsLRecord . 

(* 2 *) Definition StateInitL : list Type := 
 [ ( ( XMaybe XUInteger ) ) : Type ; 
 ( ( XMaybe TickTockLRecord ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
 Opaque StateInitLRecord . 

(* 2 *) Definition DXchgPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord DXchgPairL DXchgPairFields . 
 Opaque DXchgPairLRecord . 

(* 2 *) (* Definition TonsConfigL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord TonsConfigL TonsConfigFields . 
 Opaque TonsConfigLRecord .  *)

(* 2 *) (* Definition DTradingPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ;
 ( XAddress ) :Type ] .
Elpi GeneratePruvendoRecord DTradingPairL DTradingPairFields . 
 Opaque DTradingPairLRecord . *)
 
(* 2 *) Definition OrderInfoL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XUInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord OrderInfoL OrderInfoFields . 
 Opaque OrderInfoLRecord . 

(* 2 *) Definition OrderInfoXchgL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XUInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord OrderInfoXchgL OrderInfoXchgFields . 
 Opaque OrderInfoXchgLRecord . 

(* 2 *) Definition SellArgsL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord SellArgsL SellArgsFields . 
 Opaque SellArgsLRecord . 

(* 2 *) Definition DPriceL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XAddress (* IFlexNotify *) ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord DPriceL DPriceFields . 
 Opaque DPriceLRecord .

(* 2 *) Definition RationalPriceL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord RationalPriceL RationalPriceFields . 
 Opaque RationalPriceLRecord . 

(* 2 *) Definition DWrapperL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( Grams ) : Type ; 
 ( ( XMaybe XAddress (* ITONTokenWalletPtrLRecord *) ) ) : Type ] .
Elpi GeneratePruvendoRecord DWrapperL DWrapperFields . 
 Opaque DWrapperLRecord . 

(* 2 *) Definition DPriceXchgL : list Type := 
 [ ( RationalPriceLRecord ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XAddress (* IFlexNotifyPtr *) ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord DPriceXchgL DPriceXchgFields . 
 Opaque DPriceXchgLRecord . 

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
 