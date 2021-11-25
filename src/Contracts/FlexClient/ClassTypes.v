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

(* 1 *) Inductive PayloadArgsFields := | PayloadArgs_ι_sell | PayloadArgs_ι_amount | PayloadArgs_ι_receive_tip3_wallet | PayloadArgs_ι_client_addr .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 1 *) Inductive RationalPriceFields := | RationalPrice_ι_num | RationalPrice_ι_denum .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
(* 1 *) Inductive DWrapperFields := | DWrapper_ι_name_ | DWrapper_ι_symbol_ | DWrapper_ι_decimals_ | DWrapper_ι_workchain_id_ | DWrapper_ι_root_public_key_ | DWrapper_ι_total_granted_ | DWrapper_ι_internal_wallet_code_ | DWrapper_ι_owner_address_ | DWrapper_ι_start_balance_ | DWrapper_ι_external_wallet_ .
(* 1 *) Inductive DTONTokenWalletInternalFields := | DTONTokenWalletInternal_ι_name_ | DTONTokenWalletInternal_ι_symbol_ | DTONTokenWalletInternal_ι_decimals_ | DTONTokenWalletInternal_ι_balance_ | DTONTokenWalletInternal_ι_root_public_key_ | DTONTokenWalletInternal_ι_wallet_public_key_ | DTONTokenWalletInternal_ι_root_address_ | DTONTokenWalletInternal_ι_owner_address_ | DTONTokenWalletInternal_ι_lend_ownership_ | DTONTokenWalletInternal_ι_code_ | DTONTokenWalletInternal_ι_workchain_id_ .
(* 1 *) Inductive lend_recordFields := | lend_record_ι_lend_balance | lend_record_ι_lend_finish_time .
(* 1 *) Inductive DFlexClientFields := | owner_ | trading_pair_code_ | xchg_pair_code_ | workchain_id_ | tons_cfg_ | flex_ | ext_wallet_code_ | flex_wallet_code_ | flex_wrapper_code_ .


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Locate XBool.

Opaque addr_std_fixedLRecord .
(* 2 *) Definition PayloadArgsL : list Type := 
 [ ( XBool ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ] .
Elpi GeneratePruvendoRecord PayloadArgsL PayloadArgsFields . 
Opaque PayloadArgsLRecord .
 
(* 2 *) Definition DFlexClientL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( XCell ) : Type ; 
 ( XCell ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XAddress ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ] .
Elpi GeneratePruvendoRecord DFlexClientL DFlexClientFields . 
 Opaque DFlexClientLRecord . 

 
(* 2 *) Definition OrderInfoL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XUInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord OrderInfoL OrderInfoFields . 
 Opaque OrderInfoLRecord . 

(* 2 *) Definition SellArgsL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord SellArgsL SellArgsFields . 
 Opaque SellArgsLRecord . 

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
 