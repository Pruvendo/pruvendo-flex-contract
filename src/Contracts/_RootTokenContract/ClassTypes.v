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

(* 1 *) Inductive ContractFields := | name_ | symbol_ | decimals_ | root_public_key_ | total_supply_ | total_granted_ | wallet_code_ | owner_address_ | start_balance_ .
(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 1 *) Inductive lend_recordFields := | lend_record_ι_lend_balance | lend_record_ι_lend_finish_time .
(* 1 *) Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address .
(* 1 *) Inductive allowance_infoFields := | allowance_info_ι_spender | allowance_info_ι_remainingTokens .
(* 1 *) Inductive DWrapperFields := | DWrapper_ι_name_ | DWrapper_ι_symbol_ | DWrapper_ι_decimals_ | DWrapper_ι_workchain_id_ | DWrapper_ι_root_public_key_ | DWrapper_ι_total_granted_ | DWrapper_ι_internal_wallet_code_ | DWrapper_ι_owner_address_ | DWrapper_ι_start_balance_ | DWrapper_ι_external_wallet_ .
(* 1 *) Inductive DXchgPairFields := | DXchgPair_ι_flex_addr_ | DXchgPair_ι_tip3_major_root_ | DXchgPair_ι_tip3_minor_root_ | DXchgPair_ι_min_amount_ | DXchgPair_ι_notify_addr_ .
(* 1 *) Inductive DTONTokenWalletExternalFields := | DTONTokenWalletExternal_ι_name_ | DTONTokenWalletExternal_ι_symbol_ | DTONTokenWalletExternal_ι_decimals_ | DTONTokenWalletExternal_ι_balance_ | DTONTokenWalletExternal_ι_root_public_key_ | DTONTokenWalletExternal_ι_wallet_public_key_ | DTONTokenWalletExternal_ι_root_address_ | DTONTokenWalletExternal_ι_owner_address_ | DTONTokenWalletExternal_ι_code_ | DTONTokenWalletExternal_ι_allowance_ | DTONTokenWalletExternal_ι_workchain_id_ .
(* 1 *) Inductive DTONTokenWalletInternalFields := | DTONTokenWalletInternal_ι_name_ | DTONTokenWalletInternal_ι_symbol_ | DTONTokenWalletInternal_ι_decimals_ | DTONTokenWalletInternal_ι_balance_ | DTONTokenWalletInternal_ι_root_public_key_ | DTONTokenWalletInternal_ι_wallet_public_key_ | DTONTokenWalletInternal_ι_root_address_ | DTONTokenWalletInternal_ι_owner_address_ | DTONTokenWalletInternal_ι_lend_ownership_ | DTONTokenWalletInternal_ι_code_ | DTONTokenWalletInternal_ι_workchain_id_ .
(* 1 *) Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .

(* 2 *) Definition ContractL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( GramsLRecord ) : Type ] .
Elpi GeneratePruvendoRecord ContractL ContractFields . 
 Opaque ContractLRecord . 

(* 2 *) Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 Opaque TickTockLRecord . 

(* 2 *) Definition lend_recordL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord lend_recordL lend_recordFields . 
 Opaque lend_recordLRecord . 

(* 2 *) Definition addr_std_fixedL : list Type := 
 [ ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ] .
Elpi GeneratePruvendoRecord addr_std_fixedL addr_std_fixedFields . 
 Opaque addr_std_fixedLRecord . 

(* 2 *) Definition allowance_infoL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord allowance_infoL allowance_infoFields . 
 Opaque allowance_infoLRecord . 

(* 2 *) Definition DWrapperL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( GramsLRecord ) : Type ; 
 ( ( XMaybe ITONTokenWalletPtrLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord DWrapperL DWrapperFields . 
 Opaque DWrapperLRecord . 

(* 2 *) Definition DXchgPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord DXchgPairL DXchgPairFields . 
 Opaque DXchgPairLRecord . 

(* 2 *) Definition DTONTokenWalletExternalL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( XCell ) : Type ; 
 ( ( XMaybe allowance_infoLRecord ) ) : Type ; 
 ( XInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletExternalL DTONTokenWalletExternalFields . 
 Opaque DTONTokenWalletExternalLRecord . 

(* 2 *) Definition DTONTokenWalletInternalL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( lend_ownership_mapLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( XInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletInternalL DTONTokenWalletInternalFields . 
 Opaque DTONTokenWalletInternalLRecord . 

(* 2 *) Definition Tip3ConfigL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord Tip3ConfigL Tip3ConfigFields . 
 Opaque Tip3ConfigLRecord . 

(* 2 *) Definition StateInitL : list Type := 
 [ ( ( XMaybe XInteger ) ) : Type ; 
 ( ( XMaybe TickTockLRecord ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
 Opaque StateInitLRecord . 


End ClassTypes .
 