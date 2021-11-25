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

(* 1 *) Inductive allowance_infoFields := | allowance_info_ι_spender | allowance_info_ι_remainingTokens .
(* 1 *) Inductive lend_recordFields := | lend_record_ι_lend_balance | lend_record_ι_lend_finish_time .
(* 1 *) Inductive lend_array_recordFields := | lend_array_record_ι_lend_addr | lend_array_record_ι_lend_balance | lend_array_record_ι_lend_finish_time .
(* 1 *) Inductive details_infoFields := | details_info_ι_name | details_info_ι_symbol | details_info_ι_decimals | details_info_ι_balance | details_info_ι_root_public_key | details_info_ι_wallet_public_key | details_info_ι_root_address | details_info_ι_owner_address | details_info_ι_lend_ownership | details_info_ι_lend_balance | details_info_ι_code | details_info_ι_allowance | details_info_ι_workchain_id .
(* 1 *) Inductive DTONTokenWalletExternalFields := | DTONTokenWalletExternal_ι_name_ | DTONTokenWalletExternal_ι_symbol_ | DTONTokenWalletExternal_ι_decimals_ | DTONTokenWalletExternal_ι_balance_ | DTONTokenWalletExternal_ι_root_public_key_ | DTONTokenWalletExternal_ι_wallet_public_key_ | DTONTokenWalletExternal_ι_root_address_ | DTONTokenWalletExternal_ι_owner_address_ | DTONTokenWalletExternal_ι_code_ | DTONTokenWalletExternal_ι_allowance_ | DTONTokenWalletExternal_ι_workchain_id_ .
(* 1 *) Inductive DTONTokenWalletInternalFields := | DTONTokenWalletInternal_ι_name_ | DTONTokenWalletInternal_ι_symbol_ | DTONTokenWalletInternal_ι_decimals_ | DTONTokenWalletInternal_ι_balance_ | DTONTokenWalletInternal_ι_root_public_key_ | DTONTokenWalletInternal_ι_wallet_public_key_ | DTONTokenWalletInternal_ι_root_address_ | DTONTokenWalletInternal_ι_owner_address_ | DTONTokenWalletExternal_ι_lend_ownership_map | DTONTokenWalletInternal_ι_code_ | DTONTokenWalletInternal_ι_workchain_id_ .
(* 1 *) (* Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library . *)
(* 1 *) Inductive DRootTokenContractFields := | DRootTokenContract_ι_name_ | DRootTokenContract_ι_symbol_ | DRootTokenContract_ι_decimals_ | DRootTokenContract_ι_root_public_key_ | DRootTokenContract_ι_total_supply_ | DRootTokenContract_ι_total_granted_ | DRootTokenContract_ι_wallet_code_ | DRootTokenContract_ι_owner_address_ | DRootTokenContract_ι_start_balance_ .
(* 1 *) (* Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address . *)
(* 1 *) Inductive DTONTokenWalletFields := | DTONTokenWallet_ι_name_ | DTONTokenWallet_ι_symbol_ | DTONTokenWallet_ι_decimals_ | DTONTokenWallet_ι_balance_ | DTONTokenWallet_ι_root_public_key_ | DTONTokenWallet_ι_wallet_public_key_ | DTONTokenWallet_ι_root_address_ | DTONTokenWallet_ι_owner_address_ | DTONTokenWallet_ι_code_ | DTONTokenWallet_ι_allowance_ | DTONTokenWallet_ι_workchain_id_ .

(* 2 *) Definition ContractL : list Type := 
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
Elpi GeneratePruvendoRecord ContractL ContractFields . 
Opaque ContractLRecord .

(* 2 *) Definition allowance_infoL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord allowance_infoL allowance_infoFields . 
 Opaque allowance_infoLRecord . 

(* 2 *) Definition lend_recordL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord lend_recordL lend_recordFields . 
 Opaque lend_recordLRecord . 

(* 2 *) Definition lend_array_recordL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord lend_array_recordL lend_array_recordFields . 
 Opaque lend_array_recordLRecord . 

(* (* 2 *) Definition addr_std_fixedL : list Type := 
 [ ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ] .
Elpi GeneratePruvendoRecord addr_std_fixedL addr_std_fixedFields . 
 Opaque addr_std_fixedLRecord .  *)

(* 2 *) Definition details_infoL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( ( XHMap XInteger lend_array_recordLRecord ) ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( allowance_infoLRecord ) : Type ; 
 ( XInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord details_infoL details_infoFields . 
 Opaque details_infoLRecord . 

(* 2 *) Definition ContractL : list Type := 
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
Elpi GeneratePruvendoRecord ContractL ContractFields . 
 Opaque ContractLRecord . 

(* 2 *) Definition DTONTokenWalletExternalL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( ( XHMap addr_std_fixedLRecord lend_recordLRecord ) ) : Type ;
 ( XCell ) : Type ; 
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
 ( XCell ) : Type ; 
 ( XInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletInternalL DTONTokenWalletInternalFields . 
 Opaque DTONTokenWalletInternalLRecord . 
(* 
(* 2 *) Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord ETONTokenWalletL ETONTokenWalletFields . 
 Opaque ETONTokenWalletLRecord . 

(* 2 *) Definition StateInitL : list Type := 
 [ ( ( XMaybe XInteger ) ) : Type ; 
 ( ( XMaybe TickTockLRecord ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 Opaque TickTockLRecord .  *)

(* 2 *) Definition DRootTokenContractL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( GramsLRecord ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
 Opaque StateInitLRecord . 



End ClassTypes .
 