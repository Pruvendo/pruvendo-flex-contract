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

(* 1 *) Inductive lend_array_recordFields := | lend_array_record_ι_lend_addr | lend_array_record_ι_lend_balance | lend_array_record_ι_lend_finish_time .
(* 1 *) Inductive DTONTokenWalletFields := | DTONTokenWallet_ι_name_ | DTONTokenWallet_ι_symbol_ | DTONTokenWallet_ι_decimals_ | DTONTokenWallet_ι_balance_ | DTONTokenWallet_ι_root_public_key_ | DTONTokenWallet_ι_wallet_public_key_ | DTONTokenWallet_ι_root_address_ | DTONTokenWallet_ι_owner_address_ | DTONTokenWallet_ι_code_ | DTONTokenWallet_ι_allowance_ | DTONTokenWallet_ι_workchain_id_ .
Inductive DTONTokenWalletExternalFields := | DTONTokenWalletExternal_ι_name_ | DTONTokenWalletExternal_ι_symbol_ | DTONTokenWalletExternal_ι_decimals_ | DTONTokenWalletExternal_ι_balance_ | DTONTokenWalletExternal_ι_root_public_key_ | DTONTokenWalletExternal_ι_wallet_public_key_ | DTONTokenWalletExternal_ι_root_address_ | DTONTokenWalletExternal_ι_owner_address_ | DTONTokenWalletExternal_ι_code_ | DTONTokenWalletExternal_ι_allowance_ | DTONTokenWalletExternal_ι_workchain_id_ .
Inductive DTONTokenWalletInternalFields := | DTONTokenWalletInternal_ι_name_ | DTONTokenWalletInternal_ι_symbol_ | DTONTokenWalletInternal_ι_decimals_ | DTONTokenWalletInternal_ι_balance_ | DTONTokenWalletInternal_ι_root_public_key_ | DTONTokenWalletInternal_ι_wallet_public_key_ | DTONTokenWalletInternal_ι_root_address_ | DTONTokenWalletInternal_ι_owner_address_ | DTONTokenWalletExternal_ι_lend_ownership_map | DTONTokenWalletInternal_ι_code_ | DTONTokenWalletInternal_ι_workchain_id_ .
Inductive details_infoFields := | details_info_ι_name | details_info_ι_symbol | details_info_ι_decimals | details_info_ι_balance | details_info_ι_root_public_key | details_info_ι_wallet_public_key | details_info_ι_root_address | details_info_ι_owner_address | details_info_ι_lend_ownership | details_info_ι_lend_balance | details_info_ι_code | details_info_ι_allowance | details_info_ι_workchain_id .
Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 2 *) Definition DTONTokenWalletL : list Type := 
[ ( XString ) : Type ; 
( XString ) : Type ; 
( XUInteger8 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger256 ) : Type ; 
( XUInteger256 ) : Type ; 
( XAddress ) : Type ; 
( ( XMaybe XAddress ) ) : Type ; 
( XCell ) : Type ; 
( ( XMaybe allowance_infoLRecord ) ) : Type ; 
( XUInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletL DTONTokenWalletFields . 
Opaque DTONTokenWalletLRecord .

(* 2 *) Definition lend_array_recordL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord lend_array_recordL lend_array_recordFields . 
 Opaque lend_array_recordLRecord . 

 Definition details_infoL : list Type := 
    [ ( XString ) : Type ; 
    ( XString ) : Type ; 
    ( XUInteger8 ) : Type ; 
    ( XUInteger128 ) : Type ; 
    ( XUInteger256 ) : Type ; 
    ( XUInteger256 ) : Type ; 
    ( XAddress ) : Type ; 
    ( XAddress ) : Type ; 
    ( ( XHMap XUInteger lend_array_recordLRecord ) ) : Type ; 
    ( XUInteger128 ) : Type ; 
    ( XCell ) : Type ; 
    ( allowance_infoLRecord ) : Type ; 
    ( XUInteger8 ) : Type ] .
   Elpi GeneratePruvendoRecord details_infoL details_infoFields . 
    Opaque details_infoLRecord . 

Definition DTONTokenWalletExternalL : list Type := 
[ ( XString ) : Type ; 
( XString ) : Type ; 
( XUInteger8 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger256 ) : Type ; 
( XUInteger256 ) : Type ; 
( XAddress ) : Type ; 
( ( XMaybe XAddress ) ) : Type ; 
( XCell ) : Type ; 
( ( XMaybe allowance_infoLRecord ) ) : Type ; 
( XUInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletExternalL DTONTokenWalletExternalFields . 
Opaque DTONTokenWalletExternalLRecord . 

(* 2 *) Definition DTONTokenWalletInternalL : list Type := 
[ ( XString ) : Type ; 
( XString ) : Type ; 
( XUInteger8 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger256 ) : Type ; 
( XUInteger256 ) : Type ; 
( XAddress ) : Type ; 
( ( XMaybe XAddress ) ) : Type ; 
( ( XHMap addr_std_fixedLRecord lend_recordLRecord ) ) : Type ;
( XCell ) : Type ; 
( XUInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletInternalL DTONTokenWalletInternalFields . 
Opaque DTONTokenWalletInternalLRecord . 

End ClassTypes .
 