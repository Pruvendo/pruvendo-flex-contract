Require Import FinProof.ProgrammingWith. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonTypes.

Inductive lend_array_recordFields := | lend_array_record_ι_lend_addr | lend_array_record_ι_lend_balance | lend_array_record_ι_lend_finish_time .

Inductive DTONTokenWalletFields := 
| DTONTokenWallet_ι_name_ 
| DTONTokenWallet_ι_symbol_ 
| DTONTokenWallet_ι_decimals_ 
| DTONTokenWallet_ι_balance_ 
| DTONTokenWallet_ι_root_public_key_ 
| DTONTokenWallet_ι_wallet_public_key_ 
| DTONTokenWallet_ι_root_address_ 
| DTONTokenWallet_ι_owner_address_ 
| DTONTokenWallet_ι_lend_ownership_
| DTONTokenWallet_ι_code_ 
| DTONTokenWallet_ι_allowance_ 
| DTONTokenWallet_ι_workchain_id_ .

Inductive DTONTokenWalletExternalFields := | DTONTokenWalletExternal_ι_name_ | DTONTokenWalletExternal_ι_symbol_ | DTONTokenWalletExternal_ι_decimals_ | DTONTokenWalletExternal_ι_balance_ | DTONTokenWalletExternal_ι_root_public_key_ | DTONTokenWalletExternal_ι_wallet_public_key_ | DTONTokenWalletExternal_ι_root_address_ | DTONTokenWalletExternal_ι_owner_address_ | DTONTokenWalletExternal_ι_code_ | DTONTokenWalletExternal_ι_allowance_ | DTONTokenWalletExternal_ι_workchain_id_ .
Inductive DTONTokenWalletInternalFields := | DTONTokenWalletInternal_ι_name_ | DTONTokenWalletInternal_ι_symbol_ | DTONTokenWalletInternal_ι_decimals_ | DTONTokenWalletInternal_ι_balance_ | DTONTokenWalletInternal_ι_root_public_key_ | DTONTokenWalletInternal_ι_wallet_public_key_ | DTONTokenWalletInternal_ι_root_address_ | DTONTokenWalletInternal_ι_owner_address_ | DTONTokenWalletInternal_ι_lend_ownership_ | DTONTokenWalletInternal_ι_code_ | DTONTokenWalletInternal_ι_workchain_id_ .
Inductive details_infoFields := | details_info_ι_name | details_info_ι_symbol | details_info_ι_decimals | details_info_ι_balance | details_info_ι_root_public_key | details_info_ι_wallet_public_key | details_info_ι_root_address | details_info_ι_owner_address | details_info_ι_lend_ownership | details_info_ι_lend_balance | details_info_ι_code | details_info_ι_allowance | details_info_ι_workchain_id .
Inductive allowance_infoFields := | allowance_info_ι_spender | allowance_info_ι_remainingTokens .
Inductive lend_recordFields := | lend_record_ι_lend_balance | lend_record_ι_lend_finish_time .

Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Definition allowance_infoL : list Type := 
 [ ( address ) : Type ; 
   ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord allowance_infoL allowance_infoFields . 



Definition lend_recordL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord lend_recordL lend_recordFields . 

Definition DTONTokenWalletL : list Type := 
[ ( XString ) : Type ; 
( XString ) : Type ; 
( XUInteger8 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger256 ) : Type ; 
( XUInteger256 ) : Type ; 
( address ) : Type ; 
( ( XMaybe address ) ) : Type ; 
(XHMap addr_std_fixed lend_recordLRecord) : Type;
cell_ : Type ; 
( ( XMaybe allowance_infoLRecord ) ) : Type ; 
( XInteger (* XUInteger8 *) ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletL DTONTokenWalletFields . 

Definition lend_array_recordL : list Type := 
 [ ( address ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord lend_array_recordL lend_array_recordFields . 

Definition details_infoL : list Type := 
    [ ( XString ) : Type ; 
    ( XString ) : Type ; 
    ( XUInteger8 ) : Type ; 
    ( XUInteger128 ) : Type ; 
    ( XUInteger256 ) : Type ; 
    ( XUInteger256 ) : Type ; 
    ( address ) : Type ; 
    ( address ) : Type ; 
    ( ( XHMap XUInteger lend_array_recordLRecord ) ) : Type ; 
    ( XUInteger128 ) : Type ; 
    cell_ : Type ; 
    ( allowance_infoLRecord ) : Type ; 
    ( XInteger ) : Type ] .
Elpi GeneratePruvendoRecord details_infoL details_infoFields .     

Definition DTONTokenWalletExternalL : list Type := 
[ ( XString ) : Type ; 
( XString ) : Type ; 
( XUInteger8 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger256 ) : Type ; 
( XUInteger256 ) : Type ; 
( address ) : Type ; 
( ( XMaybe address ) ) : Type ; 
cell_ : Type ; 
( ( XMaybe allowance_infoLRecord ) ) : Type ; 
( XInteger (* XUInteger8 *) ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletExternalL DTONTokenWalletExternalFields . 

Definition DTONTokenWalletInternalL : list Type := 
[ ( XString ) : Type ; 
( XString ) : Type ; 
( XUInteger8 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger256 ) : Type ; 
( XUInteger256 ) : Type ; 
( address ) : Type ; 
( ( XMaybe address ) ) : Type ; 
( ( XHMap addr_std_fixed lend_recordLRecord ) ) : Type ;
cell_ : Type ; 
( XInteger (* XUInteger8 *) ) : Type ] . (* DTONTokenWalletExternal_ι_workchain_id_ *)
Elpi GeneratePruvendoRecord DTONTokenWalletInternalL DTONTokenWalletInternalFields . 

End ClassTypes .
 