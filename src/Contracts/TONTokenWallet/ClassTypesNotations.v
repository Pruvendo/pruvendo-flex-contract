Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.TONTokenWallet.ClassTypes.
Require Import Contracts.TONTokenWallet.Ledger.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.



Definition lend_array_record_ι_lend_addr_right {b} (x: URValue lend_array_recordLRecord b): URValue XAddress b :=
    || {x} ^^ {lend_array_record_ι_lend_addr} || : _.
    
Definition lend_array_record_ι_lend_addr_left (x: ULValue lend_array_recordLRecord): ULValue XAddress :=
    {{ {x} ^^ {lend_array_record_ι_lend_addr} }} : _.
    
Notation " a '↑' 'lend_array_record.lend_addr' " := ( lend_array_record_ι_lend_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'lend_array_record.lend_addr' " := ( lend_array_record_ι_lend_addr_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition lend_array_record_ι_lend_balance_right {b} (x: URValue lend_array_recordLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {lend_array_record_ι_lend_balance} || : _.
    
Definition lend_array_record_ι_lend_balance_left (x: ULValue lend_array_recordLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {lend_array_record_ι_lend_balance} }} : _.
    
Notation " a '↑' 'lend_array_record.lend_balance' " := ( lend_array_record_ι_lend_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'lend_array_record.lend_balance' " := ( lend_array_record_ι_lend_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition lend_array_record_ι_lend_finish_time_right {b} (x: URValue lend_array_recordLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {lend_array_record_ι_lend_finish_time} || : _.
    
Definition lend_array_record_ι_lend_finish_time_left (x: ULValue lend_array_recordLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {lend_array_record_ι_lend_finish_time} }} : _.
    
Notation " a '↑' 'lend_array_record.lend_finish_time' " := ( lend_array_record_ι_lend_finish_time_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'lend_array_record.lend_finish_time' " := ( lend_array_record_ι_lend_finish_time_left a ) (in custom ULValue at level 0) : ursus_scope.



Definition DTONTokenWallet_ι_name__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XString b :=
    || {x} ^^ {DTONTokenWallet_ι_name_} || : _.
    
Definition DTONTokenWallet_ι_name__left (x: ULValue DTONTokenWalletLRecord): ULValue XString :=
    {{ {x} ^^ {DTONTokenWallet_ι_name_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.name_' " := ( DTONTokenWallet_ι_name__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.name_' " := ( DTONTokenWallet_ι_name__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_symbol__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XString b :=
    || {x} ^^ {DTONTokenWallet_ι_symbol_} || : _.
    
Definition DTONTokenWallet_ι_symbol__left (x: ULValue DTONTokenWalletLRecord): ULValue XString :=
    {{ {x} ^^ {DTONTokenWallet_ι_symbol_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.symbol_' " := ( DTONTokenWallet_ι_symbol__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.symbol_' " := ( DTONTokenWallet_ι_symbol__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_decimals__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DTONTokenWallet_ι_decimals_} || : _.
    
Definition DTONTokenWallet_ι_decimals__left (x: ULValue DTONTokenWalletLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DTONTokenWallet_ι_decimals_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.decimals_' " := ( DTONTokenWallet_ι_decimals__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.decimals_' " := ( DTONTokenWallet_ι_decimals__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_balance__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DTONTokenWallet_ι_balance_} || : _.
    
Definition DTONTokenWallet_ι_balance__left (x: ULValue DTONTokenWalletLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DTONTokenWallet_ι_balance_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.balance_' " := ( DTONTokenWallet_ι_balance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.balance_' " := ( DTONTokenWallet_ι_balance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_root_public_key__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DTONTokenWallet_ι_root_public_key_} || : _.
    
Definition DTONTokenWallet_ι_root_public_key__left (x: ULValue DTONTokenWalletLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DTONTokenWallet_ι_root_public_key_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.root_public_key_' " := ( DTONTokenWallet_ι_root_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.root_public_key_' " := ( DTONTokenWallet_ι_root_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_wallet_public_key__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DTONTokenWallet_ι_wallet_public_key_} || : _.
    
Definition DTONTokenWallet_ι_wallet_public_key__left (x: ULValue DTONTokenWalletLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DTONTokenWallet_ι_wallet_public_key_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.wallet_public_key_' " := ( DTONTokenWallet_ι_wallet_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.wallet_public_key_' " := ( DTONTokenWallet_ι_wallet_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_root_address__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XAddress b :=
    || {x} ^^ {DTONTokenWallet_ι_root_address_} || : _.
    
Definition DTONTokenWallet_ι_root_address__left (x: ULValue DTONTokenWalletLRecord): ULValue XAddress :=
    {{ {x} ^^ {DTONTokenWallet_ι_root_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.root_address_' " := ( DTONTokenWallet_ι_root_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.root_address_' " := ( DTONTokenWallet_ι_root_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_owner_address__right {b} (x: URValue DTONTokenWalletLRecord b): URValue ( XMaybe XAddress ) b :=
    || {x} ^^ {DTONTokenWallet_ι_owner_address_} || : _.
    
Definition DTONTokenWallet_ι_owner_address__left (x: ULValue DTONTokenWalletLRecord): ULValue ( XMaybe XAddress ) :=
    {{ {x} ^^ {DTONTokenWallet_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.owner_address_' " := ( DTONTokenWallet_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.owner_address_' " := ( DTONTokenWallet_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_code__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XCell b :=
    || {x} ^^ {DTONTokenWallet_ι_code_} || : _.
    
Definition DTONTokenWallet_ι_code__left (x: ULValue DTONTokenWalletLRecord): ULValue XCell :=
    {{ {x} ^^ {DTONTokenWallet_ι_code_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.code_' " := ( DTONTokenWallet_ι_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.code_' " := ( DTONTokenWallet_ι_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_allowance__right {b} (x: URValue DTONTokenWalletLRecord b): URValue ( XMaybe allowance_infoLRecord ) b :=
    || {x} ^^ {DTONTokenWallet_ι_allowance_} || : _.
    
Definition DTONTokenWallet_ι_allowance__left (x: ULValue DTONTokenWalletLRecord): ULValue ( XMaybe allowance_infoLRecord ) :=
    {{ {x} ^^ {DTONTokenWallet_ι_allowance_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.allowance_' " := ( DTONTokenWallet_ι_allowance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.allowance_' " := ( DTONTokenWallet_ι_allowance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_workchain_id__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DTONTokenWallet_ι_workchain_id_} || : _.
    
Definition DTONTokenWallet_ι_workchain_id__left (x: ULValue DTONTokenWalletLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DTONTokenWallet_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.workchain_id_' " := ( DTONTokenWallet_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.workchain_id_' " := ( DTONTokenWallet_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_name__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XString b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_name_} || : _.
    
Definition DTONTokenWalletExternal_ι_name__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XString :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_name_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.name_' " := ( DTONTokenWalletExternal_ι_name__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.name_' " := ( DTONTokenWalletExternal_ι_name__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_symbol__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XString b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_symbol_} || : _.
    
Definition DTONTokenWalletExternal_ι_symbol__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XString :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_symbol_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.symbol_' " := ( DTONTokenWalletExternal_ι_symbol__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.symbol_' " := ( DTONTokenWalletExternal_ι_symbol__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_decimals__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_decimals_} || : _.
    
Definition DTONTokenWalletExternal_ι_decimals__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_decimals_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.decimals_' " := ( DTONTokenWalletExternal_ι_decimals__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.decimals_' " := ( DTONTokenWalletExternal_ι_decimals__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_balance__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_balance_} || : _.
    
Definition DTONTokenWalletExternal_ι_balance__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_balance_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.balance_' " := ( DTONTokenWalletExternal_ι_balance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.balance_' " := ( DTONTokenWalletExternal_ι_balance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_root_public_key__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_root_public_key_} || : _.
    
Definition DTONTokenWalletExternal_ι_root_public_key__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_root_public_key_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.root_public_key_' " := ( DTONTokenWalletExternal_ι_root_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.root_public_key_' " := ( DTONTokenWalletExternal_ι_root_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_wallet_public_key__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_wallet_public_key_} || : _.
    
Definition DTONTokenWalletExternal_ι_wallet_public_key__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_wallet_public_key_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.wallet_public_key_' " := ( DTONTokenWalletExternal_ι_wallet_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.wallet_public_key_' " := ( DTONTokenWalletExternal_ι_wallet_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_root_address__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XAddress b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_root_address_} || : _.
    
Definition DTONTokenWalletExternal_ι_root_address__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XAddress :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_root_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.root_address_' " := ( DTONTokenWalletExternal_ι_root_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.root_address_' " := ( DTONTokenWalletExternal_ι_root_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_owner_address__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue ( XMaybe XAddress ) b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_owner_address_} || : _.
    
Definition DTONTokenWalletExternal_ι_owner_address__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue ( XMaybe XAddress ) :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.owner_address_' " := ( DTONTokenWalletExternal_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.owner_address_' " := ( DTONTokenWalletExternal_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_code__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XCell b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_code_} || : _.
    
Definition DTONTokenWalletExternal_ι_code__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XCell :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_code_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.code_' " := ( DTONTokenWalletExternal_ι_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.code_' " := ( DTONTokenWalletExternal_ι_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_allowance__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue ( XMaybe allowance_infoLRecord ) b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_allowance_} || : _.
    
Definition DTONTokenWalletExternal_ι_allowance__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue ( XMaybe allowance_infoLRecord ) :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_allowance_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.allowance_' " := ( DTONTokenWalletExternal_ι_allowance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.allowance_' " := ( DTONTokenWalletExternal_ι_allowance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_workchain_id__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_workchain_id_} || : _.
    
Definition DTONTokenWalletExternal_ι_workchain_id__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.workchain_id_' " := ( DTONTokenWalletExternal_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.workchain_id_' " := ( DTONTokenWalletExternal_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.



Definition DTONTokenWalletInternal_ι_name__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue XString b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_name_} || : _.
    
Definition DTONTokenWalletInternal_ι_name__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XString :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_name_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.name_' " := ( DTONTokenWalletInternal_ι_name__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.name_' " := ( DTONTokenWalletInternal_ι_name__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_symbol__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue XString b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_symbol_} || : _.
    
Definition DTONTokenWalletInternal_ι_symbol__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XString :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_symbol_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.symbol_' " := ( DTONTokenWalletInternal_ι_symbol__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.symbol_' " := ( DTONTokenWalletInternal_ι_symbol__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_decimals__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_decimals_} || : _.
    
Definition DTONTokenWalletInternal_ι_decimals__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_decimals_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.decimals_' " := ( DTONTokenWalletInternal_ι_decimals__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.decimals_' " := ( DTONTokenWalletInternal_ι_decimals__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_balance__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_balance_} || : _.
    
Definition DTONTokenWalletInternal_ι_balance__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_balance_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.balance_' " := ( DTONTokenWalletInternal_ι_balance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.balance_' " := ( DTONTokenWalletInternal_ι_balance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_root_public_key__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_root_public_key_} || : _.
    
Definition DTONTokenWalletInternal_ι_root_public_key__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_root_public_key_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.root_public_key_' " := ( DTONTokenWalletInternal_ι_root_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.root_public_key_' " := ( DTONTokenWalletInternal_ι_root_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_wallet_public_key__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_wallet_public_key_} || : _.
    
Definition DTONTokenWalletInternal_ι_wallet_public_key__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_wallet_public_key_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.wallet_public_key_' " := ( DTONTokenWalletInternal_ι_wallet_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.wallet_public_key_' " := ( DTONTokenWalletInternal_ι_wallet_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_root_address__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue XAddress b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_root_address_} || : _.
    
Definition DTONTokenWalletInternal_ι_root_address__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XAddress :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_root_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.root_address_' " := ( DTONTokenWalletInternal_ι_root_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.root_address_' " := ( DTONTokenWalletInternal_ι_root_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_owner_address__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue ( XMaybe XAddress ) b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_owner_address_} || : _.
    
Definition DTONTokenWalletInternal_ι_owner_address__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue ( XMaybe XAddress ) :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.owner_address_' " := ( DTONTokenWalletInternal_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.owner_address_' " := ( DTONTokenWalletInternal_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_code__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue XCell b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_code_} || : _.
    
Definition DTONTokenWalletInternal_ι_code__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XCell :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_code_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.code_' " := ( DTONTokenWalletInternal_ι_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.code_' " := ( DTONTokenWalletInternal_ι_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_lend_ownership_map_right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue ( XHMap addr_std_fixedLRecord lend_recordLRecord ) b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_lend_ownership_map} || : _.
    
Definition DTONTokenWalletInternal_ι_lend_ownership_map_left (x: ULValue DTONTokenWalletInternalLRecord): ULValue ( XHMap addr_std_fixedLRecord lend_recordLRecord ) :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_allowance_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.lend_ownership_map' " := ( DTONTokenWalletInternal_ι_lend_ownership_map_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.lend_ownership_map' " := ( DTONTokenWalletInternal_ι_lend_ownership_map_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_workchain_id__right {b} (x: URValueDTONTokenWalletInternalLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_workchain_id_} || : _.
    
Definition DTONTokenWalletInternal_ι_workchain_id__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.workchain_id_' " := ( DTONTokenWalletInternal_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.workchain_id_' " := ( DTONTokenWalletInternal_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_name_right {b} (x: URValue details_infoLRecord b): URValue XString b :=
    || {x} ^^ {details_info_ι_name} || : _.
    
Definition details_info_ι_name_left (x: ULValue details_infodLRecord): ULValue XString :=
    {{ {x} ^^ {details_info_ι_name} }} : _.
    
Notation " a '↑' 'details_info.name' " := ( details_info_ι_name_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.name' " := ( details_info_ι_name_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_symbol_right {b} (x: URValue details_infoLRecord b): URValue XString b :=
    || {x} ^^ {details_info_ι_symbol} || : _.
    
Definition details_info_ι_symbol_left (x: ULValue details_infodLRecord): ULValue XString :=
    {{ {x} ^^ {details_info_ι_symbol} }} : _.
    
Notation " a '↑' 'details_info.symbol' " := ( details_info_ι_symbol_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.symbol' " := ( details_info_ι_symbol_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_decimals_right {b} (x: URValue details_infoLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {details_info_ι_decimals} || : _.
    
Definition details_info_ι_decimals_left (x: ULValue details_infodLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {details_info_ι_decimals} }} : _.
    
Notation " a '↑' 'details_info.decimals' " := ( details_info_ι_decimals_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.decimals' " := ( details_info_ι_decimals_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_balance_right {b} (x: URValue details_infoLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {details_info_ι_balance} || : _.
    
Definition details_info_ι_balance_left (x: ULValue details_infodLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {details_info_ι_balance} }} : _.
    
Notation " a '↑' 'details_info.balance' " := ( details_info_ι_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.balance' " := ( details_info_ι_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_root_public_key_right {b} (x: URValue details_infoLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {details_info_ι_root_public_key} || : _.
    
Definition details_info_ι_root_public_key_left (x: ULValue details_infodLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {details_info_ι_root_public_key} }} : _.
    
Notation " a '↑' 'details_info.root_public_key' " := ( details_info_ι_root_public_key_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.root_public_key' " := ( details_info_ι_root_public_key_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_wallet_public_key_right {b} (x: URValue details_infoLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {details_info_ι_wallet_public_key} || : _.
    
Definition details_info_ι_wallet_public_key_left (x: ULValue details_infodLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {details_info_ι_wallet_public_key} }} : _.
    
Notation " a '↑' 'details_info.wallet_public_key' " := ( details_info_ι_wallet_public_key_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.wallet_public_key' " := ( details_info_ι_wallet_public_key_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_root_address_right {b} (x: URValue details_infoLRecord b): URValue XAddress b :=
    || {x} ^^ {details_info_ι_root_address} || : _.
    
Definition details_info_ι_root_address_left (x: ULValue details_infodLRecord): ULValue XAddress :=
    {{ {x} ^^ {details_info_ι_root_address} }} : _.
    
Notation " a '↑' 'details_info.root_address' " := ( details_info_ι_root_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.root_address' " := ( details_info_ι_root_address_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_owner_address_right {b} (x: URValue details_infoLRecord b): URValue XAddress b :=
    || {x} ^^ {details_info_ι_owner_address} || : _.
    
Definition details_info_ι_owner_address_left (x: ULValue details_infodLRecord): ULValue XAddress :=
    {{ {x} ^^ {details_info_ι_owner_address} }} : _.
    
Notation " a '↑' 'details_info.owner_address' " := ( details_info_ι_owner_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.owner_address' " := ( details_info_ι_owner_address_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_lend_ownership_right {b} (x: URValue details_infoLRecord b): URValue ( XHMap XUInteger lend_array_recordLRecord ) b :=
    || {x} ^^ {details_info_ι_lend_ownership} || : _.
    
Definition details_info_ι_lend_ownership_left (x: ULValue details_infodLRecord): ULValue ( XHMap XUInteger lend_array_recordLRecord ) :=
    {{ {x} ^^ {details_info_ι_lend_ownership} }} : _.
    
Notation " a '↑' 'details_info.lend_ownership' " := ( details_info_ι_lend_ownership_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.lend_ownership' " := ( details_info_ι_lend_ownership_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_lend_balance_right {b} (x: URValue details_infoLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {details_info_ι_lend_balance} || : _.
    
Definition details_info_ι_lend_balance_left (x: ULValue details_infodLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {details_info_ι_lend_balance} }} : _.
    
Notation " a '↑' 'details_info.lend_balance' " := ( details_info_ι_lend_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.lend_balance' " := ( details_info_ι_lend_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_code_right {b} (x: URValue details_infoLRecord b): URValue XCell b :=
    || {x} ^^ {details_info_ι_code} || : _.
    
Definition details_info_ι_code_left (x: ULValue details_infodLRecord): ULValue XCell :=
    {{ {x} ^^ {details_info_ι_code} }} : _.
    
Notation " a '↑' 'details_info.code' " := ( details_info_ι_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.code' " := ( details_info_ι_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_allowance_right {b} (x: URValue details_infoLRecord b): URValue allowance_infoLRecord b :=
    || {x} ^^ {details_info_ι_allowance} || : _.
    
Definition details_info_ι_allowance_left (x: ULValue details_infodLRecord): ULValue allowance_infoLRecord :=
    {{ {x} ^^ {details_info_ι_allowance} }} : _.
    
Notation " a '↑' 'details_info.allowance' " := ( details_info_ι_allowance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.allowance' " := ( details_info_ι_allowance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_workchain_id_right {b} (x: URValue details_infoLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {details_info_ι_workchain_id} || : _.
    
Definition details_info_ι_workchain_id_left (x: ULValue details_infodLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {details_info_ι_workchain_id} }} : _.
    
Notation " a '↑' 'details_info.workchain_id' " := ( details_info_ι_workchain_id_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.workchain_id' " := ( details_info_ι_workchain_id_left a ) (in custom ULValue at level 0) : ursus_scope.

End ClassTypesNotations.