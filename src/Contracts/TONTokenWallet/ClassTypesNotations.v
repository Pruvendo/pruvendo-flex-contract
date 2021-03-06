Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonAxioms.
Require Import Project.CommonTypes.

Require Import TONTokenWallet.ClassTypes.
Require Import TONTokenWallet.Interface.

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonAxiomsModule := CommonAxioms xt sm cs.
Module Export ClassTypesModule := (* TONTokenWallet.ClassTypes. *)ClassTypes xt sm.
Module Export InterfaceModule := PublicInterface xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition lend_array_record_ι_lend_addr_right {b} (x: URValue lend_array_recordLRecord b): URValue address b :=
    || {x} ^^ {lend_array_record_ι_lend_addr} || : _.
    
Definition lend_array_record_ι_lend_addr_left (x: ULValue lend_array_recordLRecord): ULValue address :=
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

Definition DTONTokenWallet_ι_root_address__right {b} (x: URValue DTONTokenWalletLRecord b): URValue address b :=
    || {x} ^^ {DTONTokenWallet_ι_root_address_} || : _.
    
Definition DTONTokenWallet_ι_root_address__left (x: ULValue DTONTokenWalletLRecord): ULValue address :=
    {{ {x} ^^ {DTONTokenWallet_ι_root_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.root_address_' " := ( DTONTokenWallet_ι_root_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.root_address_' " := ( DTONTokenWallet_ι_root_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_owner_address__right {b} (x: URValue DTONTokenWalletLRecord b): URValue ( XMaybe address ) b :=
    || {x} ^^ {DTONTokenWallet_ι_owner_address_} || : _.
    
Definition DTONTokenWallet_ι_owner_address__left (x: ULValue DTONTokenWalletLRecord): ULValue ( XMaybe address ) :=
    {{ {x} ^^ {DTONTokenWallet_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.owner_address_' " := ( DTONTokenWallet_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.owner_address_' " := ( DTONTokenWallet_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_code__right {b} (x: URValue DTONTokenWalletLRecord b): URValue cell b :=
    || {x} ^^ {DTONTokenWallet_ι_code_} || : _.
    
Definition DTONTokenWallet_ι_code__left (x: ULValue DTONTokenWalletLRecord): ULValue cell :=
    {{ {x} ^^ {DTONTokenWallet_ι_code_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.code_' " := ( DTONTokenWallet_ι_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.code_' " := ( DTONTokenWallet_ι_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_allowance__right {b} (x: URValue DTONTokenWalletLRecord b): URValue ( XMaybe allowance_infoLRecord ) b :=
    || {x} ^^ {DTONTokenWallet_ι_allowance_} || : _.
    
Definition DTONTokenWallet_ι_allowance__left (x: ULValue DTONTokenWalletLRecord): ULValue ( XMaybe allowance_infoLRecord ) :=
    {{ {x} ^^ {DTONTokenWallet_ι_allowance_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.allowance_' " := ( DTONTokenWallet_ι_allowance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.allowance_' " := ( DTONTokenWallet_ι_allowance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWallet_ι_workchain_id__right {b} (x: URValue DTONTokenWalletLRecord b): URValue XInteger (* XUInteger8 *) b :=
    || {x} ^^ {DTONTokenWallet_ι_workchain_id_} || : _.
    
Definition DTONTokenWallet_ι_workchain_id__left (x: ULValue DTONTokenWalletLRecord): ULValue XInteger (* XUInteger8 *) :=
    {{ {x} ^^ {DTONTokenWallet_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.workchain_id_' " := ( DTONTokenWallet_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.workchain_id_' " := ( DTONTokenWallet_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.


Definition DTONTokenWallet_ι_lend_ownership__right {b} (x: URValue DTONTokenWalletLRecord b): URValue (XHMap addr_std_fixed lend_recordLRecord) (* XUInteger8 *) b :=
    || {x} ^^ {DTONTokenWallet_ι_lend_ownership_} || : _.
    
Definition DTONTokenWallet_ι_lend_ownership__left (x: ULValue DTONTokenWalletLRecord): ULValue (XHMap addr_std_fixed lend_recordLRecord) (* XUInteger8 *) :=
    {{ {x} ^^ {DTONTokenWallet_ι_lend_ownership_} }} : _.
    
Notation " a '↑' 'DTONTokenWallet.lend_ownership_' " := ( DTONTokenWallet_ι_lend_ownership__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWallet.lend_ownership_' " := ( DTONTokenWallet_ι_lend_ownership__left a ) (in custom ULValue at level 0) : ursus_scope.


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

Definition DTONTokenWalletExternal_ι_root_address__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue address b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_root_address_} || : _.
    
Definition DTONTokenWalletExternal_ι_root_address__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue address :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_root_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.root_address_' " := ( DTONTokenWalletExternal_ι_root_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.root_address_' " := ( DTONTokenWalletExternal_ι_root_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_owner_address__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue ( XMaybe address ) b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_owner_address_} || : _.
    
Definition DTONTokenWalletExternal_ι_owner_address__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue ( XMaybe address ) :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.owner_address_' " := ( DTONTokenWalletExternal_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.owner_address_' " := ( DTONTokenWalletExternal_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_code__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue cell b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_code_} || : _.
    
Definition DTONTokenWalletExternal_ι_code__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue cell :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_code_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.code_' " := ( DTONTokenWalletExternal_ι_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.code_' " := ( DTONTokenWalletExternal_ι_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_allowance__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue ( XMaybe allowance_infoLRecord ) b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_allowance_} || : _.
    
Definition DTONTokenWalletExternal_ι_allowance__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue ( XMaybe allowance_infoLRecord ) :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_allowance_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.allowance_' " := ( DTONTokenWalletExternal_ι_allowance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.allowance_' " := ( DTONTokenWalletExternal_ι_allowance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletExternal_ι_workchain_id__right {b} (x: URValue DTONTokenWalletExternalLRecord b): URValue XInteger (* XUInteger8 *) b :=
    || {x} ^^ {DTONTokenWalletExternal_ι_workchain_id_} || : _.
    
Definition DTONTokenWalletExternal_ι_workchain_id__left (x: ULValue DTONTokenWalletExternalLRecord): ULValue XInteger (* XUInteger8 *) :=
    {{ {x} ^^ {DTONTokenWalletExternal_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletExternal.workchain_id_' " := ( DTONTokenWalletExternal_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletExternal.workchain_id_' " := ( DTONTokenWalletExternal_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.



Definition DTONTokenWalletInternal_ι_name__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue XString b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_name_} || : _.
    
Definition DTONTokenWalletInternal_ι_name__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XString :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_name_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.name_' " := ( DTONTokenWalletInternal_ι_name__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.name_' " := ( DTONTokenWalletInternal_ι_name__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_symbol__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue XString b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_symbol_} || : _.
    
Definition DTONTokenWalletInternal_ι_symbol__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XString :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_symbol_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.symbol_' " := ( DTONTokenWalletInternal_ι_symbol__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.symbol_' " := ( DTONTokenWalletInternal_ι_symbol__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_decimals__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_decimals_} || : _.
    
Definition DTONTokenWalletInternal_ι_decimals__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_decimals_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.decimals_' " := ( DTONTokenWalletInternal_ι_decimals__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.decimals_' " := ( DTONTokenWalletInternal_ι_decimals__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_balance__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_balance_} || : _.
    
Definition DTONTokenWalletInternal_ι_balance__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_balance_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.balance_' " := ( DTONTokenWalletInternal_ι_balance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.balance_' " := ( DTONTokenWalletInternal_ι_balance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_root_public_key__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_root_public_key_} || : _.
    
Definition DTONTokenWalletInternal_ι_root_public_key__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_root_public_key_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.root_public_key_' " := ( DTONTokenWalletInternal_ι_root_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.root_public_key_' " := ( DTONTokenWalletInternal_ι_root_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_wallet_public_key__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_wallet_public_key_} || : _.
    
Definition DTONTokenWalletInternal_ι_wallet_public_key__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_wallet_public_key_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.wallet_public_key_' " := ( DTONTokenWalletInternal_ι_wallet_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.wallet_public_key_' " := ( DTONTokenWalletInternal_ι_wallet_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_root_address__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue address b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_root_address_} || : _.
    
Definition DTONTokenWalletInternal_ι_root_address__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue address :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_root_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.root_address_' " := ( DTONTokenWalletInternal_ι_root_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.root_address_' " := ( DTONTokenWalletInternal_ι_root_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_owner_address__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue ( XMaybe address ) b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_owner_address_} || : _.
    
Definition DTONTokenWalletInternal_ι_owner_address__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue ( XMaybe address ) :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.owner_address_' " := ( DTONTokenWalletInternal_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.owner_address_' " := ( DTONTokenWalletInternal_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_code__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue cell b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_code_} || : _.
    
Definition DTONTokenWalletInternal_ι_code__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue cell :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_code_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.code_' " := ( DTONTokenWalletInternal_ι_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.code_' " := ( DTONTokenWalletInternal_ι_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_lend_ownership__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue ( XHMap addr_std_fixed lend_recordLRecord ) b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_lend_ownership_} || : _.
    
Definition DTONTokenWalletInternal_ι_lend_ownership__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue ( XHMap addr_std_fixed lend_recordLRecord ) :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_lend_ownership_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.lend_ownership_' " := ( DTONTokenWalletInternal_ι_lend_ownership__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.lend_ownership_' " := ( DTONTokenWalletInternal_ι_lend_ownership__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTONTokenWalletInternal_ι_workchain_id__right {b} (x: URValue DTONTokenWalletInternalLRecord b): URValue XInteger (* XUInteger8 *) b :=
    || {x} ^^ {DTONTokenWalletInternal_ι_workchain_id_} || : _.
    
Definition DTONTokenWalletInternal_ι_workchain_id__left (x: ULValue DTONTokenWalletInternalLRecord): ULValue XInteger (* XUInteger8 *) :=
    {{ {x} ^^ {DTONTokenWalletInternal_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DTONTokenWalletInternal.workchain_id_' " := ( DTONTokenWalletInternal_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTONTokenWalletInternal.workchain_id_' " := ( DTONTokenWalletInternal_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_name_right {b} (x: URValue details_infoLRecord b): URValue XString b :=
    || {x} ^^ {details_info_ι_name} || : _.
    
Definition details_info_ι_name_left (x: ULValue details_infoLRecord): ULValue XString :=
    {{ {x} ^^ {details_info_ι_name} }} : _.
    
Notation " a '↑' 'details_info.name' " := ( details_info_ι_name_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.name' " := ( details_info_ι_name_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_symbol_right {b} (x: URValue details_infoLRecord b): URValue XString b :=
    || {x} ^^ {details_info_ι_symbol} || : _.
    
Definition details_info_ι_symbol_left (x: ULValue details_infoLRecord): ULValue XString :=
    {{ {x} ^^ {details_info_ι_symbol} }} : _.
    
Notation " a '↑' 'details_info.symbol' " := ( details_info_ι_symbol_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.symbol' " := ( details_info_ι_symbol_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_decimals_right {b} (x: URValue details_infoLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {details_info_ι_decimals} || : _.
    
Definition details_info_ι_decimals_left (x: ULValue details_infoLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {details_info_ι_decimals} }} : _.
    
Notation " a '↑' 'details_info.decimals' " := ( details_info_ι_decimals_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.decimals' " := ( details_info_ι_decimals_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_balance_right {b} (x: URValue details_infoLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {details_info_ι_balance} || : _.
    
Definition details_info_ι_balance_left (x: ULValue details_infoLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {details_info_ι_balance} }} : _.
    
Notation " a '↑' 'details_info.balance' " := ( details_info_ι_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.balance' " := ( details_info_ι_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_root_public_key_right {b} (x: URValue details_infoLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {details_info_ι_root_public_key} || : _.
    
Definition details_info_ι_root_public_key_left (x: ULValue details_infoLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {details_info_ι_root_public_key} }} : _.
    
Notation " a '↑' 'details_info.root_public_key' " := ( details_info_ι_root_public_key_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.root_public_key' " := ( details_info_ι_root_public_key_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_wallet_public_key_right {b} (x: URValue details_infoLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {details_info_ι_wallet_public_key} || : _.
    
Definition details_info_ι_wallet_public_key_left (x: ULValue details_infoLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {details_info_ι_wallet_public_key} }} : _.
    
Notation " a '↑' 'details_info.wallet_public_key' " := ( details_info_ι_wallet_public_key_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.wallet_public_key' " := ( details_info_ι_wallet_public_key_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_root_address_right {b} (x: URValue details_infoLRecord b): URValue address b :=
    || {x} ^^ {details_info_ι_root_address} || : _.
    
Definition details_info_ι_root_address_left (x: ULValue details_infoLRecord): ULValue address :=
    {{ {x} ^^ {details_info_ι_root_address} }} : _.
    
Notation " a '↑' 'details_info.root_address' " := ( details_info_ι_root_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.root_address' " := ( details_info_ι_root_address_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_owner_address_right {b} (x: URValue details_infoLRecord b): URValue address b :=
    || {x} ^^ {details_info_ι_owner_address} || : _.
    
Definition details_info_ι_owner_address_left (x: ULValue details_infoLRecord): ULValue address :=
    {{ {x} ^^ {details_info_ι_owner_address} }} : _.
    
Notation " a '↑' 'details_info.owner_address' " := ( details_info_ι_owner_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.owner_address' " := ( details_info_ι_owner_address_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_lend_ownership_right {b} (x: URValue details_infoLRecord b): URValue ( XHMap XUInteger lend_array_recordLRecord ) b :=
    || {x} ^^ {details_info_ι_lend_ownership} || : _.
    
Definition details_info_ι_lend_ownership_left (x: ULValue details_infoLRecord): ULValue ( XHMap XUInteger lend_array_recordLRecord ) :=
    {{ {x} ^^ {details_info_ι_lend_ownership} }} : _.
    
Notation " a '↑' 'details_info.lend_ownership' " := ( details_info_ι_lend_ownership_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.lend_ownership' " := ( details_info_ι_lend_ownership_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_lend_balance_right {b} (x: URValue details_infoLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {details_info_ι_lend_balance} || : _.
    
Definition details_info_ι_lend_balance_left (x: ULValue details_infoLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {details_info_ι_lend_balance} }} : _.
    
Notation " a '↑' 'details_info.lend_balance' " := ( details_info_ι_lend_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.lend_balance' " := ( details_info_ι_lend_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_code_right {b} (x: URValue details_infoLRecord b): URValue cell b :=
    || {x} ^^ {details_info_ι_code} || : _.
    
Definition details_info_ι_code_left (x: ULValue details_infoLRecord): ULValue cell :=
    {{ {x} ^^ {details_info_ι_code} }} : _.
    
Notation " a '↑' 'details_info.code' " := ( details_info_ι_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.code' " := ( details_info_ι_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_allowance_right {b} (x: URValue details_infoLRecord b): URValue allowance_infoLRecord b :=
    || {x} ^^ {details_info_ι_allowance} || : _.
    
Definition details_info_ι_allowance_left (x: ULValue details_infoLRecord): ULValue allowance_infoLRecord :=
    {{ {x} ^^ {details_info_ι_allowance} }} : _.
    
Notation " a '↑' 'details_info.allowance' " := ( details_info_ι_allowance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.allowance' " := ( details_info_ι_allowance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition details_info_ι_workchain_id_right {b} (x: URValue details_infoLRecord b): URValue XInteger b :=
    || {x} ^^ {details_info_ι_workchain_id} || : _.
    
Definition details_info_ι_workchain_id_left (x: ULValue details_infoLRecord): ULValue XInteger  :=
    {{ {x} ^^ {details_info_ι_workchain_id} }} : _.
    
Notation " a '↑' 'details_info.workchain_id' " := ( details_info_ι_workchain_id_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'details_info.workchain_id' " := ( details_info_ι_workchain_id_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition allowance_info_ι_spender_right {b} (x: URValue allowance_infoLRecord b): URValue address b :=
    || {x} ^^ {allowance_info_ι_spender} || : _.
    
Definition allowance_info_ι_spender_left (x: ULValue allowance_infoLRecord): ULValue address :=
    {{ {x} ^^ {allowance_info_ι_spender} }} : _.
    
Notation " a '↑' 'allowance_info.spender' " := ( allowance_info_ι_spender_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'allowance_info.spender' " := ( allowance_info_ι_spender_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition allowance_info_ι_remainingTokens_right {b} (x: URValue allowance_infoLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {allowance_info_ι_remainingTokens} || : _.
    
Definition allowance_info_ι_remainingTokens_left (x: ULValue allowance_infoLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {allowance_info_ι_remainingTokens} }} : _.
    
Notation " a '↑' 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition lend_record_ι_lend_balance_right {b} (x: URValue lend_recordLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {lend_record_ι_lend_balance} || : _.
    
Definition lend_record_ι_lend_balance_left (x: ULValue lend_recordLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {lend_record_ι_lend_balance} }} : _.
    
Notation " a '↑' 'lend_record.lend_balance' " := ( lend_record_ι_lend_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'lend_record.lend_balance' " := ( lend_record_ι_lend_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition lend_record_ι_lend_finish_time_right {b} (x: URValue lend_recordLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {lend_record_ι_lend_finish_time} || : _.
    
Definition lend_record_ι_lend_finish_time_left (x: ULValue lend_recordLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {lend_record_ι_lend_finish_time} }} : _.
    
Notation " a '↑' 'lend_record.lend_finish_time' " := ( lend_record_ι_lend_finish_time_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'lend_record.lend_finish_time' " := ( lend_record_ι_lend_finish_time_left a ) (in custom ULValue at level 0) : ursus_scope.




(* IonTip3LendOwnership : address -> XUInteger128 -> XUInteger32 -> XUInteger256 -> address -> cell -> ITONTokenWalletNotifyP *)
Definition IonTip3LendOwnership_right { a1 a2 a3 a4 a5 a6 }  (x : URValue address a1 ) 
                                                 (y : URValue XUInteger128 a2) 
                                                 (z : URValue XUInteger32 a3)
                                                 (t : URValue XUInteger256 a4)
                                                 (u : URValue address a5)
                                                 (v : URValue cell a6) : URValue ITONTokenWalletNotify (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 a6))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  #(IonTip3LendOwnership x' y' z' t' u' v' : ITONTokenWalletNotify))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.onTip3LendOwnership' ( x , y , z , t , u , v ) " := (IonTip3LendOwnership_right x y z t u v) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, v custom URValue at level 0 ) : ursus_scope .

(* | IonTip3Transfer : address -> XUInteger128 -> XUInteger128 -> XUInteger256 -> address -> cell -> ITONTokenWalletNotifyP. *)
Definition IonTip3Transfer_right { a1 a2 a3 a4 a5 a6 }  (x : URValue address a1 ) 
                                                 (y : URValue XUInteger128 a2) 
                                                 (z : URValue XUInteger128 a3)
                                                 (t : URValue XUInteger256 a4)
                                                 (u : URValue address a5)
                                                 (v : URValue cell a6) : URValue ITONTokenWalletNotify (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 a6))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  #(IonTip3Transfer x' y' z' t' u' v' : ITONTokenWalletNotify))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'TONTokenWallet.onTip3Transfer' ( x , y , z , t , u , v ) " := (IonTip3Transfer_right x y z t u v) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, v custom URValue at level 0 ) : ursus_scope .

(*********************************************************************************************************)

(*
Inductive ITONTokenWalletP :=
| ItransferWithNotify : address -> address -> XUInteger128 -> XUInteger128 -> XBool -> cell -> ITONTokenWalletP
| ItransferToRecipient : address -> XUInteger256 -> address -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> ITONTokenWalletP
| ItransferToRecipientWithNotify : address -> XUInteger256 -> address -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> cell -> ITONTokenWalletP
| IlendOwnership : address -> XUInteger128 -> XUInteger256 -> XUInteger128 -> 
                         XUInteger32 -> cell -> cell -> ITONTokenWalletP
| _Icreate : InitialState -> ITONTokenWalletP.
 *)

Definition ItransferWithNotify_right { a1 a2 a3 a4 a5 a6 }  (x : URValue address a1 ) 
                                                 (y : URValue address a2) 
                                                 (z : URValue XUInteger128 a3)
                                                 (t : URValue XUInteger128 a4)
                                                 (u : URValue XBool a5)
                                                 (v : URValue cell a6) : URValue ITONTokenWallet (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 a6))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  #(ItransferWithNotify x' y' z' t' u' v' : ITONTokenWallet))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.transferWithNotify' ( x , y , z , t , u , v ) " := (ItransferWithNotify_right x y z t u v) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, v custom URValue at level 0 ) : ursus_scope .

(* ItransferToRecipient : address -> XUInteger256 -> address -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> ITONTokenWalletP *)

Definition ItransferToRecipient_right { a1 a2 a3 a4 a5 a6 a7}  (x : URValue address a1 ) 
                                                 (y : URValue XUInteger256 a2) 
                                                 (z : URValue address a3)
                                                 (t : URValue XUInteger128 a4)
                                                 (u : URValue XUInteger128 a5)
                                                 (v : URValue XBool a6)
                                                 (w : URValue XBool a7) : 
                                                 URValue ITONTokenWallet (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 (orb a6 a7)))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  
                                    urvalue_bind w (fun w' =>  #(ItransferToRecipient x' y' z' t' u' v' w': ITONTokenWallet)))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.transferToRecipient' ( x , y , z , t , u , v , w ) " := (ItransferToRecipient_right x y z t u v w) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, 
 v custom URValue at level 0, w custom URValue at level 0 ) : ursus_scope .

(*  ItransferToRecipientWithNotify : address -> XUInteger256 -> address -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> cell -> ITONTokenWalletP *)

Definition ItransferToRecipientWithNotify_right { a1 a2 a3 a4 a5 a6 a7 a8}  (x : URValue address a1 ) 
                                                 (y : URValue XUInteger256 a2) 
                                                 (z : URValue address a3)
                                                 (t : URValue XUInteger128 a4)
                                                 (u : URValue XUInteger128 a5)
                                                 (v : URValue XBool a6)
                                                 (w : URValue XBool a7) 
                                                 (q : URValue cell a8): 
                                                 URValue ITONTokenWallet (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 (orb a6 (orb a7 a8))))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  
                                    urvalue_bind w (fun w' =>  
                                        urvalue_bind q (fun q' => #(ItransferToRecipientWithNotify x' y' z' t' u' v' w' q': ITONTokenWallet))))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.ItransferToRecipientWithNotify' ( x , y , z , t , u , v , w , q ) " := (ItransferToRecipientWithNotify_right x y z t u v w q) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, 
 v custom URValue at level 0, w custom URValue at level 0 , q custom URValue at level 0) : ursus_scope .


(* | IlendOwnership : address -> XUInteger128 -> XUInteger256 -> XUInteger128 -> 
                         XUInteger32 -> cell -> cell -> ITONTokenWalletP *)

Definition IlendOwnership_right { a1 a2 a3 a4 a5 a6 a7}  (x : URValue address a1 ) 
                                                 (y : URValue XUInteger128 a2) 
                                                 (z : URValue XUInteger256 a3)
                                                 (t : URValue XUInteger128 a4)
                                                 (u : URValue XUInteger32 a5)
                                                 (v : URValue cell a6)
                                                 (w : URValue cell a7) : 
                                                 URValue ITONTokenWallet (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 (orb a6 a7)))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  
                                    urvalue_bind w (fun w' =>  #(IlendOwnership x' y' z' t' u' v' w': ITONTokenWallet)))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.lendOwnership' ( x , y , z , t , u , v , w ) " := (IlendOwnership_right x y z t u v w) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, 
 v custom URValue at level 0, w custom URValue at level 0 ) : ursus_scope .


 Definition Iburn_right { a1 a2}  (x : URValue XUInteger256 a1 ) 
 (y : URValue address a2) 
 : URValue ITONTokenWallet (orb a1 a2 ).
pose proof ((urvalue_bind x (fun x' => 
urvalue_bind y (fun y' =>
  #(Iburn x' y' : ITONTokenWallet)))): URValue _ _).
rewrite right_or_false in X.
refine X.
Defined.

Notation " '.burn' ( x , y ) " := (Iburn_right x y) 
(in custom URValue at level 0 , x custom URValue at level 0,
y custom URValue at level 0 ) : ursus_scope .

Definition Iaccept_right { a1 a2 a3 }  (x : URValue XUInteger128 a1 ) 
(y : URValue address a2) 
(z : URValue XUInteger128 a3) 
: URValue ITONTokenWallet (orb a1 (orb a2 a3) ).
pose proof ((urvalue_bind x (fun x' => 
urvalue_bind y (fun y' =>
urvalue_bind z (fun z' =>
 #(Iaccept x' y' z' : ITONTokenWallet))))): URValue _ _).
rewrite right_or_false in X.
refine X.
Defined.

Notation " '.accept' ( x , y , z ) " := (Iaccept_right x y z) 
(in custom URValue at level 0 , x custom URValue at level 0,
y custom URValue at level 0 , z custom URValue at level 0 ) : ursus_scope .


Definition IreturnOwnership_right { a1}  (x : URValue XUInteger128 a1 ) 
: URValue ITONTokenWallet (a1 ).
pose proof ((urvalue_bind x (fun x' => 
 #(IreturnOwnership x' : ITONTokenWallet))): URValue _ _).
rewrite right_or_false in X.
refine X.
Defined.

Notation " '.returnOwnership' ( x ) " := (IreturnOwnership_right x) 
(in custom URValue at level 0 , x custom URValue at level 0) : ursus_scope .

(* void transfer(
    address_t answer_addr,
    address_t to,
    uint128 tokens,
    uint128 grams,
    bool_t  return_ownership
  ) = 10; *)

  Definition Itransfer_right { a1 a2 a3 a4 a5 }  (x : URValue address a1 ) 
  (y : URValue address a2) 
  (z : URValue XUInteger128 a3)
  (t : URValue XUInteger128 a4)
  (u : URValue XBool a5) : URValue ITONTokenWallet (orb a1 (orb a2 (orb a3 (orb a4 a5 )))).
pose proof (urvalue_bind x (fun x' => 
urvalue_bind y (fun y' =>
urvalue_bind z (fun z' =>  
urvalue_bind t (fun t' =>  
urvalue_bind u (fun u' =>  #(Itransfer x' y' z' t' u' : ITONTokenWallet)))))): URValue _ _).
rewrite right_or_false in X.
refine X.
Defined.

Notation " '.transfer' ( x , y , z , t , u ) " := (Itransfer_right x y z t u) 
(in custom URValue at level 0 , x custom URValue at level 0,
y custom URValue at level 0 , z custom URValue at level 0, 
t custom URValue at level 0 , u custom URValue at level 0) : ursus_scope .

Definition _Icreate_right { a1 }  ( x : URValue StateInitLRecord a1 ) : URValue ITONTokenWallet a1.
 pose proof (urvalue_bind x (fun x' => #(_Icreate x' : ITONTokenWallet)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'TONTokenWallet.deploy' ( x ) " := (_Icreate_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .
Notation " 'TONTokenWallet.deploy_noop' ( x ) " := (_Icreate_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .

Definition IinternalTransfer__right { a1 a2 a3 a4 a5 a6 }  (x : URValue XUInteger128 a1 ) 
                                                 (y : URValue address a2) 
                                                 (z : URValue XUInteger256 a3)
                                                 (t : URValue address a4)
                                                 (u : URValue XBool a5)
                                                 (v : URValue cell a6) : URValue ITONTokenWallet (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 a6))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  #(IinternalTransfer x' y' z' t' u' v' : ITONTokenWallet))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.internalTransfer_' ( x , y , z , t , u , v ) " := (IinternalTransfer__right x y z t u v) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, v custom URValue at level 0 ) : ursus_scope .

 Definition _IcreateNotify_right { a1 }  ( x : URValue StateInitLRecord a1 ) : URValue ITONTokenWalletNotify a1.
 pose proof (urvalue_bind x (fun x' => #(_IcreateNotify x' : ITONTokenWalletNotify)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'TONTokenWalletNotify.deploy' ( x ) " := (_IcreateNotify_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .

Definition IinternalTransferFrom_right { a1 a2 a3 a4 a5 }  (x : URValue address a1 ) 
(y : URValue address a2) 
(z : URValue XUInteger128 a3)
(t : URValue XBool a4)
(u : URValue cell a5) : URValue ITONTokenWallet (orb a1 (orb a2 (orb a3 (orb a4 a5 )))).
pose proof (urvalue_bind x (fun x' => 
urvalue_bind y (fun y' =>
urvalue_bind z (fun z' =>  
urvalue_bind t (fun t' =>  
urvalue_bind u (fun u' =>  #(IinternalTransferFrom x' y' z' t' u' : ITONTokenWallet)))))): URValue _ _).
rewrite right_or_false in X.
refine X.
Defined.

Notation " '.internalTransferFrom' ( x , y , z , t , u ) " := (IinternalTransferFrom_right x y z t u) 
(in custom URValue at level 0 , x custom URValue at level 0,
y custom URValue at level 0 , z custom URValue at level 0, 
t custom URValue at level 0 , u custom URValue at level 0) : ursus_scope .

End ClassTypesNotations.