Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.Wrapper.ClassTypes.
Require Import Contracts.Wrapper.Ledger.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition WrapperRet_ι_err_code_right {b} (x: URValue WrapperRetLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {WrapperRet_ι_err_code} || : _ .
    
Definition WrapperRet_ι_err_code_left (x: ULValue WrapperRetLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {WrapperRet_ι_err_code} }} : _.
    
Notation " a '↑' 'WrapperRet.err_code' " := ( WrapperRet_ι_err_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperRet.err_code' " := ( WrapperRet_ι_err_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperRet_ι_flex_wallet_right {b} (x: URValue WrapperRetLRecord b): URValue XAddress b :=
    || {x} ^^ {WrapperRet_ι_flex_wallet} || : _ .
    
Definition WrapperRet_ι_flex_wallet_left (x: ULValue WrapperRetLRecord): ULValue XAddress :=
    {{ {x} ^^ {WrapperRet_ι_flex_wallet} }} : _.
    
Notation " a '↑' 'WrapperRet.flex_wallet' " := ( WrapperRet_ι_flex_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperRet.flex_wallet' " := ( WrapperRet_ι_flex_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDeployWalletArgs_ι_pubkey_right {b} (x: URValue FlexDeployWalletArgsLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {FlexDeployWalletArgs_ι_pubkey} || : _ .
    
Definition FlexDeployWalletArgs_ι_pubkey_left (x: ULValue FlexDeployWalletArgsLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {FlexDeployWalletArgs_ι_pubkey} }} : _.
    
Notation " a '↑' 'FlexDeployWalletArgs.pubkey' " := ( FlexDeployWalletArgs_ι_pubkey_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDeployWalletArgs.pubkey' " := ( FlexDeployWalletArgs_ι_pubkey_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDeployWalletArgs_ι_internal_owner_right {b} (x: URValue FlexDeployWalletArgsLRecord b): URValue XAddress b :=
    || {x} ^^ {FlexDeployWalletArgs_ι_internal_owner} || : _ .
    
Definition FlexDeployWalletArgs_ι_internal_owner_left (x: ULValue FlexDeployWalletArgsLRecord): ULValue XAddress :=
    {{ {x} ^^ {FlexDeployWalletArgs_ι_internal_owner} }} : _.
    
Notation " a '↑' 'FlexDeployWalletArgs.internal_owner' " := ( FlexDeployWalletArgs_ι_internal_owner_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDeployWalletArgs.internal_owner' " := ( FlexDeployWalletArgs_ι_internal_owner_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDeployWalletArgs_ι_grams_right {b} (x: URValue FlexDeployWalletArgsLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {FlexDeployWalletArgs_ι_grams} || : _ .
    
Definition FlexDeployWalletArgs_ι_grams_left (x: ULValue FlexDeployWalletArgsLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {FlexDeployWalletArgs_ι_grams} }} : _.
    
Notation " a '↑' 'FlexDeployWalletArgs.grams' " := ( FlexDeployWalletArgs_ι_grams_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDeployWalletArgs.grams' " := ( FlexDeployWalletArgs_ι_grams_left a ) (in custom ULValue at level 0) : ursus_scope.



Definition wrapper_details_info_ι_name_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XString b :=
    || {x} ^^ {wrapper_details_info_ι_name} || : _ .
    
Definition wrapper_details_info_ι_name_left (x: ULValue wrapper_details_infoLRecord): ULValue XString :=
    {{ {x} ^^ {wrapper_details_info_ι_name} }} : _.
    
Notation " a '↑' 'wrapper_details_info.name' " := ( wrapper_details_info_ι_name_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.name' " := ( wrapper_details_info_ι_name_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_symbol_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XString b :=
    || {x} ^^ {wrapper_details_info_ι_symbol} || : _ .
    
Definition wrapper_details_info_ι_symbol_left (x: ULValue wrapper_details_infoLRecord): ULValue XString :=
    {{ {x} ^^ {wrapper_details_info_ι_symbol} }} : _.
    
Notation " a '↑' 'wrapper_details_info.symbol' " := ( wrapper_details_info_ι_symbol_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.symbol' " := ( wrapper_details_info_ι_symbol_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_decimals_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {wrapper_details_info_ι_decimals} || : _ .
    
Definition wrapper_details_info_ι_decimals_left (x: ULValue wrapper_details_infoLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {wrapper_details_info_ι_decimals} }} : _.
    
Notation " a '↑' 'wrapper_details_info.decimals' " := ( wrapper_details_info_ι_decimals_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.decimals' " := ( wrapper_details_info_ι_decimals_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_root_public_key_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {wrapper_details_info_ι_root_public_key} || : _ .
    
Definition wrapper_details_info_ι_root_public_key_left (x: ULValue wrapper_details_infoLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {wrapper_details_info_ι_root_public_key} }} : _.
    
Notation " a '↑' 'wrapper_details_info.root_public_key' " := ( wrapper_details_info_ι_root_public_key_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.root_public_key' " := ( wrapper_details_info_ι_root_public_key_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_total_granted_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {wrapper_details_info_ι_total_granted} || : _ .
    
Definition wrapper_details_info_ι_total_granted_left (x: ULValue wrapper_details_infoLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {wrapper_details_info_ι_total_granted} }} : _.
    
Notation " a '↑' 'wrapper_details_info.total_granted' " := ( wrapper_details_info_ι_total_granted_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.total_granted' " := ( wrapper_details_info_ι_total_granted_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_wallet_code_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XCell b :=
    || {x} ^^ {wrapper_details_info_ι_wallet_code} || : _ .
    
Definition wrapper_details_info_ι_wallet_code_left (x: ULValue wrapper_details_infoLRecord): ULValue XCell :=
    {{ {x} ^^ {wrapper_details_info_ι_wallet_code} }} : _.
    
Notation " a '↑' 'wrapper_details_info.wallet_code' " := ( wrapper_details_info_ι_wallet_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.wallet_code' " := ( wrapper_details_info_ι_wallet_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_owner_address_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XAddress b :=
    || {x} ^^ {wrapper_details_info_ι_owner_address} || : _ .
    
Definition wrapper_details_info_ι_owner_address_left (x: ULValue wrapper_details_infoLRecord): ULValue XAddress :=
    {{ {x} ^^ {wrapper_details_info_ι_owner_address} }} : _.
    
Notation " a '↑' 'wrapper_details_info.owner_address' " := ( wrapper_details_info_ι_owner_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.owner_address' " := ( wrapper_details_info_ι_owner_address_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_external_wallet_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XAddress b :=
    || {x} ^^ {wrapper_details_info_ι_external_wallet} || : _ .
    
Definition wrapper_details_info_ι_external_wallet_left (x: ULValue wrapper_details_infoLRecord): ULValue XAddress :=
    {{ {x} ^^ {wrapper_details_info_ι_external_wallet} }} : _.
    
Notation " a '↑' 'wrapper_details_info.external_wallet' " := ( wrapper_details_info_ι_external_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.external_wallet' " := ( wrapper_details_info_ι_external_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_name__right {b} (x: URValue DWrapperFieldsLRecord b): URValue XString b :=
    || {x} ^^ {DWrapper_ι_name_} || : _ .
    
Definition DWrapper_ι_name__left (x: ULValue DWrapperFieldsLRecord): ULValue XString :=
    {{ {x} ^^ {DWrapper_ι_name_} }} : _.
    
Notation " a '↑' 'DWrapper.name_' " := ( DWrapper_ι_name__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.name_' " := ( DWrapper_ι_name__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_symbol__right {b} (x: URValue DWrapperFieldsLRecord b): URValue XString b :=
    || {x} ^^ {DWrapper_ι_symbol_} || : _ .
    
Definition DWrapper_ι_symbol__left (x: ULValue DWrapperFieldsLRecord): ULValue XString :=
    {{ {x} ^^ {DWrapper_ι_symbol_} }} : _.
    
Notation " a '↑' 'DWrapper.symbol_' " := ( DWrapper_ι_symbol__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.symbol_' " := ( DWrapper_ι_symbol__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_decimals__right {b} (x: URValue DWrapperFieldsLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DWrapper_ι_decimals_} || : _ .
    
Definition DWrapper_ι_decimals__left (x: ULValue DWrapperFieldsLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DWrapper_ι_decimals_} }} : _.
    
Notation " a '↑' 'DWrapper.decimals_' " := ( DWrapper_ι_decimals__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.decimals_' " := ( DWrapper_ι_decimals__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_workchain_id__right {b} (x: URValue DWrapperFieldsLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DWrapper_ι_workchain_id_} || : _ .
    
Definition DWrapper_ι_workchain_id__left (x: ULValue DWrapperFieldsLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DWrapper_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DWrapper.workchain_id_' " := ( DWrapper_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.workchain_id_' " := ( DWrapper_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_root_public_key__right {b} (x: URValue DWrapperFieldsLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DWrapper_ι_root_public_key_} || : _ .
    
Definition DWrapper_ι_root_public_key__left (x: ULValue DWrapperFieldsLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DWrapper_ι_root_public_key_} }} : _.
    
Notation " a '↑' 'DWrapper.root_public_key_' " := ( DWrapper_ι_root_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.root_public_key_' " := ( DWrapper_ι_root_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_total_granted__right {b} (x: URValue DWrapperFieldsLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DWrapper_ι_total_granted_} || : _ .
    
Definition DWrapper_ι_total_granted__left (x: ULValue DWrapperFieldsLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DWrapper_ι_total_granted_} }} : _.
    
Notation " a '↑' 'DWrapper.total_granted_' " := ( DWrapper_ι_total_granted__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.total_granted_' " := ( DWrapper_ι_total_granted__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_owner_address__right {b} (x: URValue DWrapperFieldsLRecord b): URValue ( XMaybe XAddress ) b :=
    || {x} ^^ {DWrapper_ι_owner_address_} || : _ .
    
Definition DWrapper_ι_owner_address__left (x: ULValue DWrapperFieldsLRecord): ULValue ( XMaybe XAddress ) :=
    {{ {x} ^^ {DWrapper_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DWrapper.owner_address_' " := ( DWrapper_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.owner_address_' " := ( DWrapper_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_internal_wallet_code__right {b} (x: URValue DWrapperFieldsLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DWrapper_ι_internal_wallet_code_} || : _ .
    
Definition DWrapper_ι_internal_wallet_code__left (x: ULValue DWrapperFieldsLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DWrapper_ι_internal_wallet_code_} }} : _.
    
Notation " a '↑' 'DWrapper.internal_wallet_code_' " := ( DWrapper_ι_internal_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.internal_wallet_code_' " := ( DWrapper_ι_internal_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_start_balance__right {b} (x: URValue DWrapperFieldsLRecord b): URValue GramsLRecord b :=
    || {x} ^^ {DWrapper_ι_start_balance_} || : _ .
    
Definition DWrapper_ι_start_balance__left (x: ULValue DWrapperFieldsLRecord): ULValue GramsLRecord :=
    {{ {x} ^^ {DWrapper_ι_start_balance_} }} : _.
    
Notation " a '↑' 'DWrapper.start_balance_' " := ( DWrapper_ι_start_balance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.start_balance_' " := ( DWrapper_ι_start_balance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_external_wallet__right {b} (x: URValue DWrapperFieldsLRecord b): URValue XAddress b :=
    || {x} ^^ {DWrapper_ι_external_wallet_} || : _ .
    
Definition DWrapper_ι_external_wallet__left (x: ULValue DWrapperFieldsLRecord): ULValue XAddress :=
    {{ {x} ^^ {DWrapper_ι_external_wallet_} }} : _.
    
Notation " a '↑' 'DWrapper.external_wallet_' " := ( DWrapper_ι_external_wallet__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.external_wallet_' " := ( DWrapper_ι_external_wallet__left a ) (in custom ULValue at level 0) : ursus_scope.

End ClassTypesNotations.