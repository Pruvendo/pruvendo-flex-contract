Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.RootTokenContract.ClassTypes.
Require Import Contracts.RootTokenContract.Ledger.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := Contracts.RootTokenContract.ClassTypes.ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition DRootTokenContract_ι_name__right {b} (x: URValue DRootTokenContractLRecord b): URValue XString b :=
    || {x} ^^ {DRootTokenContract_ι_name_} || : _.
    
Definition DRootTokenContract_ι_name__left (x: ULValue DRootTokenContractLRecord): ULValue XString :=
    {{ {x} ^^ {DRootTokenContract_ι_name_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.name_' " := ( DRootTokenContract_ι_name__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.name_' " := ( DRootTokenContract_ι_name__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_symbol__right {b} (x: URValue DRootTokenContractLRecord b): URValue XString b :=
    || {x} ^^ {DRootTokenContract_ι_symbol_} || : _.
    
Definition DRootTokenContract_ι_symbol__left (x: ULValue DRootTokenContractLRecord): ULValue XString :=
    {{ {x} ^^ {DRootTokenContract_ι_symbol_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.symbol_' " := ( DRootTokenContract_ι_symbol__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.symbol_' " := ( DRootTokenContract_ι_symbol__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_decimals__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DRootTokenContract_ι_decimals_} || : _.
    
Definition DRootTokenContract_ι_decimals__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DRootTokenContract_ι_decimals_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.decimals_' " := ( DRootTokenContract_ι_decimals__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.decimals_' " := ( DRootTokenContract_ι_decimals__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_root_public_key__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DRootTokenContract_ι_root_public_key_} || : _.
    
Definition DRootTokenContract_ι_root_public_key__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DRootTokenContract_ι_root_public_key_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.root_public_key_' " := ( DRootTokenContract_ι_root_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.root_public_key_' " := ( DRootTokenContract_ι_root_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_total_supply__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DRootTokenContract_ι_total_supply_} || : _.
    
Definition DRootTokenContract_ι_total_supply__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DRootTokenContract_ι_total_supply_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.total_supply_' " := ( DRootTokenContract_ι_total_supply__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.total_supply_' " := ( DRootTokenContract_ι_total_supply__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_total_granted__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DRootTokenContract_ι_total_granted_} || : _.
    
Definition DRootTokenContract_ι_total_granted__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DRootTokenContract_ι_total_granted_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.total_granted_' " := ( DRootTokenContract_ι_total_granted__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.total_granted_' " := ( DRootTokenContract_ι_total_granted__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_wallet_code__right {b} (x: URValue DRootTokenContractLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DRootTokenContract_ι_wallet_code_} || : _.
    
Definition DRootTokenContract_ι_wallet_code__left (x: ULValue DRootTokenContractLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DRootTokenContract_ι_wallet_code_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.wallet_code_' " := ( DRootTokenContract_ι_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.wallet_code_' " := ( DRootTokenContract_ι_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_owner_address__right {b} (x: URValue DRootTokenContractLRecord b): URValue ( XMaybe XAddress ) b :=
    || {x} ^^ {DRootTokenContract_ι_owner_address_} || : _.
    
Definition DRootTokenContract_ι_owner_address__left (x: ULValue DRootTokenContractLRecord): ULValue ( XMaybe XAddress ) :=
    {{ {x} ^^ {DRootTokenContract_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DRootTokenContract_ι_owner_address_' " := ( DRootTokenContract_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract_ι_owner_address_' " := ( DRootTokenContract_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.


Definition DRootTokenContract_ι_start_balance__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger b :=
    || {x} ^^ {DRootTokenContract_ι_start_balance_} || : _.
    
Definition DRootTokenContract_ι_start_balance__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger :=
    {{ {x} ^^ {DRootTokenContract_ι_start_balance_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.start_balance_' " := ( DRootTokenContract_ι_start_balance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.start_balance_' " := ( DRootTokenContract_ι_start_balance__left a ) (in custom ULValue at level 0) : ursus_scope.





End ClassTypesNotations.


