Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.FlexClient.ClassTypes.
Require Import Contracts.FlexClient.Ledger.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := Contracts.FlexClient.ClassTypes.ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition DFlexClient_ι_owner__right {b} (x: URValue DFlexClientLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DFlexClient_ι_owner_} || : _.
    
Definition DFlexClient_ι_owner__left (x: ULValue DFlexClientLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DFlexClient_ι_owner_} }} : _.
    
Notation " a '↑' 'DFlexClient.owner_' " := ( DFlexClient_ι_owner__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.owner_' " := ( DFlexClient_ι_owner__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_trading_pair_code__right {b} (x: URValue DFlexClientLRecord b): URValue XCell b :=
    || {x} ^^ {DFlexClient_ι_trading_pair_code_} || : _.
    
Definition DFlexClient_ι_trading_pair_code__left (x: ULValue DFlexClientLRecord): ULValue XCell :=
    {{ {x} ^^ {DFlexClient_ι_trading_pair_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.trading_pair_code_' " := ( DFlexClient_ι_trading_pair_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.trading_pair_code_' " := ( DFlexClient_ι_trading_pair_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_xchg_pair_code__right {b} (x: URValue DFlexClientLRecord b): URValue XCell b :=
    || {x} ^^ {DFlexClient_ι_xchg_pair_code_} || : _.
    
Definition DFlexClient_ι_xchg_pair_code__left (x: ULValue DFlexClientLRecord): ULValue XCell :=
    {{ {x} ^^ {DFlexClient_ι_xchg_pair_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.xchg_pair_code_' " := ( DFlexClient_ι_xchg_pair_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.xchg_pair_code_' " := ( DFlexClient_ι_xchg_pair_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_workchain_id__right {b} (x: URValue DFlexClientLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DFlexClient_ι_workchain_id_} || : _.
    
Definition DFlexClient_ι_workchain_id__left (x: ULValue DFlexClientLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DFlexClient_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DFlexClient.workchain_id_' " := ( DFlexClient_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.workchain_id_' " := ( DFlexClient_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_tons_cfg__right {b} (x: URValue DFlexClientLRecord b): URValue TonsConfigLRecord b :=
    || {x} ^^ {DFlexClient_ι_tons_cfg_} || : _.
    
Definition DFlexClient_ι_tons_cfg__left (x: ULValue DFlexClientLRecord): ULValue TonsConfigLRecord :=
    {{ {x} ^^ {DFlexClient_ι_tons_cfg_} }} : _.
    
Notation " a '↑' 'DFlexClient.tons_cfg_' " := ( DFlexClient_ι_tons_cfg__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.tons_cfg_' " := ( DFlexClient_ι_tons_cfg__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_flex__right {b} (x: URValue DFlexClientLRecord b): URValue XAddress b :=
    || {x} ^^ {DFlexClient_ι_flex_} || : _.
    
Definition DFlexClient_ι_flex__left (x: ULValue DFlexClientLRecord): ULValue XAddress :=
    {{ {x} ^^ {DFlexClient_ι_flex_} }} : _.
    
Notation " a '↑' 'DFlexClient.flex_' " := ( DFlexClient_ι_flex__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.flex_' " := ( DFlexClient_ι_flex__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_ext_wallet_code__right {b} (x: URValue DFlexClientLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlexClient_ι_ext_wallet_code_} || : _.
    
Definition DFlexClient_ι_ext_wallet_code__left (x: ULValue DFlexClientLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlexClient_ι_ext_wallet_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.ext_wallet_code_' " := ( DFlexClient_ι_ext_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.ext_wallet_code_' " := ( DFlexClient_ι_ext_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_flex_wallet_code__right {b} (x: URValue DFlexClientLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlexClient_ι_flex_wallet_code_} || : _.
    
Definition DFlexClient_ι_flex_wallet_code__left (x: ULValue DFlexClientLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlexClient_ι_flex_wallet_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.flex_wallet_code_' " := ( DFlexClient_ι_flex_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.flex_wallet_code_' " := ( DFlexClient_ι_flex_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_flex_wrapper_code__right {b} (x: URValue DFlexClientLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlexClient_ι_flex_wrapper_code_} || : _.
    
Definition DFlexClient_ι_flex_wrapper_code__left (x: ULValue DFlexClientLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlexClient_ι_flex_wrapper_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.flex_wrapper_code_' " := ( DFlexClient_ι_flex_wrapper_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.flex_wrapper_code_' " := ( DFlexClient_ι_flex_wrapper_code__left a ) (in custom ULValue at level 0) : ursus_scope.


Definition SellArgs_ι_amount_right {b} (x: URValue SellArgsLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {SellArgs_ι_amount} || : _.
    
Definition SellArgs_ι_amount _left (x: ULValue SellArgsLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {SellArgs_ι_amount} }} : _.
    
Notation " a '↑' 'SellArgs.amount' " := ( SellArgs_ι_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'SellArgs.amount' " := ( SellArgs_ι_amount _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition SellArgs_ι_receive_wallet_right {b} (x: URValue SellArgsLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {SellArgs_ι_receive_wallet} || : _.
    
Definition SellArgs_ι_receive_wallet _left (x: ULValue SellArgsLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {SellArgs_ι_receive_wallet} }} : _.
    
Notation " a '↑' 'SellArgs.receive_wallet' " := ( SellArgs_ι_receive_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'SellArgs.receive_wallet' " := ( SellArgs_ι_receive_wallet _left a ) (in custom ULValue at level 0) : ursus_scope.

End ClassTypesNotations.


