Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import FinProof.Common.


Require Import Project.CommonNotations.
Require Import Contracts.TradingPair.ClassTypes.
(* Require Import Contracts.TradingPair.Ledger. *)

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition DTradingPair_ι_flex_addr__right {b} (x: URValue DTradingPairLRecord b): URValue XAddress b :=
    || {x} ^^ {DTradingPair_ι_flex_addr_} || : _.
    
Definition DTradingPair_ι_flex_addr__left (x: ULValue DTradingPairLRecord): ULValue XAddress :=
    {{ {x} ^^ {DTradingPair_ι_flex_addr_} }} : _.
    
Notation " a '↑' 'DTradingPair.flex_addr_' " := ( DTradingPair_ι_flex_addr__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTradingPair.flex_addr_' " := ( DTradingPair_ι_flex_addr__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTradingPair_ι_tip3_root__right {b} (x: URValue DTradingPairLRecord b): URValue XAddress b :=
    || {x} ^^ {DTradingPair_ι_tip3_root_} || : _.
    
Definition DTradingPair_ι_tip3_root__left (x: ULValue DTradingPairLRecord): ULValue XAddress :=
    {{ {x} ^^ {DTradingPair_ι_tip3_root_} }} : _.
    
Notation " a '↑' 'DTradingPair.tip3_root_' " := ( DTradingPair_ι_tip3_root__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTradingPair.tip3_root_' " := ( DTradingPair_ι_tip3_root__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTradingPair_ι_deploy_value__right {b} (x: URValue DTradingPairLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DTradingPair_ι_deploy_value_} || : _.
    
Definition DTradingPair_ι_deploy_value__left (x: ULValue DTradingPairLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DTradingPair_ι_deploy_value_} }} : _.
    
Notation " a '↑' 'DTradingPair.deploy_value_' " := ( DTradingPair_ι_deploy_value__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTradingPair.deploy_value_' " := ( DTradingPair_ι_deploy_value__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTradingPair_ι_min_amount__right {b} (x: URValue DTradingPairLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DTradingPair_ι_min_amount_} || : _.
    
Definition DTradingPair_ι_min_amount__left (x: ULValue DTradingPairLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DTradingPair_ι_min_amount_} }} : _.
    
Notation " a '↑' 'DTradingPair.min_amount_' " := ( DTradingPair_ι_min_amount__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTradingPair.min_amount_' " := ( DTradingPair_ι_min_amount__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DTradingPair_ι_notify_addr__right {b} (x: URValue DTradingPairLRecord b): URValue XAddress b :=
    || {x} ^^ {DTradingPair_ι_notify_addr_} || : _.
    
Definition DTradingPair_ι_notify_addr__left (x: ULValue DTradingPairLRecord): ULValue XAddress :=
    {{ {x} ^^ {DTradingPair_ι_notify_addr_} }} : _.
    
Notation " a '↑' 'DTradingPair.notify_addr_' " := ( DTradingPair_ι_notify_addr__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DTradingPair.notify_addr_' " := ( DTradingPair_ι_notify_addr__left a ) (in custom ULValue at level 0) : ursus_scope.

End ClassTypesNotations.
