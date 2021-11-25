Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.XchgPair.ClassTypes.
Require Import Contracts.XchgPair.Ledger.

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition DXchgPair_ι_flex_addr__right {b} (x: URValue DXchgPairLRecord b): URValue XAddress b :=
    || {x} ^^ {DXchgPair_ι_flex_addr_} || : _.
    
Definition DXchgPair_ι_flex_addr__left (x: ULValue DXchgPairLRecord): ULValue XAddress :=
    {{ {x} ^^ {DXchgPair_ι_flex_addr_} }} : _.
    
Notation " a '↑' 'DXchgPair.flex_addr_' " := ( DXchgPair_ι_flex_addr__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DXchgPair.flex_addr_' " := ( DXchgPair_ι_flex_addr__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DXchgPair_ι_tip3_major_root__right {b} (x: URValue DXchgPairLRecord b): URValue XAddress b :=
    || {x} ^^ {DXchgPair_ι_tip3_major_root_} || : _ .
    
Definition DXchgPair_ι_tip3_major_root__left (x: ULValue DXchgPairLRecord): ULValue XAddress :=
    {{ {x} ^^ {DXchgPair_ι_tip3_major_root_} }} : _.
    
Notation " a '↑' 'DXchgPair.tip3_major_root_' " := ( DXchgPair_ι_tip3_major_root__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DXchgPair.tip3_major_root_' " := ( DXchgPair_ι_tip3_major_root__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DXchgPair_ι_tip3_minor_root__right {b} (x: URValue DXchgPairLRecord b): URValue XAddress b :=
    || {x} ^^ {DXchgPair_ι_tip3_minor_root_} || : _ .
    
Definition DXchgPair_ι_tip3_minor_root__left (x: ULValue DXchgPairLRecord): ULValue XAddress :=
    {{ {x} ^^ {DXchgPair_ι_tip3_minor_root_} }} : _.
    
Notation " a '↑' 'DXchgPair.tip3_minor_root_' " := ( DXchgPair_ι_tip3_minor_root__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DXchgPair.tip3_minor_root_' " := ( DXchgPair_ι_tip3_minor_root__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DXchgPair_ι_min_amount__right {b} (x: URValue DXchgPairLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DXchgPair_ι_min_amount_} || : _ .
    
Definition DXchgPair_ι_min_amount__left (x: ULValue DXchgPairLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DXchgPair_ι_min_amount_} }} : _.
    
Notation " a '↑' 'DXchgPair.min_amount_' " := ( DXchgPair_ι_min_amount__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DXchgPair.min_amount_' " := ( DXchgPair_ι_min_amount__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DXchgPair_ι_notify_addr__right {b} (x: URValue DXchgPairLRecord b): URValue XAddress b :=
    || {x} ^^ {DXchgPair_ι_notify_addr_} || : _ .
    
Definition DXchgPair_ι_notify_addr__left (x: ULValue DXchgPairLRecord): ULValue XAddress :=
    {{ {x} ^^ {DXchgPair_ι_notify_addr_} }} : _.
    
Notation " a '↑' 'DXchgPair.notify_addr_' " := ( DXchgPair_ι_notify_addr__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DXchgPair.notify_addr_' " := ( DXchgPair_ι_notify_addr__left a ) (in custom ULValue at level 0) : ursus_scope.

End ClassTypesNotations.


