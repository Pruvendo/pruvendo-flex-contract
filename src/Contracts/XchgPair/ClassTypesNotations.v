Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.

Require Import XchgPair.ClassTypes.
Require Import XchgPair.Interface.
(* Require Import XchgPair.Ledger. *)

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.
Module Export InterfaceModule := PublicInterface xt sm.

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

(*| IonDeploy : XUInteger128 -> XUInteger128 -> XAddress -> PublicInterfaceP *)
Definition IonDeploy_right { a1 a2 a3 }  ( min_amount : URValue XUInteger128 a1 ) 
                                         ( deploy_value : URValue XUInteger128 a2 ) 
                                         ( notify_addr : URValue XAddress a3 ) : URValue IXchgPair (orb a1 (orb a2 a3)).
 pose proof (urvalue_bind min_amount (fun a => urvalue_bind deploy_value (fun b => urvalue_bind notify_addr (fun c => #(IonDeploy a b c : IXchgPair)))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.onDeploy' ( x , y , z ) " := (IonDeploy_right x y z)
(in custom URValue at level 0 , x custom URValue at level 0 , y custom URValue at level 0 , z custom URValue at level 0 ) : ursus_scope .
 
Definition _Icreate_right { a1 }  ( x : URValue StateInitLRecord a1 ) : URValue IXchgPair a1.
 pose proof (urvalue_bind x (fun x' => #(_Icreate x' : IXchgPair)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '._create' ( x ) " := (_Icreate_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .
 

End ClassTypesNotations.


