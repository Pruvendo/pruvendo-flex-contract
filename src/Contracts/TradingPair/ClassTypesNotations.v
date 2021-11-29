Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import FinProof.Common.

Require Import Project.CommonNotations.
Require Import TradingPair.ClassTypes.
Require Import TradingPair.Interface. 

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.
Module Export InterfaceModule := PublicInterface xt sm.

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


(******************************************************)
Definition IonDeploy_right { a1 a2 a3 }  ( min_amount : URValue XUInteger128 a1 ) 
                                         ( deploy_value : URValue XUInteger128 a2 ) 
                                         ( notify_addr : URValue XAddress a3 ) : URValue ITradingPair (orb a1 (orb a2 a3)).
 pose proof (urvalue_bind min_amount (fun a => urvalue_bind deploy_value (fun b => urvalue_bind notify_addr (fun c => #(IonDeploy a b c : ITradingPair)))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'TradingPair.onDeploy' ( x , y , z ) " := (IonDeploy_right x y z)
(in custom URValue at level 0 , x custom URValue at level 0 , y custom URValue at level 0 , z custom URValue at level 0 ) : ursus_scope .
 
Definition _Icreate_right { a1 }  ( x : URValue StateInitLRecord a1 ) : URValue ITradingPair a1.
 pose proof (urvalue_bind x (fun x' => #(_Icreate x' : ITradingPair)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'TradingPair.deploy' ( x ) " := (_Icreate_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .
 

End ClassTypesNotations.
