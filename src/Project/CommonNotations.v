Require Import FinProof.ProgrammingWith.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmFunc.

Require Import CommonTypes.


Module CommonNotations (xt : XTypesSig) (sm : StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export tvmNotationsModule := tvmNotations xt sm cs. 
Module Export TypesModule := Types xt sm. 
Import UrsusNotations.
Local Open Scope ursus_scope.


Check eq_refl : XUInteger128 = field_type TonsConfig_ι_transfer_tip3.


Definition transfer_tip3_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger b :=
    || {x} ^^ {TonsConfig_ι_transfer_tip3} || : _ .
    
Definition transfer_tip3_left (x: ULValue TonsConfigLRecord): ULValue XUInteger :=
    {{ {x} ^^ {TonsConfig_ι_transfer_tip3} }} : _.
    
Notation " a '↑' 'TonsConfig.transfer_tip3' " := ( transfer_tip3_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.transfer_tip3' " := ( transfer_tip3_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition process_queue_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {TonsConfig_ι_process_queue} || : _.

Definition process_queue_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {TonsConfig_ι_process_queue} }} : _.

Notation " a '↑' 'TonsConfig.process_queue' " := ( process_queue_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.process_queue' " := ( process_queue_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition order_answer_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {TonsConfig_ι_order_answer} || : _.

Definition order_answer_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {TonsConfig_ι_order_answer} }} : _.

Notation " a '↑' 'TonsConfig.order_answer' " := ( order_answer_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.order_answer' " := ( order_answer_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition return_ownership_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {TonsConfig_ι_return_ownership} || : _.

Definition return_ownership_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {TonsConfig_ι_return_ownership} }} : _.

Notation " a '↑' 'TonsConfig.return_ownership' " := ( return_ownership_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.return_ownership' " := ( return_ownership_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition send_notify_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {TonsConfig_ι_send_notify} || : _.

Definition send_notify_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {TonsConfig_ι_send_notify} }} : _.

Notation " a '↑' 'TonsConfig.send_notify' " := ( send_notify_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.send_notify' " := ( send_notify_left a ) (in custom ULValue at level 0) : ursus_scope.

End CommonNotations.

