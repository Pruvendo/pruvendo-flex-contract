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


Definition transfer_tip3_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger b :=
    || {x} ^^ {TonsConfig_ι_transfer_tip3} || : _ .
    
Definition transfer_tip3_left (x: ULValue TonsConfigLRecord): ULValue XUInteger :=
    {{ {x} ^^ {TonsConfig_ι_transfer_tip3} }} : _.
    
Notation " a '↑' 'TonsConfig.transfer_tip3' " := ( transfer_tip3_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.transfer_tip3' " := ( transfer_tip3_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition trading_pair_deploy_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger b :=
    || {x} ^^ {TonsConfig_ι_trading_pair_deploy} || : _ .
    
Definition trading_pair_deploy_left (x: ULValue TonsConfigLRecord): ULValue XUInteger :=
    {{ {x} ^^ {TonsConfig_ι_trading_pair_deploy} }} : _.
    
Notation " a '↑' 'TonsConfig.trading_pair_deploy' " := ( trading_pair_deploy_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.trading_pair_deploy' " := ( trading_pair_deploy_left a ) (in custom ULValue at level 0) : ursus_scope.

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




Definition tick_right {b} (x: URValue TickTockLRecord b): URValue XBool b :=
|| {x} ^^ {TickTock_ι_tick} || : _.

Definition tick_left (x: ULValue TickTockLRecord): ULValue XBool :=
{{ {x} ^^ {TickTock_ι_tick} }} : _.

Notation " a '↑' 'TickTock.tick' " := ( tick_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TickTock.tick' " := ( tick_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition tock_right {b} (x: URValue TickTockLRecord b): URValue XBool b :=
|| {x} ^^ {TickTock_ι_tock} || : _.

Definition tock_left (x: ULValue TickTockLRecord): ULValue XBool :=
{{ {x} ^^ {TickTock_ι_tock} }} : _.

Notation " a '↑' 'TickTock.tock' " := ( tock_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TickTock.tock' " := ( tock_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition workchain_id_right {b} (x: URValue addr_std_fixedLRecord b): URValue XUInteger8 b :=
|| {x} ^^ {addr_std_fixed_ι_workchain_id} || : _.

Definition workchain_id_left (x: ULValue addr_std_fixedLRecord): ULValue XUInteger8 :=
{{ {x} ^^ {addr_std_fixed_ι_workchain_id} }} : _.

Notation " a '↑' 'addr_std_fixed.workchain_id' " := ( workchain_id_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'addr_std_fixed.workchain_id' " := ( workchain_id_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition address_right {b} (x: URValue addr_std_fixedLRecord b): URValue XUInteger256 b :=
|| {x} ^^ {addr_std_fixed_ι_address} || : _.

Definition address_left (x: ULValue addr_std_fixedLRecord): ULValue XUInteger256 :=
{{ {x} ^^ {addr_std_fixed_ι_address} }} : _.

Notation " a '↑' 'addr_std_fixed.address' " := ( address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'addr_std_fixed.address' " := ( address_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition name_right {b} (x: URValue Tip3ConfigLRecord b): URValue XString b :=
|| {x} ^^ {Tip3Config_ι_name} || : _.

Definition name_left (x: ULValue Tip3ConfigLRecord): ULValue XString :=
{{ {x} ^^ {Tip3Config_ι_name} }} : _.

Notation " a '↑' 'Tip3Config.name' " := ( name_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.name' " := ( name_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition symbol_right {b} (x: URValue Tip3ConfigLRecord b): URValue XString b :=
|| {x} ^^ {Tip3Config_ι_symbol} || : _.

Definition symbol_left (x: ULValue Tip3ConfigLRecord): ULValue XString :=
{{ {x} ^^ {Tip3Config_ι_symbol} }} : _.

Notation " a '↑' 'Tip3Config.symbol' " := ( symbol_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.symbol' " := ( symbol_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition decimals_right {b} (x: URValue Tip3ConfigLRecord b): URValue XUInteger8 b :=
|| {x} ^^ {Tip3Config_ι_decimals} || : _.

Definition decimals_left (x: ULValue Tip3ConfigLRecord): ULValue XUInteger8 :=
{{ {x} ^^ {Tip3Config_ι_decimals} }} : _.

Notation " a '↑' 'Tip3Config.decimals' " := ( decimals_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.decimals' " := ( decimals_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition root_public_key_right {b} (x: URValue Tip3ConfigLRecord b): URValue XUInteger256 b :=
|| {x} ^^ {Tip3Config_ι_root_public_key} || : _.

Definition root_public_key_left (x: ULValue Tip3ConfigLRecord): ULValue XUInteger256 :=
{{ {x} ^^ {Tip3Config_ι_root_public_key} }} : _.

Notation " a '↑' 'Tip3Config.root_public_key' " := ( root_public_key_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.root_public_key' " := ( root_public_key_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition root_address_right {b} (x: URValue Tip3ConfigLRecord b): URValue XAddress b :=
|| {x} ^^ {Tip3Config_ι_root_address} || : _.

Definition root_address_left (x: ULValue Tip3ConfigLRecord): ULValue XAddress :=
{{ {x} ^^ {Tip3Config_ι_root_address} }} : _.

Notation " a '↑' 'Tip3Config.root_address' " := ( root_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.root_address' " := ( root_address_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition workchain_id__right {b} (x: URValue Tip3ConfigLRecord b): URValue XUInteger8 b :=
|| {x} ^^ {Tip3Config_ι_workchain_id_} || : _.

Definition workchain_id__left (x: ULValue Tip3ConfigLRecord): ULValue XUInteger8 :=
{{ {x} ^^ {Tip3Config_ι_workchain_id_} }} : _.

Notation " a '↑' 'Tip3Config.workchain_id_' " := ( workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.workchain_id_' " := ( workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.


End CommonNotations.

