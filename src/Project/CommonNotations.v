Require Import Strings.String.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import CommonTypes.

Module CommonNotations (xt : XTypesSig) (sm : StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export tvmNotationsModule := tvmNotations xt sm cs. 
Module Export TypesModule := Types xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope string_scope.

Notation UE := (UExpression _ _) (only parsing).
Notation UEf := (UExpression _ false) (only parsing).
Notation UEt := (UExpression _ true) (only parsing).

Notation " 'public' x " := ( x ) (at level 12, left associativity, only parsing) : ursus_scope .
Notation " 'private' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .

Arguments urgenerate_field {_} {_} {_} _ {_} & _.

Notation " |{ e }| " := e (in custom URValue at level 0, e custom ULValue , only parsing ) : ursus_scope.
Notation " {| e |} " := e (in custom ULValue at level 0, e custom URValue , only parsing ) : ursus_scope.

Definition TonsConfig_ι_transfer_tip3_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TonsConfig_ι_transfer_tip3} || : _ .
    
Definition TonsConfig_ι_transfer_tip3_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TonsConfig_ι_transfer_tip3} }} : _.
    
Notation " a '↑' 'TonsConfig.transfer_tip3' " := ( TonsConfig_ι_transfer_tip3_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.transfer_tip3' " := ( TonsConfig_ι_transfer_tip3_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TonsConfig_ι_return_ownership_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TonsConfig_ι_return_ownership} || : _ .
    
Definition TonsConfig_ι_return_ownership_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TonsConfig_ι_return_ownership} }} : _.
    
Notation " a '↑' 'TonsConfig.return_ownership' " := ( TonsConfig_ι_return_ownership_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.return_ownership' " := ( TonsConfig_ι_return_ownership_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TonsConfig_ι_trading_pair_deploy_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TonsConfig_ι_trading_pair_deploy} || : _ .
    
Definition TonsConfig_ι_trading_pair_deploy_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TonsConfig_ι_trading_pair_deploy} }} : _.
    
Notation " a '↑' 'TonsConfig.trading_pair_deploy' " := ( TonsConfig_ι_trading_pair_deploy_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.trading_pair_deploy' " := ( TonsConfig_ι_trading_pair_deploy_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TonsConfig_ι_order_answer_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TonsConfig_ι_order_answer} || : _ .
    
Definition TonsConfig_ι_order_answer_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TonsConfig_ι_order_answer} }} : _.
    
Notation " a '↑' 'TonsConfig.order_answer' " := ( TonsConfig_ι_order_answer_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.order_answer' " := ( TonsConfig_ι_order_answer_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TonsConfig_ι_process_queue_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TonsConfig_ι_process_queue} || : _ .
    
Definition TonsConfig_ι_process_queue_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TonsConfig_ι_process_queue} }} : _.
    
Notation " a '↑' 'TonsConfig.process_queue' " := ( TonsConfig_ι_process_queue_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.process_queue' " := ( TonsConfig_ι_process_queue_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TonsConfig_ι_send_notify_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TonsConfig_ι_send_notify} || : _ .
    
Definition TonsConfig_ι_send_notify_left (x: ULValue TonsConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TonsConfig_ι_send_notify} }} : _.
    
Notation " a '↑' 'TonsConfig.send_notify' " := ( TonsConfig_ι_send_notify_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TonsConfig.send_notify' " := ( TonsConfig_ι_send_notify_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TickTock_ι_tick_right {b} (x: URValue TickTockLRecord b): URValue XBool b :=
    || {x} ^^ {TickTock_ι_tick} || : _ .
    
Definition TickTock_ι_tick_left (x: ULValue TickTockLRecord): ULValue XBool :=
    {{ {x} ^^ {TickTock_ι_tick} }} : _.
    
Notation " a '↑' 'TickTock.tick' " := ( TickTock_ι_tick_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TickTock.tick' " := ( TickTock_ι_tick_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TickTock_ι_tock_right {b} (x: URValue TickTockLRecord b): URValue XBool b :=
    || {x} ^^ {TickTock_ι_tock} || : _ .
    
Definition TickTock_ι_tock_left (x: ULValue TickTockLRecord): ULValue XBool :=
    {{ {x} ^^ {TickTock_ι_tock} }} : _.
    
Notation " a '↑' 'TickTock.tock' " := ( TickTock_ι_tock_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TickTock.tock' " := ( TickTock_ι_tock_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition Tip3Config_ι_name_right {b} (x: URValue Tip3ConfigLRecord b): URValue XString b :=
    || {x} ^^ {Tip3Config_ι_name} || : _ .
    
Definition Tip3Config_ι_name_left (x: ULValue Tip3ConfigLRecord): ULValue XString :=
    {{ {x} ^^ {Tip3Config_ι_name} }} : _.
    
Notation " a '↑' 'Tip3Config.name' " := ( Tip3Config_ι_name_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.name' " := ( Tip3Config_ι_name_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition Tip3Config_ι_symbol_right {b} (x: URValue Tip3ConfigLRecord b): URValue XString b :=
    || {x} ^^ {Tip3Config_ι_symbol} || : _ .
    
Definition Tip3Config_ι_symbol_left (x: ULValue Tip3ConfigLRecord): ULValue XString :=
    {{ {x} ^^ {Tip3Config_ι_symbol} }} : _.
    
Notation " a '↑' 'Tip3Config.symbol' " := ( Tip3Config_ι_symbol_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.symbol' " := ( Tip3Config_ι_symbol_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition Tip3Config_ι_decimals_right {b} (x: URValue Tip3ConfigLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {Tip3Config_ι_decimals} || : _ .
    
Definition Tip3Config_ι_decimals_left (x: ULValue Tip3ConfigLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {Tip3Config_ι_decimals} }} : _.
    
Notation " a '↑' 'Tip3Config.decimals' " := ( Tip3Config_ι_decimals_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.decimals' " := ( Tip3Config_ι_decimals_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition Tip3Config_ι_root_public_key_right {b} (x: URValue Tip3ConfigLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {Tip3Config_ι_root_public_key} || : _ .
    
Definition Tip3Config_ι_root_public_key_left (x: ULValue Tip3ConfigLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {Tip3Config_ι_root_public_key} }} : _.
    
Notation " a '↑' 'Tip3Config.root_public_key' " := ( Tip3Config_ι_root_public_key_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.root_public_key' " := ( Tip3Config_ι_root_public_key_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition Tip3Config_ι_root_address_right {b} (x: URValue Tip3ConfigLRecord b): URValue address b :=
    || {x} ^^ {Tip3Config_ι_root_address} || : _ .
    
Definition Tip3Config_ι_root_address_left (x: ULValue Tip3ConfigLRecord): ULValue address :=
    {{ {x} ^^ {Tip3Config_ι_root_address} }} : _.
    
Notation " a '↑' 'Tip3Config.root_address' " := ( Tip3Config_ι_root_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.root_address' " := ( Tip3Config_ι_root_address_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition Tip3Config_ι_workchain_id__right {b} (x: URValue Tip3ConfigLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {Tip3Config_ι_workchain_id_} || : _ .
    
Definition Tip3Config_ι_workchain_id__left (x: ULValue Tip3ConfigLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {Tip3Config_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'Tip3Config.workchain_id_' " := ( Tip3Config_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.workchain_id_' " := ( Tip3Config_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition StateInit_ι_split_depth_right {b} (x: URValue StateInitLRecord b): URValue ( XMaybe XUInteger ) b :=
    || {x} ^^ {StateInit_ι_split_depth} || : _ .
    
Definition StateInit_ι_split_depth_left (x: ULValue StateInitLRecord): ULValue ( XMaybe XUInteger ) :=
    {{ {x} ^^ {StateInit_ι_split_depth} }} : _.
    
Notation " a '↑' 'StateInit.split_depth' " := ( StateInit_ι_split_depth_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'StateInit.split_depth' " := ( StateInit_ι_split_depth_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition StateInit_ι_special_right {b} (x: URValue StateInitLRecord b): URValue ( XMaybe TickTockLRecord ) b :=
    || {x} ^^ {StateInit_ι_special} || : _ .
    
Definition StateInit_ι_special_left (x: ULValue StateInitLRecord): ULValue ( XMaybe TickTockLRecord ) :=
    {{ {x} ^^ {StateInit_ι_special} }} : _.
    
Notation " a '↑' 'StateInit.special' " := ( StateInit_ι_special_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'StateInit.special' " := ( StateInit_ι_special_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition StateInit_ι_code_right {b} (x: URValue StateInitLRecord b): URValue ( XMaybe cell ) b :=
    || {x} ^^ {StateInit_ι_code} || : _ .
    
Definition StateInit_ι_code_left (x: ULValue StateInitLRecord): ULValue ( XMaybe cell ) :=
    {{ {x} ^^ {StateInit_ι_code} }} : _.
    
Notation " a '↑' 'StateInit.code' " := ( StateInit_ι_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'StateInit.code' " := ( StateInit_ι_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition StateInit_ι_data_right {b} (x: URValue StateInitLRecord b): URValue ( XMaybe cell ) b :=
    || {x} ^^ {StateInit_ι_data} || : _ .
    
Definition StateInit_ι_data_left (x: ULValue StateInitLRecord): ULValue ( XMaybe cell ) :=
    {{ {x} ^^ {StateInit_ι_data} }} : _.
    
Notation " a '↑' 'StateInit.data' " := ( StateInit_ι_data_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'StateInit.data' " := ( StateInit_ι_data_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition StateInit_ι_library_right {b} (x: URValue StateInitLRecord b): URValue ( XMaybe cell ) b :=
    || {x} ^^ {StateInit_ι_library} || : _ .
    
Definition StateInit_ι_library_left (x: ULValue StateInitLRecord): ULValue ( XMaybe cell ) :=
    {{ {x} ^^ {StateInit_ι_library} }} : _.
    
Notation " a '↑' 'StateInit.library' " := ( StateInit_ι_library_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'StateInit.library' " := ( StateInit_ι_library_left a ) (in custom ULValue at level 0) : ursus_scope.

(***********************)
Definition internal_msg_header_ι_function_id_right {b} (x: URValue internal_msg_headerLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {internal_msg_header_ι_function_id} || : _ .
    
Definition internal_msg_header_ι_function_id_left (x: ULValue internal_msg_headerLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {internal_msg_header_ι_function_id} }} : _.
    
Notation " a '↑' 'internal_msg_header.function_id' " := ( internal_msg_header_ι_function_id_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'internal_msg_header.function_id' " := ( internal_msg_header_ι_function_id_left a ) (in custom ULValue at level 0) : ursus_scope.

(* ---------------- *)
Definition int_msg_info_ι_ihr_disabled_right {b} (x: URValue int_msg_infoLRecord b): URValue XBool b :=
    || {x} ^^ {int_msg_info_ι_ihr_disabled} || : _ .
    
Definition int_msg_info_ι_ihr_disabled_left (x: ULValue int_msg_infoLRecord): ULValue XBool :=
    {{ {x} ^^ {int_msg_info_ι_ihr_disabled} }} : _.
    
Notation " a '↑' 'int_msg_info.ihr_disabled' " := ( int_msg_info_ι_ihr_disabled_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.ihr_disabled' " := ( int_msg_info_ι_ihr_disabled_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition int_msg_info_ι_bounce_right {b} (x: URValue int_msg_infoLRecord b): URValue XBool b :=
    || {x} ^^ {int_msg_info_ι_bounce} || : _ .
    
Definition int_msg_info_ι_bounce_left (x: ULValue int_msg_infoLRecord): ULValue XBool :=
    {{ {x} ^^ {int_msg_info_ι_bounce} }} : _.
    
Notation " a '↑' 'int_msg_info.bounce' " := ( int_msg_info_ι_bounce_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.bounce' " := ( int_msg_info_ι_bounce_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition int_msg_info_ι_bounced_right {b} (x: URValue int_msg_infoLRecord b): URValue XBool b :=
    || {x} ^^ {int_msg_info_ι_bounced} || : _ .
    
Definition int_msg_info_ι_bounced_left (x: ULValue int_msg_infoLRecord): ULValue XBool :=
    {{ {x} ^^ {int_msg_info_ι_bounced} }} : _.
    
Notation " a '↑' 'int_msg_info.bounced' " := ( int_msg_info_ι_bounced_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.bounced' " := ( int_msg_info_ι_bounced_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition int_msg_info_ι_src_right {b} (x: URValue int_msg_infoLRecord b): URValue address b :=
    || {x} ^^ {int_msg_info_ι_src} || : _ .
    
Definition int_msg_info_ι_src_left (x: ULValue int_msg_infoLRecord): ULValue address :=
    {{ {x} ^^ {int_msg_info_ι_src} }} : _.
    
Notation " a '↑' 'int_msg_info.src' " := ( int_msg_info_ι_src_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.src' " := ( int_msg_info_ι_src_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition int_msg_info_ι_dest_right {b} (x: URValue int_msg_infoLRecord b): URValue address b :=
    || {x} ^^ {int_msg_info_ι_dest} || : _ .
    
Definition int_msg_info_ι_dest_left (x: ULValue int_msg_infoLRecord): ULValue address :=
    {{ {x} ^^ {int_msg_info_ι_dest} }} : _.
    
Notation " a '↑' 'int_msg_info.dest' " := ( int_msg_info_ι_dest_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.dest' " := ( int_msg_info_ι_dest_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition int_msg_info_ι_value_right {b} (x: URValue int_msg_infoLRecord b): URValue CurrencyCollectionLRecord b :=
    || {x} ^^ {int_msg_info_ι_value} || : _ .
    
Definition int_msg_info_ι_value_left (x: ULValue int_msg_infoLRecord): ULValue CurrencyCollectionLRecord :=
    {{ {x} ^^ {int_msg_info_ι_value} }} : _.
    
Notation " a '↑' 'int_msg_info.value' " := ( int_msg_info_ι_value_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.value' " := ( int_msg_info_ι_value_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition int_msg_info_ι_ihr_fee_right {b} (x: URValue int_msg_infoLRecord b): URValue XUInteger16 b :=
    || {x} ^^ {int_msg_info_ι_ihr_fee} || : _ .
    
Definition int_msg_info_ι_ihr_fee_left (x: ULValue int_msg_infoLRecord): ULValue XUInteger16 :=
    {{ {x} ^^ {int_msg_info_ι_ihr_fee} }} : _.

Notation " a '↑' 'int_msg_info.ihr_fee' " := ( int_msg_info_ι_ihr_fee_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.ihr_fee' " := ( int_msg_info_ι_ihr_fee_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition int_msg_info_ι_fwd_fee_right {b} (x: URValue int_msg_infoLRecord b): URValue XUInteger16 b :=
    || {x} ^^ {int_msg_info_ι_fwd_fee} || : _ .
    
Definition int_msg_info_ι_fwd_fee_left (x: ULValue int_msg_infoLRecord): ULValue XUInteger16 :=
    {{ {x} ^^ {int_msg_info_ι_fwd_fee} }} : _.

Notation " a '↑' 'int_msg_info.fwd_fee' " := ( int_msg_info_ι_fwd_fee_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.fwd_fee' " := ( int_msg_info_ι_fwd_fee_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition int_msg_info_ι_created_lt_right {b} (x: URValue int_msg_infoLRecord b): URValue XUInteger64 b :=
    || {x} ^^ {int_msg_info_ι_created_lt} || : _ .
    
Definition int_msg_info_ι_created_lt_left (x: ULValue int_msg_infoLRecord): ULValue XUInteger64 :=
    {{ {x} ^^ {int_msg_info_ι_created_lt} }} : _.
    
Notation " a '↑' 'int_msg_info.created_lt' " := ( int_msg_info_ι_created_lt_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.created_lt' " := ( int_msg_info_ι_created_lt_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition int_msg_info_ι_created_at_right {b} (x: URValue int_msg_infoLRecord b): URValue XUInteger64 b :=
    || {x} ^^ {int_msg_info_ι_created_at} || : _ .
    
Definition int_msg_info_ι_created_at_left (x: ULValue int_msg_infoLRecord): ULValue XUInteger64 :=
    {{ {x} ^^ {int_msg_info_ι_created_at} }} : _.
    
Notation " a '↑' 'int_msg_info.created_at' " := ( int_msg_info_ι_created_at_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'int_msg_info.created_at' " := ( int_msg_info_ι_created_at_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition CurrencyCollection_ι_grams_right {b} (x: URValue CurrencyCollectionLRecord b): URValue XUInteger16 b :=
    || {x} ^^ {CurrencyCollection_ι_grams} || : _ .
    
Definition CurrencyCollection_ι_grams_left (x: ULValue CurrencyCollectionLRecord): ULValue XUInteger16 :=
    {{ {x} ^^ {CurrencyCollection_ι_grams} }} : _.
    
Notation " a '↑' 'CurrencyCollection.grams' " := ( CurrencyCollection_ι_grams_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'CurrencyCollection.grams' " := ( CurrencyCollection_ι_grams_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition CurrencyCollection_ι_other_right {b} (x: URValue CurrencyCollectionLRecord b): URValue ExtraCurrencyCollectionLRecord b :=
    || {x} ^^ {CurrencyCollection_ι_other} || : _ .
    
Definition CurrencyCollection_ι_other_left (x: ULValue CurrencyCollectionLRecord): ULValue ExtraCurrencyCollectionLRecord :=
    {{ {x} ^^ {CurrencyCollection_ι_other} }} : _.
    
Notation " a '↑' 'CurrencyCollection.other' " := ( CurrencyCollection_ι_other_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'CurrencyCollection.other' " := ( CurrencyCollection_ι_other_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition ExtraCurrencyCollection_ι_dict_right {b} (x: URValue ExtraCurrencyCollectionLRecord b): URValue (XHMap XUInteger32 XUInteger32) b :=
    || {x} ^^ {ExtraCurrencyCollection_ι_dict} || : _ .
    
Definition ExtraCurrencyCollection_ι_dict_left (x: ULValue ExtraCurrencyCollectionLRecord): ULValue (XHMap XUInteger32 XUInteger32) :=
    {{ {x} ^^ {ExtraCurrencyCollection_ι_dict} }} : _.
    
Notation " a '↑' 'ExtraCurrencyCollection.dict' " := ( ExtraCurrencyCollection_ι_dict_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ExtraCurrencyCollection.dict' " := ( ExtraCurrencyCollection_ι_dict_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition OrderRet_err_code_right {b} (x: URValue OrderRetLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {OrderRet_ι_err_code} || : _ .

Definition OrderRet_processed_right {b} (x: URValue OrderRetLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderRet_ι_processed} || : _ .

Definition OrderRet_enqueued_right {b} (x: URValue OrderRetLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderRet_ι_enqueued} || : _ .

Definition OrderRet_err_code_left  (x: ULValue OrderRetLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {OrderRet_ι_err_code} }} : _ .

Definition OrderRet_processed_left  (x: ULValue OrderRetLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderRet_ι_processed} }} : _ .

Definition OrderRet_enqueued_left  (x: ULValue OrderRetLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderRet_ι_enqueued} }} : _ .    

Notation " a '↑' 'OrderRet.err_code' " := ( OrderRet_err_code_left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'OrderRet.err_code' " := ( OrderRet_err_code_right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'OrderRet.processed' " := ( OrderRet_processed_left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'OrderRet.processed' " := ( OrderRet_processed_right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'OrderRet.enqueued' " := ( OrderRet_enqueued_left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'OrderRet.enqueued' " := ( OrderRet_enqueued_right a) (in custom URValue at level 0) : ursus_scope. 

Tactic Notation "vararg" ident(x) constr(ss) := 
let s := fresh x in 
let T := type of x in 
refine {{new 'x : T @ ss := {} ; {_} }} ;
refine {{ {x} := #{s} ; {_} }} ;
clear s.

End CommonNotations.

