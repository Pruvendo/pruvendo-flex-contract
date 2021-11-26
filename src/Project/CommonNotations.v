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

Definition addr_std_fixed_ι_workchain_id_right {b} (x: URValue addr_std_fixedLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {addr_std_fixed_ι_workchain_id} || : _ .
    
Definition addr_std_fixed_ι_workchain_id_left (x: ULValue addr_std_fixedLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {addr_std_fixed_ι_workchain_id} }} : _.
    
Notation " a '↑' 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition addr_std_fixed_ι_address_right {b} (x: URValue addr_std_fixedLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {addr_std_fixed_ι_address} || : _ .
    
Definition addr_std_fixed_ι_address_left (x: ULValue addr_std_fixedLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {addr_std_fixed_ι_address} }} : _.
    
Notation " a '↑' 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address_left a ) (in custom ULValue at level 0) : ursus_scope.

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


Definition Tip3Config_ι_root_address_right {b} (x: URValue Tip3ConfigLRecord b): URValue XAddress b :=
    || {x} ^^ {Tip3Config_ι_root_address} || : _ .
    
Definition Tip3Config_ι_root_address_left (x: ULValue Tip3ConfigLRecord): ULValue XAddress :=
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

Definition StateInit_ι_code_right {b} (x: URValue StateInitLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {StateInit_ι_code} || : _ .
    
Definition StateInit_ι_code_left (x: ULValue StateInitLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {StateInit_ι_code} }} : _.
    
Notation " a '↑' 'StateInit.code' " := ( StateInit_ι_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'StateInit.code' " := ( StateInit_ι_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition StateInit_ι_data_right {b} (x: URValue StateInitLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {StateInit_ι_data} || : _ .
    
Definition StateInit_ι_data_left (x: ULValue StateInitLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {StateInit_ι_data} }} : _.
    
Notation " a '↑' 'StateInit.data' " := ( StateInit_ι_data_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'StateInit.data' " := ( StateInit_ι_data_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition StateInit_ι_library_right {b} (x: URValue StateInitLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {StateInit_ι_library} || : _ .
    
Definition StateInit_ι_library_left (x: ULValue StateInitLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {StateInit_ι_library} }} : _.
    
Notation " a '↑' 'StateInit.library' " := ( StateInit_ι_library_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'StateInit.library' " := ( StateInit_ι_library_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition allowance_info_ι_spender_right {b} (x: URValue allowance_infoLRecord b): URValue XAddress b :=
    || {x} ^^ {allowance_info_ι_spender} || : _.
    
Definition allowance_info_ι_spender_left (x: ULValue allowance_infoLRecord): ULValue XAddress :=
    {{ {x} ^^ {allowance_info_ι_spender} }} : _.
    
Notation " a '↑' 'allowance_info.spender' " := ( allowance_info_ι_spender_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'allowance_info.spender' " := ( allowance_info_ι_spender_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition allowance_info_ι_remainingTokens_right {b} (x: URValue allowance_infoLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {allowance_info_ι_remainingTokens} || : _.
    
Definition allowance_info_ι_remainingTokens_left (x: ULValue allowance_infoLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {allowance_info_ι_remainingTokens} }} : _.
    
Notation " a '↑' 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition lend_record_ι_lend_balance_right {b} (x: URValue lend_recordLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {lend_record_ι_lend_balance} || : _.
    
Definition lend_record_ι_lend_balance_left (x: ULValue lend_recordLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {lend_record_ι_lend_balance} }} : _.
    
Notation " a '↑' 'lend_record.lend_balance' " := ( lend_record_ι_lend_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'lend_record.lend_balance' " := ( lend_record_ι_lend_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition lend_record_ι_lend_finish_time_right {b} (x: URValue lend_recordLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {lend_record_ι_lend_finish_time} || : _.
    
Definition lend_record_ι_lend_finish_time_left (x: ULValue lend_recordLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {lend_record_ι_lend_finish_time} }} : _.
    
Notation " a '↑' 'lend_record.lend_finish_time' " := ( lend_record_ι_lend_finish_time_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'lend_record.lend_finish_time' " := ( lend_record_ι_lend_finish_time_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition PayloadArgs_sell_right {b} (x: URValue PayloadArgsLRecord b): URValue XBool b :=
    || {x} ^^ {PayloadArgs_ι_sell} || : _ .

Definition PayloadArgs_amount_right {b} (x: URValue PayloadArgsLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {PayloadArgs_ι_amount} || : _ .

Definition PayloadArgs_receive_tip3_wallet_right {b} (x: URValue PayloadArgsLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {PayloadArgs_ι_receive_tip3_wallet} || : _ .

Definition PayloadArgs_client_addr_right {b} (x: URValue PayloadArgsLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {PayloadArgs_ι_client_addr} || : _ .

Definition PayloadArgs_sell_left (x: ULValue PayloadArgsLRecord): ULValue XBool :=
    {{ {x} ^^ {PayloadArgs_ι_sell} }} : _ .

Definition PayloadArgs_amount_left (x: ULValue PayloadArgsLRecord): ULValue XUInteger128:=
    {{ {x} ^^ {PayloadArgs_ι_amount} }} : _ .

Definition PayloadArgs_receive_tip3_wallet_left (x: ULValue PayloadArgsLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {PayloadArgs_ι_receive_tip3_wallet} }} : _ .

Definition PayloadArgs_client_addr_left (x: ULValue PayloadArgsLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {PayloadArgs_ι_client_addr} }} : _ .    


Notation " a '↑' 'PayloadArgs.sell' " := ( PayloadArgs_sell_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.sell' " := ( PayloadArgs_sell_left a ) (in custom ULValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.amount' " := ( PayloadArgs_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.amount' " := ( PayloadArgs_amount_left a ) (in custom ULValue at level 0) : ursus_scope.   
Notation " a '↑' 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_receive_tip3_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_receive_tip3_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.client_addr' " := ( PayloadArgs_client_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.client_addr' " := ( PayloadArgs_client_addr_left a ) (in custom ULValue at level 0) : ursus_scope.   

Definition OrderInfoXchg_original_amount_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderInfoXchg_ι_original_amount} || : _ .

Definition OrderInfoXchg_amount_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderInfoXchg_ι_amount} || : _ .

Definition OrderInfoXchg_account_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderInfoXchg_ι_account} || : _ .

Definition OrderInfoXchg_tip3_wallet_provide_right {b} (x: URValue OrderInfoXchgLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {OrderInfoXchg_ι_tip3_wallet_provide} || : _ .  

Definition OrderInfoXchg_tip3_wallet_receive_right {b} (x: URValue OrderInfoXchgLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {OrderInfoXchg_ι_tip3_wallet_receive} || : _ .

Definition OrderInfoXchg_client_addr_right {b} (x: URValue OrderInfoXchgLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {OrderInfoXchg_ι_client_addr} || : _ .

Definition OrderInfoXchg_order_finish_time_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {OrderInfoXchg_ι_order_finish_time} || : _ .  

Definition OrderInfoXchg_original_amount_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderInfoXchg_ι_original_amount} }} : _ .

Definition OrderInfoXchg_amount_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderInfoXchg_ι_amount} }} : _ .

Definition OrderInfoXchg_account_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderInfoXchg_ι_account} }} : _ .

Definition OrderInfoXchg_tip3_wallet_provide_left  (x: ULValue OrderInfoXchgLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {OrderInfoXchg_ι_tip3_wallet_provide} }} : _ .  

Definition OrderInfoXchg_tip3_wallet_receive_left  (x: ULValue OrderInfoXchgLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {OrderInfoXchg_ι_tip3_wallet_receive} }} : _ .

Definition OrderInfoXchg_client_addr_left  (x: ULValue OrderInfoXchgLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {OrderInfoXchg_ι_client_addr} }} : _ .

Definition OrderInfoXchg_order_finish_time_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {OrderInfoXchg_ι_order_finish_time} }} : _ .     

 
 Notation "  a '↑' 'OrderInfoXchg.original_amount' " := ( OrderInfoXchg_original_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.original_amount' " := ( OrderInfoXchg_original_amount_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.amount' " := ( OrderInfoXchg_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.amount' " := ( OrderInfoXchg_amount_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.account' " := ( OrderInfoXchg_account_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.account' " := ( OrderInfoXchg_account_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.tip3_wallet_provide' " := ( OrderInfoXchg_tip3_wallet_provide_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.tip3_wallet_provide' " := ( OrderInfoXchg_tip3_wallet_provide_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.tip3_wallet_receive' " := ( OrderInfoXchg_tip3_wallet_receive_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.tip3_wallet_receive' " := ( OrderInfoXchg_tip3_wallet_receive_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.client_addr' " := ( OrderInfoXchg_client_addr_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.client_addr' " := ( OrderInfoXchg_client_addr_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.order_finish_time' " := ( OrderInfoXchg_order_finish_time_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.order_finish_time' " := ( OrderInfoXchg_order_finish_time_right a) (in custom URValue at level 0) : ursus_scope. 
 
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

 Definition OrderInfo_amount_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
	|| {x} ^^ {OrderInfo_ι_amount} || : _.
	
Definition OrderInfo_amount_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_amount} }} : _.
	
Notation " a '↑' 'OrderInfo.amount' " := ( OrderInfo_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.amount' " := ( OrderInfo_amount_left a ) (in custom ULValue at level 0) : ursus_scope.
	
Definition OrderInfo_account_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfo_ι_account} || : _.

Definition OrderInfo_account_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_account} }} : _.

Notation " a '↑' 'OrderInfo.account' " := ( OrderInfo_account_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.account' " := ( OrderInfo_account_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition OrderInfo_order_finish_time_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfo_ι_order_finish_time} || : _.

Definition OrderInfo_order_finish_time_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_order_finish_time} }} : _.

Notation " a '↑' 'OrderInfo.order_finish_time' " := ( OrderInfo_order_finish_time_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.order_finish_time' " := ( OrderInfo_order_finish_time_left a ) (in custom ULValue at level 0) : ursus_scope.
	
Definition OrderInfo_original_amount_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfo_ι_original_amount} || : _.

Definition OrderInfo_original_amount_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_original_amount} }} : _.

Notation " a '↑' 'OrderInfo.original_amount' " := ( OrderInfo_original_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.original_amount' " := ( OrderInfo_original_amount_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition process_ret_sells_amount_right {b} (x: URValue process_retLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {process_ret_ι_sells_amount} || : _ .

Definition process_ret_sells__right {b} (x: URValue process_retLRecord b): URValue ( XQueue OrderInfoLRecord ) b :=
    || {x} ^^ {process_ret_ι_sells_} || : _ .

Definition process_ret_buys_amount_right {b} (x: URValue process_retLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {process_ret_ι_buys_amount} || : _ .

Definition process_ret_buys__right {b} (x: URValue process_retLRecord b): URValue ( XQueue OrderInfoLRecord ) b :=
    || {x} ^^ {process_ret_ι_buys_} || : _ .

Definition process_ret_ret__right {b} (x: URValue process_retLRecord b): URValue ( XMaybe OrderRetLRecord ) b :=
    || {x} ^^ {process_ret_ι_ret_} || : _ .  

Definition process_ret_sells_amount_left  (x: ULValue process_retLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {process_ret_ι_sells_amount} }} : _ .

Definition process_ret_sells__left  (x: ULValue process_retLRecord): ULValue ( XQueue OrderInfoLRecord ) :=
    {{ {x} ^^ {process_ret_ι_sells_} }} : _ .

Definition process_ret_buys_amount_left  (x: ULValue process_retLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {process_ret_ι_buys_amount} }} : _ .

Definition process_ret_buys__left  (x: ULValue process_retLRecord): ULValue ( XQueue OrderInfoLRecord ) :=
    {{ {x} ^^ {process_ret_ι_buys_} }} : _ .

Definition process_ret_ret__left  (x: ULValue process_retLRecord): ULValue ( XMaybe OrderRetLRecord ) :=
    {{ {x} ^^ {process_ret_ι_ret_} }} : _ .              

Notation " a '↑' 'process_ret.sells_amount' " := ( process_ret_sells_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.sells_amount' " := ( process_ret_sells_amount_right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.sells_' " := ( process_ret_sells__left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.sells_' " := ( process_ret_sells__right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.buys_amount' " := ( process_ret_buys_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.buys_amount' " := ( process_ret_buys_amount_right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.buys_' " := ( process_ret_buys__left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.buys_' " := ( process_ret_buys__right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.ret_' " := ( process_ret_ret__left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.ret_' " := ( process_ret_ret__right a) (in custom URValue at level 0) : ursus_scope. 
 

End CommonNotations.

