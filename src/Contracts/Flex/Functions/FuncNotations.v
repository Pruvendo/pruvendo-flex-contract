
Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Require Import Project.CommonConstSig.

Require Import Contracts.Flex.Ledger.
Require Import Contracts.Flex.Functions.FuncSig.

(* здесь инмпортируем все внешние интерфейсы *)
Require Import Contracts.Flex.Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module FlexPublicInterface := Contracts.Flex.PublicInterface xt sm.
Module FlexClientPublicInterface := Contracts.FlexClient.PublicInterface xt sm.



Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Fail Check OutgoingMessage_default.

Import UrsusNotations.

Local Open Scope ursus_scope.

Notation " 'lend_record.lend_balance' " := ( lend_record_ι_lend_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_record.lend_balance' " := ( lend_record_ι_lend_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_record.lend_finish_time' " := ( lend_record_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_record.lend_finish_time' " := ( lend_record_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.spender' " := ( allowance_info_ι_spender ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.spender' " := ( allowance_info_ι_spender ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.name_' " := ( DWrapper_ι_name_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.name_' " := ( DWrapper_ι_name_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.symbol_' " := ( DWrapper_ι_symbol_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.symbol_' " := ( DWrapper_ι_symbol_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.decimals_' " := ( DWrapper_ι_decimals_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.decimals_' " := ( DWrapper_ι_decimals_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.workchain_id_' " := ( DWrapper_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.workchain_id_' " := ( DWrapper_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.root_public_key_' " := ( DWrapper_ι_root_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.root_public_key_' " := ( DWrapper_ι_root_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.total_granted_' " := ( DWrapper_ι_total_granted_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.total_granted_' " := ( DWrapper_ι_total_granted_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.internal_wallet_code_' " := ( DWrapper_ι_internal_wallet_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.internal_wallet_code_' " := ( DWrapper_ι_internal_wallet_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.owner_address_' " := ( DWrapper_ι_owner_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.owner_address_' " := ( DWrapper_ι_owner_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.start_balance_' " := ( DWrapper_ι_start_balance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.start_balance_' " := ( DWrapper_ι_start_balance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.external_wallet_' " := ( DWrapper_ι_external_wallet_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DWrapper.external_wallet_' " := ( DWrapper_ι_external_wallet_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.flex_addr_' " := ( DXchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.flex_addr_' " := ( DXchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.tip3_major_root_' " := ( DXchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.tip3_major_root_' " := ( DXchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.tip3_minor_root_' " := ( DXchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.tip3_minor_root_' " := ( DXchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.min_amount_' " := ( DXchgPair_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.min_amount_' " := ( DXchgPair_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.notify_addr_' " := ( DXchgPair_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.notify_addr_' " := ( DXchgPair_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.name_' " := ( DTONTokenWalletExternal_ι_name_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.name_' " := ( DTONTokenWalletExternal_ι_name_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.symbol_' " := ( DTONTokenWalletExternal_ι_symbol_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.symbol_' " := ( DTONTokenWalletExternal_ι_symbol_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.decimals_' " := ( DTONTokenWalletExternal_ι_decimals_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.decimals_' " := ( DTONTokenWalletExternal_ι_decimals_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.balance_' " := ( DTONTokenWalletExternal_ι_balance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.balance_' " := ( DTONTokenWalletExternal_ι_balance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.root_public_key_' " := ( DTONTokenWalletExternal_ι_root_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.root_public_key_' " := ( DTONTokenWalletExternal_ι_root_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.wallet_public_key_' " := ( DTONTokenWalletExternal_ι_wallet_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.wallet_public_key_' " := ( DTONTokenWalletExternal_ι_wallet_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.root_address_' " := ( DTONTokenWalletExternal_ι_root_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.root_address_' " := ( DTONTokenWalletExternal_ι_root_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.owner_address_' " := ( DTONTokenWalletExternal_ι_owner_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.owner_address_' " := ( DTONTokenWalletExternal_ι_owner_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.code_' " := ( DTONTokenWalletExternal_ι_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.code_' " := ( DTONTokenWalletExternal_ι_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.allowance_' " := ( DTONTokenWalletExternal_ι_allowance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.allowance_' " := ( DTONTokenWalletExternal_ι_allowance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.workchain_id_' " := ( DTONTokenWalletExternal_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.workchain_id_' " := ( DTONTokenWalletExternal_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.name_' " := ( DTONTokenWalletInternal_ι_name_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.name_' " := ( DTONTokenWalletInternal_ι_name_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.symbol_' " := ( DTONTokenWalletInternal_ι_symbol_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.symbol_' " := ( DTONTokenWalletInternal_ι_symbol_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.decimals_' " := ( DTONTokenWalletInternal_ι_decimals_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.decimals_' " := ( DTONTokenWalletInternal_ι_decimals_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.balance_' " := ( DTONTokenWalletInternal_ι_balance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.balance_' " := ( DTONTokenWalletInternal_ι_balance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.root_public_key_' " := ( DTONTokenWalletInternal_ι_root_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.root_public_key_' " := ( DTONTokenWalletInternal_ι_root_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.wallet_public_key_' " := ( DTONTokenWalletInternal_ι_wallet_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.wallet_public_key_' " := ( DTONTokenWalletInternal_ι_wallet_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.root_address_' " := ( DTONTokenWalletInternal_ι_root_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.root_address_' " := ( DTONTokenWalletInternal_ι_root_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.owner_address_' " := ( DTONTokenWalletInternal_ι_owner_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.owner_address_' " := ( DTONTokenWalletInternal_ι_owner_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.lend_ownership_' " := ( DTONTokenWalletInternal_ι_lend_ownership_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.lend_ownership_' " := ( DTONTokenWalletInternal_ι_lend_ownership_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.code_' " := ( DTONTokenWalletInternal_ι_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.code_' " := ( DTONTokenWalletInternal_ι_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.workchain_id_' " := ( DTONTokenWalletInternal_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.workchain_id_' " := ( DTONTokenWalletInternal_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.name' " := ( Tip3Config_ι_name ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.name' " := ( Tip3Config_ι_name ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.symbol' " := ( Tip3Config_ι_symbol ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.symbol' " := ( Tip3Config_ι_symbol ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.decimals' " := ( Tip3Config_ι_decimals ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.decimals' " := ( Tip3Config_ι_decimals ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.root_public_key' " := ( Tip3Config_ι_root_public_key ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.root_public_key' " := ( Tip3Config_ι_root_public_key ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.root_address' " := ( Tip3Config_ι_root_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.root_address' " := ( Tip3Config_ι_root_address ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.split_depth' " := ( StateInit_ι_split_depth ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.split_depth' " := ( StateInit_ι_split_depth ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.special' " := ( StateInit_ι_special ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.special' " := ( StateInit_ι_special ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.code' " := ( StateInit_ι_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.code' " := ( StateInit_ι_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.data' " := ( StateInit_ι_data ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.data' " := ( StateInit_ι_data ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.library' " := ( StateInit_ι_library ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.library' " := ( StateInit_ι_library ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.flex_addr_' " := ( DTradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.flex_addr_' " := ( DTradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.tip3_root_' " := ( DTradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.tip3_root_' " := ( DTradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.deploy_value_' " := ( DTradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.deploy_value_' " := ( DTradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 

 Notation " 'DTradingPair.min_amount_' " := ( DTradingPair_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.min_amount_' " := ( DTradingPair_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.notify_addr_' " := ( DTradingPair_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.notify_addr_' " := ( DTradingPair_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 

 Notation " 'TonsConfig.transfer_tip3' " := ( TonsConfig_ι_transfer_tip3 ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.transfer_tip3' " := ( TonsConfig_ι_transfer_tip3 ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( TonsConfig_ι_return_ownership ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( TonsConfig_ι_return_ownership ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( TonsConfig_ι_trading_pair_deploy ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( TonsConfig_ι_trading_pair_deploy ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.order_answer' " := ( TonsConfig_ι_order_answer ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.order_answer' " := ( TonsConfig_ι_order_answer ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.process_queue' " := ( TonsConfig_ι_process_queue ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.process_queue' " := ( TonsConfig_ι_process_queue ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.send_notify' " := ( TonsConfig_ι_send_notify ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.send_notify' " := ( TonsConfig_ι_send_notify ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.register_wrapper_cost' " := ( ListingConfig_ι_register_wrapper_cost ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.register_wrapper_cost' " := ( ListingConfig_ι_register_wrapper_cost ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.reject_wrapper_cost' " := ( ListingConfig_ι_reject_wrapper_cost ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.reject_wrapper_cost' " := ( ListingConfig_ι_reject_wrapper_cost ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.wrapper_deploy_value' " := ( ListingConfig_ι_wrapper_deploy_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.wrapper_deploy_value' " := ( ListingConfig_ι_wrapper_deploy_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.wrapper_keep_balance' " := ( ListingConfig_ι_wrapper_keep_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.wrapper_keep_balance' " := ( ListingConfig_ι_wrapper_keep_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.ext_wallet_balance' " := ( ListingConfig_ι_ext_wallet_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.ext_wallet_balance' " := ( ListingConfig_ι_ext_wallet_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.set_internal_wallet_value' " := ( ListingConfig_ι_set_internal_wallet_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.set_internal_wallet_value' " := ( ListingConfig_ι_set_internal_wallet_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.register_pair_cost' " := ( ListingConfig_ι_register_pair_cost ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.register_pair_cost' " := ( ListingConfig_ι_register_pair_cost ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.reject_pair_cost' " := ( ListingConfig_ι_reject_pair_cost ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.reject_pair_cost' " := ( ListingConfig_ι_reject_pair_cost ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.pair_deploy_value' " := ( ListingConfig_ι_pair_deploy_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.pair_deploy_value' " := ( ListingConfig_ι_pair_deploy_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.pair_keep_balance' " := ( ListingConfig_ι_pair_keep_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.pair_keep_balance' " := ( ListingConfig_ι_pair_keep_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.register_return_value' " := ( ListingConfig_ι_register_return_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'ListingConfig.register_return_value' " := ( ListingConfig_ι_register_return_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequest.client_addr' " := ( WrapperListingRequest_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequest.client_addr' " := ( WrapperListingRequest_ι_client_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequest.client_funds' " := ( WrapperListingRequest_ι_client_funds ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequest.client_funds' " := ( WrapperListingRequest_ι_client_funds ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequest.tip3cfg' " := ( WrapperListingRequest_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequest.tip3cfg' " := ( WrapperListingRequest_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequestWithPubkey.wrapper_pubkey' " := ( WrapperListingRequestWithPubkey_ι_wrapper_pubkey ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequestWithPubkey.wrapper_pubkey' " := ( WrapperListingRequestWithPubkey_ι_wrapper_pubkey ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequestWithPubkey.request' " := ( WrapperListingRequestWithPubkey_ι_request ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'WrapperListingRequestWithPubkey.request' " := ( WrapperListingRequestWithPubkey_ι_request ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.client_addr' " := ( TradingPairListingRequest_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.client_addr' " := ( TradingPairListingRequest_ι_client_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.client_funds' " := ( TradingPairListingRequest_ι_client_funds ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.client_funds' " := ( TradingPairListingRequest_ι_client_funds ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.tip3_root' " := ( TradingPairListingRequest_ι_tip3_root ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.tip3_root' " := ( TradingPairListingRequest_ι_tip3_root ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.min_amount' " := ( TradingPairListingRequest_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.min_amount' " := ( TradingPairListingRequest_ι_min_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.notify_addr' " := ( TradingPairListingRequest_ι_notify_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequest.notify_addr' " := ( TradingPairListingRequest_ι_notify_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequestWithPubkey.wrapper_pubkey' " := ( TradingPairListingRequestWithPubkey_ι_wrapper_pubkey ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequestWithPubkey.wrapper_pubkey' " := ( TradingPairListingRequestWithPubkey_ι_wrapper_pubkey ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequestWithPubkey.request' " := ( TradingPairListingRequestWithPubkey_ι_request ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPairListingRequestWithPubkey.request' " := ( TradingPairListingRequestWithPubkey_ι_request ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.client_addr' " := ( XchgPairListingRequest_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.client_addr' " := ( XchgPairListingRequest_ι_client_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.client_funds' " := ( XchgPairListingRequest_ι_client_funds ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.client_funds' " := ( XchgPairListingRequest_ι_client_funds ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.tip3_major_root' " := ( XchgPairListingRequest_ι_tip3_major_root ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.tip3_major_root' " := ( XchgPairListingRequest_ι_tip3_major_root ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.tip3_minor_root' " := ( XchgPairListingRequest_ι_tip3_minor_root ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.tip3_minor_root' " := ( XchgPairListingRequest_ι_tip3_minor_root ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.min_amount' " := ( XchgPairListingRequest_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.min_amount' " := ( XchgPairListingRequest_ι_min_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.notify_addr' " := ( XchgPairListingRequest_ι_notify_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequest.notify_addr' " := ( XchgPairListingRequest_ι_notify_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequestWithPubkey.request_pubkey' " := ( XchgPairListingRequestWithPubkey_ι_request_pubkey ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequestWithPubkey.request_pubkey' " := ( XchgPairListingRequestWithPubkey_ι_request_pubkey ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequestWithPubkey.request' " := ( XchgPairListingRequestWithPubkey_ι_request ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPairListingRequestWithPubkey.request' " := ( XchgPairListingRequestWithPubkey_ι_request ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.deployer_pubkey' " := ( FlexOwnershipInfo_ι_deployer_pubkey ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.deployer_pubkey' " := ( FlexOwnershipInfo_ι_deployer_pubkey ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.ownership_description' " := ( FlexOwnershipInfo_ι_ownership_description ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.ownership_description' " := ( FlexOwnershipInfo_ι_ownership_description ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.owner_contract' " := ( FlexOwnershipInfo_ι_owner_contract ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.owner_contract' " := ( FlexOwnershipInfo_ι_owner_contract ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.initialized' " := ( FlexDetails_ι_initialized ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.initialized' " := ( FlexDetails_ι_initialized ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.tons_cfg' " := ( FlexDetails_ι_tons_cfg ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.tons_cfg' " := ( FlexDetails_ι_tons_cfg ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.listing_cfg' " := ( FlexDetails_ι_listing_cfg ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.listing_cfg' " := ( FlexDetails_ι_listing_cfg ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.trading_pair_code' " := ( FlexDetails_ι_trading_pair_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.trading_pair_code' " := ( FlexDetails_ι_trading_pair_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.xchg_pair_code' " := ( FlexDetails_ι_xchg_pair_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.xchg_pair_code' " := ( FlexDetails_ι_xchg_pair_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.deals_limit' " := ( FlexDetails_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.deals_limit' " := ( FlexDetails_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.ownership' " := ( FlexDetails_ι_ownership ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.ownership' " := ( FlexDetails_ι_ownership ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.wrapper_listing_requests' " := ( FlexDetails_ι_wrapper_listing_requests ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.wrapper_listing_requests' " := ( FlexDetails_ι_wrapper_listing_requests ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.trading_pair_listing_requests' " := ( FlexDetails_ι_trading_pair_listing_requests ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.trading_pair_listing_requests' " := ( FlexDetails_ι_trading_pair_listing_requests ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.xchg_pair_listing_requests' " := ( FlexDetails_ι_xchg_pair_listing_requests ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDetails.xchg_pair_listing_requests' " := ( FlexDetails_ι_xchg_pair_listing_requests ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition deployer_pubkey__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType deployer_pubkey_ ) : ULValue XInteger256 ) . 
 Definition deployer_pubkey__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType deployer_pubkey_ ) : URValue XInteger256 false ) . 
 Notation " '_deployer_pubkey_' " := ( deployer_pubkey__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_deployer_pubkey_' " := ( deployer_pubkey__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : ULValue XInteger8 ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : URValue XInteger8 false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition ownership_description__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType ownership_description_ ) : ULValue XString ) . 
 Definition ownership_description__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType ownership_description_ ) : URValue XString false ) . 
 Notation " '_ownership_description_' " := ( ownership_description__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_ownership_description_' " := ( ownership_description__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition owner_address__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType owner_address_ ) : ULValue ( XMaybe XAddress ) ) . 
 Definition owner_address__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType owner_address_ ) : URValue ( XMaybe XAddress ) false ) . 
 Notation " '_owner_address_' " := ( owner_address__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_owner_address_' " := ( owner_address__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tons_cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : ULValue TonsConfigLRecord ) . 
 Definition tons_cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : URValue TonsConfigLRecord false ) . 
 Notation " '_tons_cfg_' " := ( tons_cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tons_cfg_' " := ( tons_cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition listing_cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType listing_cfg_ ) : ULValue ListingConfigLRecord ) . 
 Definition listing_cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType listing_cfg_ ) : URValue ListingConfigLRecord false ) . 
 Notation " '_listing_cfg_' " := ( listing_cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_listing_cfg_' " := ( listing_cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition pair_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType pair_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition pair_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType pair_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_pair_code_' " := ( pair_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_pair_code_' " := ( pair_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition xchg_pair_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition xchg_pair_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_xchg_pair_code_' " := ( xchg_pair_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_xchg_pair_code_' " := ( xchg_pair_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition price_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType price_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition price_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType price_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_price_code_' " := ( price_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_price_code_' " := ( price_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition xchg_price_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType xchg_price_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition xchg_price_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType xchg_price_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_xchg_price_code_' " := ( xchg_price_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_xchg_price_code_' " := ( xchg_price_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition ext_wallet_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType ext_wallet_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition ext_wallet_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType ext_wallet_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_ext_wallet_code_' " := ( ext_wallet_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_ext_wallet_code_' " := ( ext_wallet_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex_wallet_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType flex_wallet_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition flex_wallet_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType flex_wallet_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_flex_wallet_code_' " := ( flex_wallet_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_wallet_code_' " := ( flex_wallet_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition wrapper_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType wrapper_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition wrapper_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType wrapper_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_wrapper_code_' " := ( wrapper_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_wrapper_code_' " := ( wrapper_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition deals_limit__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : ULValue XInteger8 ) . 
 Definition deals_limit__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : URValue XInteger8 false ) . 
 Notation " '_deals_limit_' " := ( deals_limit__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_deals_limit_' " := ( deals_limit__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition wrapper_listing_requests__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType wrapper_listing_requests_ ) : ULValue ( (XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) ) ) . 
 Definition wrapper_listing_requests__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType wrapper_listing_requests_ ) : URValue ( (XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) ) false ) . 
 Notation " '_wrapper_listing_requests_' " := ( wrapper_listing_requests__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_wrapper_listing_requests_' " := ( wrapper_listing_requests__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition trading_pair_listing_requests__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType trading_pair_listing_requests_ ) : ULValue ( (XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord) ) ) ). 
 Definition trading_pair_listing_requests__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType trading_pair_listing_requests_ ) : URValue ( (XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord) ) ) false ) . 
 Notation " '_trading_pair_listing_requests_' " := ( trading_pair_listing_requests__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_trading_pair_listing_requests_' " := ( trading_pair_listing_requests__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition xchg_pair_listing_requests__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_listing_requests_ ) : ULValue ( (XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord) ) ) ) . 
 Definition xchg_pair_listing_requests__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_listing_requests_ ) : URValue ( (XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord) ) ) false ) . 
 Notation " '_xchg_pair_listing_requests_' " := ( xchg_pair_listing_requests__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_xchg_pair_listing_requests_' " := ( xchg_pair_listing_requests__right ) (in custom URValue at level 0) : ursus_scope. 
 
Notation " 'FLEX_TIMESTAMP_DELAY_' " := (sInject FLEX_TIMESTAMP_DELAY) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::sender_is_not_deployer' " := (sInject sender_is_not_deployer) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::unexpected_refs_count_in_code' " := (sInject unexpected_refs_count_in_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::cant_override_code' " := (sInject cant_override_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::sender_is_not_my_owner' " := (sInject sender_is_not_my_owner) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::not_enough_funds' " := (sInject not_enough_funds) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::wrapper_not_requested' " := (sInject wrapper_not_requested) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::trading_pair_not_requested' " := (sInject trading_pair_not_requested) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::xchg_pair_not_requested' " := (sInject xchg_pair_not_requested) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::costs_inconsistency' " := (sInject costs_inconsistency) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::wrapper_with_such_pubkey_already_requested' " := (sInject wrapper_with_such_pubkey_already_requested) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::trading_pair_with_such_pubkey_already_requested' " := (sInject trading_pair_with_such_pubkey_already_requested) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::xchg_pair_with_such_pubkey_already_requested' " := (sInject xchg_pair_with_such_pubkey_already_requested) (in custom URValue at level 0) : ursus_scope. 

Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.


 Definition constructor_left { R a1 a2 a3 a4 a5 a6 }  
( deployer_pubkey : URValue ( XInteger256 ) a1 ) 
( ownership_description : URValue ( XString ) a2 ) 
( owner_address : URValue ( XMaybe XAddress ) a3 ) 
( tons_cfg : URValue ( TonsConfigLRecord ) a4 ) 
( deals_limit : URValue ( XInteger8 ) a5 ) 
( listing_cfg : URValue ( ListingConfigLRecord ) a6 ) 
: UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) constructor 
 deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg ) . 
 
 Notation " 'constructor_' '(' deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg ')' " := 
 ( constructor_left 
 deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg ) 
 (in custom ULValue at level 0 , deployer_pubkey custom URValue at level 0 
 , ownership_description custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , tons_cfg custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition setSpecificCode_left { R a1 a2 }  ( type : URValue ( XInteger8 ) a1 ) ( code : URValue ( XCell ) a2 ) : UExpression R ( orb a2 a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) setSpecificCode 
 type code ) . 
 
 Notation " 'setSpecificCode_' '(' type code ')' " := 
 ( setSpecificCode_left 
 type code ) 
 (in custom ULValue at level 0 , type custom URValue at level 0 
 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setPairCode_left { R a1 }  ( code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setPairCode 
 code ) . 
 
 Notation " 'setPairCode_' '(' code ')' " := 
 ( setPairCode_left 
 code ) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setXchgPairCode_left { R a1 }  ( code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setXchgPairCode 
 code ) . 
 
 Notation " 'setXchgPairCode_' '(' code ')' " := 
 ( setXchgPairCode_left 
 code ) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setWrapperCode_left { R a1 }  ( code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setWrapperCode 
 code ) . 
 
 Notation " 'setWrapperCode_' '(' code ')' " := 
 ( setWrapperCode_left 
 code ) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setPriceCode_left { R a1 }  ( code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setPriceCode 
 code ) . 
 
 Notation " 'setPriceCode_' '(' code ')' " := 
 ( setPriceCode_left 
 code ) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setXchgPriceCode_left { R a1 }  ( code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setXchgPriceCode 
 code ) . 
 
 Notation " 'setXchgPriceCode_' '(' code ')' " := 
 ( setXchgPriceCode_left 
 code ) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setExtWalletCode_left { R a1 }  ( code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setExtWalletCode 
 code ) . 
 
 Notation " 'setExtWalletCode_' '(' code ')' " := 
 ( setExtWalletCode_left 
 code ) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setFlexWalletCode_left { R a1 }  ( code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setFlexWalletCode 
 code ) . 
 
 Notation " 'setFlexWalletCode_' '(' code ')' " := 
 ( setFlexWalletCode_left 
 code ) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_left { R a1 a2 }  ( tto : URValue ( XAddress ) a1 ) ( tons : URValue ( XInteger128 ) a2 ) : UExpression R true (* ( orb a2 a1 ) *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) transfer 
 tto tons ) . 
 
 Notation " 'transfer_' '(' tto tons ')' " := 
 ( transfer_left 
 tto tons ) 
 (in custom ULValue at level 0 , tto custom URValue at level 0 
 , tons custom URValue at level 0 ) : ursus_scope . 
 Definition registerTradingPair_right { a1 a2 a3 a4 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( tip3_root : URValue ( XAddress ) a2 ) ( min_amount : URValue ( XInteger128 ) a3 ) ( notify_addr : URValue ( XAddress ) a4 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) registerTradingPair 
 pubkey tip3_root min_amount notify_addr ) . 
 
 Notation " 'registerTradingPair_' '(' pubkey tip3_root min_amount notify_addr ')' " := 
 ( registerTradingPair_right 
 pubkey tip3_root min_amount notify_addr ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , tip3_root custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

 Definition approveTradingPair_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XAddress true (* a1 *) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) approveTradingPair 
 pubkey ) .  
 
 Notation " 'approveTradingPair_' '(' pubkey ')' " := 
 ( approveTradingPair_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition rejectTradingPair_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XBool true (* a1 *) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) rejectTradingPair 
 pubkey ) . 
 
 Notation " 'rejectTradingPair_' '(' pubkey ')' " := 
 ( rejectTradingPair_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition registerXchgPair_right { a1 a2 a3 a4 a5 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( tip3_major_root : URValue ( XAddress ) a2 ) ( tip3_minor_root : URValue ( XAddress ) a3 ) ( min_amount : URValue ( XInteger128 ) a4 ) ( notify_addr : URValue ( XAddress ) a5 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) registerXchgPair 
 pubkey tip3_major_root tip3_minor_root min_amount notify_addr ) . 
 
 Notation " 'registerXchgPair_' '(' pubkey tip3_major_root tip3_minor_root min_amount notify_addr ')' " := 
 ( registerXchgPair_right 
 pubkey tip3_major_root tip3_minor_root min_amount notify_addr ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

 Definition approveXchgPair_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XAddress true (* a1 *) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) approveXchgPair 
 pubkey ) . 
 
 Notation " 'approveXchgPair_' '(' pubkey ')' " := 
 ( approveXchgPair_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition rejectXchgPair_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XBool true (* a1 *) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) rejectXchgPair 
 pubkey ) . 
 
 Notation " 'rejectXchgPair_' '(' pubkey ')' " := 
 ( rejectXchgPair_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition registerWrapper_right { a1 a2 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a2 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) registerWrapper 
 pubkey tip3cfg ) . 
 
 Notation " 'registerWrapper_' '(' pubkey tip3cfg ')' " := 
 ( registerWrapper_right 
 pubkey tip3cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 

 Definition approveWrapper_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XAddress true (* a1 *) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) approveWrapper 
 pubkey ) . 
 
 Notation " 'approveWrapper_' '(' pubkey ')' " := 
 ( approveWrapper_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition rejectWrapper_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XBool true (* a1 *) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) rejectWrapper 
 pubkey ) . 
 
 Notation " 'rejectWrapper_' '(' pubkey ')' " := 
 ( rejectWrapper_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition isFullyInitialized_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) isFullyInitialized 
 ) . 
 
 Notation " 'isFullyInitialized_' '(' ')' " := 
 ( isFullyInitialized_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getDetails_right  : URValue FlexDetailsLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDetails 
 ) . 
 
 Notation " 'getDetails_' '(' ')' " := 
 ( getDetails_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getTonsCfg_right  : URValue TonsConfigLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTonsCfg 
 ) . 
 
 Notation " 'getTonsCfg_' '(' ')' " := 
 ( getTonsCfg_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getListingCfg_right  : URValue ListingConfigLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getListingCfg 
 ) . 
 
 Notation " 'getListingCfg_' '(' ')' " := 
 ( getListingCfg_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getTradingPairCode_right  : URValue XCell false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTradingPairCode 
 ) . 
 
 Notation " 'getTradingPairCode_' '(' ')' " := 
 ( getTradingPairCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getXchgPairCode_right  : URValue XCell false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getXchgPairCode 
 ) . 
 
 Notation " 'getXchgPairCode_' '(' ')' " := 
 ( getXchgPairCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getSellPriceCode_right { a1 }  ( tip3_addr : URValue ( XAddress ) a1 ) : URValue XCell true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) getSellPriceCode 
 tip3_addr ) . 
 
 Notation " 'getSellPriceCode_' '(' tip3_addr ')' " := 
 ( getSellPriceCode_right 
 tip3_addr ) 
 (in custom URValue at level 0 , tip3_addr custom URValue at level 0 ) : ursus_scope . 
 Definition getXchgPriceCode_right { a1 a2 }  ( tip3_addr1 : URValue ( XAddress ) a1 ) ( tip3_addr2 : URValue ( XAddress ) a2 ) : URValue XCell true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) getXchgPriceCode 
 tip3_addr1 tip3_addr2 ) . 
 
 Notation " 'getXchgPriceCode_' '(' tip3_addr1 tip3_addr2 ')' " := 
 ( getXchgPriceCode_right 
 tip3_addr1 tip3_addr2 ) 
 (in custom URValue at level 0 , tip3_addr1 custom URValue at level 0 
 , tip3_addr2 custom URValue at level 0 ) : ursus_scope . 
 Definition getSellTradingPair_right { a1 }  ( tip3_root : URValue ( XAddress ) a1 ) : URValue XAddress a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) getSellTradingPair 
 tip3_root ) . 
 
 Notation " 'getSellTradingPair_' '(' tip3_root ')' " := 
 ( getSellTradingPair_right 
 tip3_root ) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 ) : ursus_scope . 
 Definition getXchgTradingPair_right { a1 a2 }  ( tip3_major_root : URValue ( XAddress ) a1 ) ( tip3_minor_root : URValue ( XAddress ) a2 ) : URValue XAddress ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) getXchgTradingPair 
 tip3_major_root tip3_minor_root ) . 
 
 Notation " 'getXchgTradingPair_' '(' tip3_major_root tip3_minor_root ')' " := 
 ( getXchgTradingPair_right 
 tip3_major_root tip3_minor_root ) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 ) : ursus_scope . 
 Definition getDealsLimit_right  : URValue XInteger8 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDealsLimit 
 ) . 
 
 Notation " 'getDealsLimit_' '(' ')' " := 
 ( getDealsLimit_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getOwnershipInfo_right  : URValue FlexOwnershipInfoLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwnershipInfo 
 ) . 
 
 Notation " 'getOwnershipInfo_' '(' ')' " := 
 ( getOwnershipInfo_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getWrapperListingRequests_right  : URValue ( XHMap XInteger WrapperListingRequestWithPubkeyLRecord) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getWrapperListingRequests 
 ) . 
 
 Notation " 'getWrapperListingRequests_' '(' ')' " := 
 ( getWrapperListingRequests_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getTradingPairListingRequests_right  : URValue ( XHMap XInteger TradingPairListingRequestWithPubkeyLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTradingPairListingRequests 
 ) . 
 
 Notation " 'getTradingPairListingRequests_' '(' ')' " := 
 ( getTradingPairListingRequests_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getXchgPairListingRequests_right  : URValue ( XHMap XInteger XchgPairListingRequestWithPubkeyLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getXchgPairListingRequests 
 ) . 
 
 Notation " 'getXchgPairListingRequests_' '(' ')' " := 
 ( getXchgPairListingRequests_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition check_owner_left { R }  : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_owner 
 ) . 
 
 Notation " 'check_owner_' '(' ')' " := 
 ( check_owner_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 Definition _fallback_right { a1 a2 }  ( msg : URValue ( XCell ) a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue XInteger ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 msg msg_body ) . 
 
 Notation " '_fallback_' '(' msg msg_body ')' " := 
 ( _fallback_right 
 msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 
 Definition prepare_wrapper_state_init_and_addr_right { a1 a2 }  ( wrapper_code : URValue ( XCell ) a1 ) ( wrapper_data : URValue ( DWrapperLRecord ) a2 ) : URValue ( StateInitLRecord * XInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_wrapper_state_init_and_addr 
 wrapper_code wrapper_data ) . 
 
 Notation " 'prepare_wrapper_state_init_and_addr_' '(' wrapper_code wrapper_data ')' " := 
 ( prepare_wrapper_state_init_and_addr_right 
 wrapper_code wrapper_data ) 
 (in custom URValue at level 0 , wrapper_code custom URValue at level 0 
 , wrapper_data custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_flex_state_init_and_addr_right { a1 a2 }  ( flex_data : URValue ( ContractLRecord ) a1 ) ( flex_code : URValue ( XCell ) a2 ) : URValue ( StateInitLRecord * XInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_flex_state_init_and_addr 
 flex_data flex_code ) . 
 
 Notation " 'prepare_flex_state_init_and_addr_' '(' flex_data flex_code ')' " := 
 ( prepare_flex_state_init_and_addr_right 
 flex_data flex_code ) 
 (in custom URValue at level 0 , flex_data custom URValue at level 0 
 , flex_code custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_external_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XInteger8 ) a3 ) ( root_public_key : URValue ( XInteger256 ) a4 ) ( wallet_public_key : URValue ( XInteger256 ) a5 ) ( root_address : URValue ( XAddress ) a6 ) ( owner_address : URValue ( XMaybe XAddress ) a7 ) ( code : URValue ( XCell ) a8 ) ( workchain_id : URValue ( XInteger8 ) a9 ) : URValue ( StateInitLRecord * XInteger256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_external_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_external_wallet_state_init_and_addr_' '(' name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ')' " := 
 ( prepare_external_wallet_state_init_and_addr_right 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 
 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 
 , root_public_key custom URValue at level 0 
 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , code custom URValue at level 0 
 , workchain_id custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_internal_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XInteger8 ) a3 ) ( root_public_key : URValue ( XInteger256 ) a4 ) ( wallet_public_key : URValue ( XInteger256 ) a5 ) ( root_address : URValue ( XAddress ) a6 ) ( owner_address : URValue ( XMaybe XAddress ) a7 ) ( code : URValue ( XCell ) a8 ) ( workchain_id : URValue ( XInteger8 ) a9 ) : URValue ( StateInitLRecord * XInteger256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_internal_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_internal_wallet_state_init_and_addr_' '(' name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ')' " := 
 ( prepare_internal_wallet_state_init_and_addr_right 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 
 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 
 , root_public_key custom URValue at level 0 
 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , code custom URValue at level 0 
 , workchain_id custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_trading_pair_state_init_and_addr_right { a1 a2 }  ( pair_data : URValue ( DTradingPairLRecord ) a1 ) ( pair_code : URValue ( XCell ) a2 ) : URValue ( StateInitLRecord * XInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_trading_pair_state_init_and_addr 
 pair_data pair_code ) . 
 
 Notation " 'prepare_trading_pair_state_init_and_addr_' '(' pair_data pair_code ')' " := 
 ( prepare_trading_pair_state_init_and_addr_right 
 pair_data pair_code ) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 
 , pair_code custom URValue at level 0 ) : ursus_scope . 
 Definition prepare_trading_pair_right { a1 a2 a3 }  ( flex : URValue ( XAddress ) a1 ) ( tip3_root : URValue ( XAddress ) a2 ) ( pair_code : URValue ( XCell ) a3 ) : URValue ( StateInitLRecord * XInteger256 ) ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) prepare_trading_pair 
 flex tip3_root pair_code ) . 
 
 Notation " 'prepare_trading_pair_' '(' flex tip3_root pair_code ')' " := 
 ( prepare_trading_pair_right 
 flex tip3_root pair_code ) 
 (in custom URValue at level 0 , flex custom URValue at level 0 
 , tip3_root custom URValue at level 0 
 , pair_code custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_xchg_pair_state_init_and_addr_right { a1 a2 }  ( pair_data : URValue ( DXchgPairLRecord ) a1 ) ( pair_code : URValue ( XCell ) a2 ) : URValue ( StateInitLRecord * XInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_xchg_pair_state_init_and_addr 
 pair_data pair_code ) . 
 
 Notation " 'prepare_xchg_pair_state_init_and_addr_' '(' pair_data pair_code ')' " := 
 ( prepare_xchg_pair_state_init_and_addr_right 
 pair_data pair_code ) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 
 , pair_code custom URValue at level 0 ) : ursus_scope .

 Definition approveTradingPairImpl_right { a1 a2 a3 a4 a5 }  
( pubkey : URValue ( XInteger256 ) a1 ) 
( trading_pair_listing_requests : URValue ( XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord) ) a2 ) 
( pair_code : URValue ( XCell ) a3 )
 ( workchain_id : URValue ( XInteger8 ) a4 ) 
( listing_cfg : URValue ( ListingConfigLRecord ) a5 ) : URValue (XAddress * XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord)) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) approveTradingPairImpl 
 pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg ) . 
 
 Notation " 'approveTradingPairImpl_' '(' pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg ')' " := 
 ( approveTradingPairImpl_right 
 pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , trading_pair_listing_requests custom URValue at level 0 
 , pair_code custom URValue at level 0 
 , workchain_id custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

 Definition rejectTradingPairImpl_right { a1 a2 a3 }  
( pubkey : URValue ( XInteger256 ) a1 ) 
( trading_pair_listing_requests : URValue ( XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord ) ) a2 ) 
( listing_cfg : URValue ( ListingConfigLRecord ) a3 ) 
: URValue ( XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord ) ) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) rejectTradingPairImpl 
 pubkey trading_pair_listing_requests listing_cfg ) . 

 Notation " 'rejectTradingPairImpl_' '(' pubkey trading_pair_listing_requests listing_cfg ')' " := 
 ( rejectTradingPairImpl_right 
 pubkey trading_pair_listing_requests listing_cfg ) 
 (in custom URValue at level 0 , 
   pubkey custom URValue at level 0 
 , trading_pair_listing_requests custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope .
 
 Definition approveXchgPairImpl_right { a1 a2 a3 a4 a5 }  
( pubkey : URValue ( XInteger256 ) a1 )
 ( xchg_pair_listing_requests : URValue ( XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord) ) a2 ) 
( xchg_pair_code : URValue ( XCell ) a3 )
 ( workchain_id : URValue ( XInteger8 ) a4 ) 
( listing_cfg : URValue ( ListingConfigLRecord ) a5 ) :
 URValue ( XAddress * (XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord ) ) ) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) approveXchgPairImpl 
 pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg ) . 
 
 Notation " 'approveXchgPairImpl_' '(' pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg ')' " := 
 ( approveXchgPairImpl_right 
 pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , xchg_pair_listing_requests custom URValue at level 0 
 , xchg_pair_code custom URValue at level 0 
 , workchain_id custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

 Definition rejectXchgPairImpl_right { a1 a2 a3 }  
( pubkey : URValue ( XInteger256 ) a1 ) 
( xchg_pair_listing_requests : URValue ( XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord) ) a2 ) 
( listing_cfg : URValue ( ListingConfigLRecord ) a3 ) 
: URValue ( XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord) ) true := 

 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) rejectXchgPairImpl 
 pubkey xchg_pair_listing_requests listing_cfg ) . 
 
 Notation " 'rejectXchgPairImpl_' '(' pubkey xchg_pair_listing_requests listing_cfg ')' " := 
 ( rejectXchgPairImpl_right 
 pubkey xchg_pair_listing_requests listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , xchg_pair_listing_requests custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope .
 
 Definition approveWrapperImpl_right { a1 a2 a3 a4 a5 a6 a7 }  
( pubkey : URValue ( XInteger256 ) a1 ) 
( wrapper_listing_requests : URValue ( XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) a2 )
( wrapper_code : URValue ( XCell ) a3 ) 
( ext_wallet_code : URValue ( XCell ) a4 ) 
( flex_wallet_code : URValue ( XCell ) a5 )
 ( workchain_id : URValue ( XInteger8 ) a6 ) 
( listing_cfg : URValue ( ListingConfigLRecord ) a7 ) 
: URValue ( XAddress * (XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) ) true := 

 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) approveWrapperImpl 
 pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg ) . 
 
 Notation " 'approveWrapperImpl_' '(' pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg ')' " := 
 ( approveWrapperImpl_right 
 pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , wrapper_listing_requests custom URValue at level 0 
 , wrapper_code custom URValue at level 0 
 , ext_wallet_code custom URValue at level 0 
 , flex_wallet_code custom URValue at level 0 
 , workchain_id custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

 Definition rejectWrapperImpl_right { a1 a2 a3 }  
( pubkey : URValue ( XInteger256 ) a1 ) 
( wrapper_listing_requests : URValue ( XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) a2 ) 
( listing_cfg : URValue ( ListingConfigLRecord ) a3 ) 
: URValue ( XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) rejectWrapperImpl 
 pubkey wrapper_listing_requests listing_cfg ) . 
 
 Notation " 'rejectWrapperImpl_' '(' pubkey wrapper_listing_requests listing_cfg ')' " := 
 ( rejectWrapperImpl_right 
 pubkey wrapper_listing_requests listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , wrapper_listing_requests custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

End Calls. 

End FuncNotations.