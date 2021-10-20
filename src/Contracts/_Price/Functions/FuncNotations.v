
Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Require Import Project.CommonConstSig.

Require Import Contracts.Price.Ledger.
Require Import Contracts.Price.Functions.FuncSig.

(* здесь инмпортируем все внешние интерфейсы *)
Require Import Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module PricePublicInterface := PublicInterface xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.

Check XQueue.
Import xt.

Import UrsusNotations.

Local Open Scope ursus_scope.



Notation " 'TickTock.tick' " := ( TickTock_ι_tick ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TickTock.tick' " := ( TickTock_ι_tick ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TickTock.tock' " := ( TickTock_ι_tock ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TickTock.tock' " := ( TickTock_ι_tock ) (in custom URValue at level 0) : ursus_scope. 
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
 Notation " 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address ) (in custom URValue at level 0) : ursus_scope. 
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
 Notation " 'OrderRet.err_code' " := ( OrderRet_ι_err_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.err_code' " := ( OrderRet_ι_err_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.processed' " := ( OrderRet_ι_processed ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.processed' " := ( OrderRet_ι_processed ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.enqueued' " := ( OrderRet_ι_enqueued ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.enqueued' " := ( OrderRet_ι_enqueued ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'SellArgs.amount' " := ( SellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'SellArgs.amount' " := ( SellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'SellArgs.receive_wallet' " := ( SellArgs_ι_receive_wallet ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'SellArgs.receive_wallet' " := ( SellArgs_ι_receive_wallet ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.original_amount' " := ( OrderInfo_ι_original_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.original_amount' " := ( OrderInfo_ι_original_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.amount' " := ( OrderInfo_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.amount' " := ( OrderInfo_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.account' " := ( OrderInfo_ι_account ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.account' " := ( OrderInfo_ι_account ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.tip3_wallet' " := ( OrderInfo_ι_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.tip3_wallet' " := ( OrderInfo_ι_tip3_wallet ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.client_addr' " := ( OrderInfo_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.client_addr' " := ( OrderInfo_ι_client_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.order_finish_time' " := ( OrderInfo_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfo.order_finish_time' " := ( OrderInfo_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfo.price' " := ( DetailsInfo_ι_price ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfo.price' " := ( DetailsInfo_ι_price ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfo.min_amount' " := ( DetailsInfo_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfo.min_amount' " := ( DetailsInfo_ι_min_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfo.sell_amount' " := ( DetailsInfo_ι_sell_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfo.sell_amount' " := ( DetailsInfo_ι_sell_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfo.buy_amount' " := ( DetailsInfo_ι_buy_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfo.buy_amount' " := ( DetailsInfo_ι_buy_amount ) (in custom URValue at level 0) : ursus_scope. 
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
 
 Definition price__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType price_ ) : ULValue XInteger128 ) . 
 Definition price__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType price_ ) : URValue XInteger128 false ) . 
 Notation " '_price_' " := ( price__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_price_' " := ( price__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition sells_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType sells_amount_ ) : ULValue XInteger128 ) . 
 Definition sells_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType sells_amount_ ) : URValue XInteger128 false ) . 
 Notation " '_sells_amount_' " := ( sells_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_sells_amount_' " := ( sells_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition buys_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType buys_amount_ ) : ULValue XInteger128 ) . 
 Definition buys_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType buys_amount_ ) : URValue XInteger128 false ) . 
 Notation " '_buys_amount_' " := ( buys_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_buys_amount_' " := ( buys_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : ULValue addr_std_fixedLRecord ) . 
 Definition flex__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : URValue addr_std_fixedLRecord false ) . 
 Notation " '_flex_' " := ( flex__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_' " := ( flex__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition min_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType min_amount_ ) : ULValue XInteger128 ) . 
 Definition min_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType min_amount_ ) : URValue XInteger128 false ) . 
 Notation " '_min_amount_' " := ( min_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_min_amount_' " := ( min_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition deals_limit__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : ULValue XInteger8 ) . 
 Definition deals_limit__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : URValue XInteger8 false ) . 
 Notation " '_deals_limit_' " := ( deals_limit__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_deals_limit_' " := ( deals_limit__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition notify_addr__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType notify_addr_ ) : ULValue XAddress ) . 
 Definition notify_addr__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType notify_addr_ ) : URValue XAddress false ) . 
 Notation " '_notify_addr_' " := ( notify_addr__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_notify_addr_' " := ( notify_addr__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : ULValue XInteger8 ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : URValue XInteger8 false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tons_cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : ULValue TonsConfigLRecord ) . 
 Definition tons_cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : URValue TonsConfigLRecord false ) . 
 Notation " '_tons_cfg_' " := ( tons_cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tons_cfg_' " := ( tons_cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tip3_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tip3_code_ ) : ULValue XCell ) . 
 Definition tip3_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tip3_code_ ) : URValue XCell false ) . 
 Notation " '_tip3_code_' " := ( tip3_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tip3_code_' " := ( tip3_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tip3cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tip3cfg_ ) : ULValue Tip3ConfigLRecord ) . 
 Definition tip3cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tip3cfg_ ) : URValue Tip3ConfigLRecord false ) . 
 Notation " '_tip3cfg_' " := ( tip3cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tip3cfg_' " := ( tip3cfg__right ) (in custom URValue at level 0) : ursus_scope. 

 Definition sells__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType sells_ ) : ULValue ( XQueue OrderInfoLRecord ) ) . 
 Definition sells__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType sells_ ) : URValue ( XQueue OrderInfoLRecord ) false ) . 
 Notation " '_sells_' " := ( sells__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_sells_' " := ( sells__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition buys__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType buys_ ) : ULValue ( XQueue OrderInfoLRecord ) ) . 
 Definition buys__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType buys_ ) : URValue ( XQueue OrderInfoLRecord ) false ) . 
 Notation " '_buys_' " := ( buys__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_buys_' " := ( buys__right ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.tip3root_' " := ( dealer_ι_tip3root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.tip3root_' " := ( dealer_ι_tip3root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.notify_addr_' " := ( dealer_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.notify_addr_' " := ( dealer_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.price_' " := ( dealer_ι_price_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.price_' " := ( dealer_ι_price_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.deals_limit_' " := ( dealer_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.deals_limit_' " := ( dealer_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.tons_cfg_' " := ( dealer_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.tons_cfg_' " := ( dealer_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.sells_amount_' " := ( dealer_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.sells_amount_' " := ( dealer_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.sells_' " := ( dealer_ι_sells_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.sells_' " := ( dealer_ι_sells_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.buys_amount_' " := ( dealer_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.buys_amount_' " := ( dealer_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.buys_' " := ( dealer_ι_buys_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.buys_' " := ( dealer_ι_buys_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.ret_' " := ( dealer_ι_ret_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.ret_' " := ( dealer_ι_ret_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.sells_amount' " := ( process_ret_ι_sells_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.sells_amount' " := ( process_ret_ι_sells_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.sells_' " := ( process_ret_ι_sells_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.sells_' " := ( process_ret_ι_sells_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.buys_amount' " := ( process_ret_ι_buys_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.buys_amount' " := ( process_ret_ι_buys_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.buys_' " := ( process_ret_ι_buys_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.buys_' " := ( process_ret_ι_buys_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.ret_' " := ( process_ret_ι_ret_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.ret_' " := ( process_ret_ι_ret_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_ownership_info.owner' " := ( lend_ownership_info_ι_owner ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_ownership_info.owner' " := ( lend_ownership_info_ι_owner ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_ownership_info.lend_balance' " := ( lend_ownership_info_ι_lend_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_ownership_info.lend_balance' " := ( lend_ownership_info_ι_lend_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_ownership_info.lend_finish_time' " := ( lend_ownership_info_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_ownership_info.lend_finish_time' " := ( lend_ownership_info_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.spender' " := ( allowance_info_ι_spender ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.spender' " := ( allowance_info_ι_spender ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.name_' " := ( TONTokenWallet_ι_name_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.name_' " := ( TONTokenWallet_ι_name_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.symbol_' " := ( TONTokenWallet_ι_symbol_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.symbol_' " := ( TONTokenWallet_ι_symbol_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.decimals_' " := ( TONTokenWallet_ι_decimals_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.decimals_' " := ( TONTokenWallet_ι_decimals_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.balance_' " := ( TONTokenWallet_ι_balance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.balance_' " := ( TONTokenWallet_ι_balance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.root_public_key_' " := ( TONTokenWallet_ι_root_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.root_public_key_' " := ( TONTokenWallet_ι_root_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.wallet_public_key_' " := ( TONTokenWallet_ι_wallet_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.wallet_public_key_' " := ( TONTokenWallet_ι_wallet_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.root_address_' " := ( TONTokenWallet_ι_root_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.root_address_' " := ( TONTokenWallet_ι_root_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.owner_address_' " := ( TONTokenWallet_ι_owner_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.owner_address_' " := ( TONTokenWallet_ι_owner_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.lend_ownership_' " := ( TONTokenWallet_ι_lend_ownership_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.lend_ownership_' " := ( TONTokenWallet_ι_lend_ownership_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.code_' " := ( TONTokenWallet_ι_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.code_' " := ( TONTokenWallet_ι_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.allowance_' " := ( TONTokenWallet_ι_allowance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.allowance_' " := ( TONTokenWallet_ι_allowance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.workchain_id_' " := ( TONTokenWallet_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TONTokenWallet.workchain_id_' " := ( TONTokenWallet_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.original_amount' " := ( OrderInfoXchg_ι_original_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.original_amount' " := ( OrderInfoXchg_ι_original_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.amount' " := ( OrderInfoXchg_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.amount' " := ( OrderInfoXchg_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.account' " := ( OrderInfoXchg_ι_account ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.account' " := ( OrderInfoXchg_ι_account ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( OrderInfoXchg_ι_tip3_wallet_provide ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( OrderInfoXchg_ι_tip3_wallet_provide ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( OrderInfoXchg_ι_tip3_wallet_receive ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( OrderInfoXchg_ι_tip3_wallet_receive ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.client_addr' " := ( OrderInfoXchg_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.client_addr' " := ( OrderInfoXchg_ι_client_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.order_finish_time' " := ( OrderInfoXchg_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.order_finish_time' " := ( OrderInfoXchg_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 

(**************************************************************************************************)

 Definition calc_cost_call { a1 a2 }  ( amount : URValue XInteger128 a1 ) ( price : URValue XInteger128 a2 ) : LedgerT ( ControlResult ( XMaybe XInteger128 ) false ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) calc_cost 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} ( amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} ( price ) ) 
 . 
 Notation " 'Ф_calc_cost_ref_' '(' amount price ')' " := 
 ( URResult ( Ф_calc_cost_call 
 amount price )) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom ULValue at level 0 ) : ursus_scope . 
 
 Definition dealer_Ф_make_deal_call { a1 a2 }  ( sell : URValue OrderInfoP a1 ) ( buy : URValue OrderInfoP a2 ) : LedgerT ( ControlResult ( XBool # XBool # XInteger128 )%sol false ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) dealer_Ф_make_deal 
 ( SimpleLedgerableArg URValue {{ Λ "sell" }} ( sell ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "buy" }} ( buy ) ) 
 . 
 Notation " 'dealer_Ф_make_deal_ref_' '(' sell buy ')' " := 
 ( URResult ( dealer_Ф_make_deal_call 
 sell buy )) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , buy custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Ф_is_active_time_call { a1 }  ( order_finish_time : URValue XInteger32 a1 ) : LedgerT ( ControlResult XBool false ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Ф_is_active_time 
 ( SimpleLedgerableArg URValue {{ Λ "order_finish_time" }} ( order_finish_time ) ) 
 . 
 Notation " 'Ф_is_active_time_ref_' '(' order_finish_time ')' " := 
 ( URResult ( Ф_is_active_time_call 
 order_finish_time )) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope . 
 
 Definition dealer_Ф_extract_active_order_call { a1 a2 a3 a4 }  ( cur_order : URValue ( XMaybe OrderInfoWithIdxP ) a1 ) ( orders : URValue ( XList OrderInfoP ) a2 ) ( all_amount : URValue XInteger128 a3 ) ( sell : URValue XBool a4 ) : LedgerT ( ControlResult ( XList OrderInfoP ) false ( orb ( orb ( orb a4 a3 ) a2 ) a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ4 ) dealer_Ф_extract_active_order 
 ( SimpleLedgerableArg URValue {{ Λ "cur_order" }} ( cur_order ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "orders" }} ( orders ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "all_amount" }} ( all_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "sell" }} ( sell ) ) 
 . 
 Notation " 'dealer_Ф_extract_active_order_ref_' '(' cur_order orders all_amount sell ')' " := 
 ( URResult ( dealer_Ф_extract_active_order_call 
 cur_order orders all_amount sell )) 
 (in custom URValue at level 0 , cur_order custom URValue at level 0 
 , orders custom ULValue at level 0 
 , all_amount custom ULValue at level 0 
 , sell custom ULValue at level 0 ) : ursus_scope . 
 
 Definition dealer_Ф_process_queue_call { a1 a2 }  ( sell_idx : URValue XInteger a1 ) ( buy_idx : URValue XInteger a2 ) : LedgerT ( ControlResult PhantomType ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) dealer_Ф_process_queue 
 ( SimpleLedgerableArg URValue {{ Λ "sell_idx" }} ( sell_idx ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "buy_idx" }} ( buy_idx ) ) 
 . 
 Notation " 'dealer_Ф_process_queue_ref_' '(' sell_idx buy_idx ')' " := 
 ( FuncallExpression ( dealer_Ф_process_queue_call 
 sell_idx buy_idx )) 
 (in custom ULValue at level 0 , sell_idx custom URValue at level 0 
 , buy_idx custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Ф_process_queue_impl_call { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 }  ( tip3root : URValue XAddress a1 ) ( notify_addr : URValue IFlexNotifyPtrP a2 ) ( price : URValue XInteger128 a3 ) ( deals_limit : URValue XInteger8 a4 ) ( tons_cfg : URValue TonsConfigP a5 ) ( sell_idx : URValue XInteger a6 ) ( buy_idx : URValue XInteger a7 ) ( sells_amount : URValue XInteger128 a8 ) ( sells : URValue ( XList OrderInfoP ) a9 ) ( buys_amount : URValue XInteger128 a10 ) ( buys : URValue ( XList OrderInfoP ) a11 ) : LedgerT ( ControlResult process_retP false ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a11 a10 ) a9 ) a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ11 ) Ф_process_queue_impl 
 ( SimpleLedgerableArg URValue {{ Λ "tip3root" }} ( tip3root ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "notify_addr" }} ( notify_addr ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} ( price ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tons_cfg" }} ( tons_cfg ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "sell_idx" }} ( sell_idx ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "buy_idx" }} ( buy_idx ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "sells_amount" }} ( sells_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "sells" }} ( sells ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "buys_amount" }} ( buys_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "buys" }} ( buys ) ) 
 . 
 Notation " 'Ф_process_queue_impl_ref_' '(' tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ')' " := 
 ( URResult ( Ф_process_queue_impl_call 
 tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys )) 
 (in custom URValue at level 0 , tip3root custom URValue at level 0 
 , notify_addr custom ULValue at level 0 
 , price custom ULValue at level 0 
 , deals_limit custom ULValue at level 0 
 , tons_cfg custom ULValue at level 0 
 , sell_idx custom ULValue at level 0 
 , buy_idx custom ULValue at level 0 
 , sells_amount custom ULValue at level 0 
 , sells custom ULValue at level 0 
 , buys_amount custom ULValue at level 0 
 , buys custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_processQueue_call  : LedgerT ( ControlResult PhantomType ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_processQueue 
 . 
 Notation " 'Price_Ф_processQueue_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_processQueue_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_onTip3LendOwnershipMinValue_call  : LedgerT ( ControlResult XInteger128 false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_onTip3LendOwnershipMinValue 
 . 
 Notation " 'Price_Ф_onTip3LendOwnershipMinValue_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_onTip3LendOwnershipMinValue_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_expected_wallet_address_call { a1 a2 }  ( wallet_pubkey : URValue XInteger256 a1 ) ( internal_owner : URValue XInteger256 a2 ) : LedgerT ( ControlResult XInteger256 false ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Price_Ф_expected_wallet_address 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_pubkey" }} ( wallet_pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} ( internal_owner ) ) 
 . 
 Notation " 'Price_Ф_expected_wallet_address_ref_' '(' wallet_pubkey internal_owner ')' " := 
 ( URResult ( Price_Ф_expected_wallet_address_call 
 wallet_pubkey internal_owner )) 
 (in custom URValue at level 0 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_verify_tip3_addr_call { a1 a2 a3 }  ( tip3_wallet : URValue XAddress a1 ) ( wallet_pubkey : URValue XInteger256 a2 ) ( internal_owner : URValue XInteger256 a3 ) : LedgerT ( ControlResult XBool false ( orb ( orb a3 a2 ) a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) Price_Ф_verify_tip3_addr 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_wallet" }} ( tip3_wallet ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_pubkey" }} ( wallet_pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} ( internal_owner ) ) 
 . 
 Notation " 'Price_Ф_verify_tip3_addr_ref_' '(' tip3_wallet wallet_pubkey internal_owner ')' " := 
 ( URResult ( Price_Ф_verify_tip3_addr_call 
 tip3_wallet wallet_pubkey internal_owner )) 
 (in custom URValue at level 0 , tip3_wallet custom URValue at level 0 
 , wallet_pubkey custom ULValue at level 0 
 , internal_owner custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_on_sell_fail_call { a1 a2 a3 }  ( ec : URValue XInteger a1 ) ( wallet_in : URValue ITONTokenWalletPtrP a2 ) ( amount : URValue XInteger128 a3 ) : LedgerT ( ControlResult OrderRetP false ( orb ( orb a3 a2 ) a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) Price_Ф_on_sell_fail 
 ( SimpleLedgerableArg URValue {{ Λ "ec" }} ( ec ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_in" }} ( wallet_in ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} ( amount ) ) 
 . 
 Notation " 'Price_Ф_on_sell_fail_ref_' '(' ec wallet_in amount ')' " := 
 ( URResult ( Price_Ф_on_sell_fail_call 
 ec wallet_in amount )) 
 (in custom URValue at level 0 , ec custom URValue at level 0 
 , wallet_in custom ULValue at level 0 
 , amount custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_onTip3LendOwnership_call { a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue XAddress a1 ) ( balance : URValue XInteger128 a2 ) ( lend_finish_time : URValue XInteger32 a3 ) ( pubkey : URValue XInteger256 a4 ) ( internal_owner : URValue XAddress a5 ) ( payload : URValue XCell a6 ) : LedgerT ( ControlResult OrderRetP false ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ6 ) Price_Ф_onTip3LendOwnership 
 ( SimpleLedgerableArg URValue {{ Λ "answer_addr" }} ( answer_addr ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "balance" }} ( balance ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "lend_finish_time" }} ( lend_finish_time ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "pubkey" }} ( pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} ( internal_owner ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "payload" }} ( payload ) ) 
 . 
 Notation " 'Price_Ф_onTip3LendOwnership_ref_' '(' answer_addr balance lend_finish_time pubkey internal_owner payload ')' " := 
 ( URResult ( Price_Ф_onTip3LendOwnership_call 
 answer_addr balance lend_finish_time pubkey internal_owner payload )) 
 (in custom URValue at level 0 , answer_addr custom URValue at level 0 
 , balance custom ULValue at level 0 
 , lend_finish_time custom ULValue at level 0 
 , pubkey custom ULValue at level 0 
 , internal_owner custom ULValue at level 0 
 , payload custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_buyTip3MinValue_call { a1 }  ( buy_cost : URValue XInteger128 a1 ) : LedgerT ( ControlResult XInteger128 false ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Price_Ф_buyTip3MinValue 
 ( SimpleLedgerableArg URValue {{ Λ "buy_cost" }} ( buy_cost ) ) 
 . 
 Notation " 'Price_Ф_buyTip3MinValue_ref_' '(' buy_cost ')' " := 
 ( URResult ( Price_Ф_buyTip3MinValue_call 
 buy_cost )) 
 (in custom URValue at level 0 , buy_cost custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_buyTip3_call { a1 a2 a3 }  ( amount : URValue XInteger128 a1 ) ( receive_tip3_wallet : URValue XAddress a2 ) ( order_finish_time : URValue XInteger32 a3 ) : LedgerT ( ControlResult OrderRetP false ( orb ( orb a3 a2 ) a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) Price_Ф_buyTip3 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} ( amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "receive_tip3_wallet" }} ( receive_tip3_wallet ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "order_finish_time" }} ( order_finish_time ) ) 
 . 
 Notation " 'Price_Ф_buyTip3_ref_' '(' amount receive_tip3_wallet order_finish_time ')' " := 
 ( URResult ( Price_Ф_buyTip3_call 
 amount receive_tip3_wallet order_finish_time )) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , receive_tip3_wallet custom ULValue at level 0 
 , order_finish_time custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Ф_cancel_order_impl_call { a1 a2 a3 a4 a5 a6 a7 }  ( orders : URValue ( XList OrderInfoP ) a1 ) ( client_addr : URValue addr_std_fixedP a2 ) ( all_amount : URValue XInteger128 a3 ) ( sell : URValue XBool a4 ) ( return_ownership : URValue GramsP a5 ) ( process_queue : URValue GramsP a6 ) ( incoming_val : URValue GramsP a7 ) : LedgerT ( ControlResult ( XList OrderInfoP ) false ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ7 ) Ф_cancel_order_impl 
 ( SimpleLedgerableArg URValue {{ Λ "orders" }} ( orders ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "client_addr" }} ( client_addr ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "all_amount" }} ( all_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "sell" }} ( sell ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "return_ownership" }} ( return_ownership ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "process_queue" }} ( process_queue ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "incoming_val" }} ( incoming_val ) ) 
 . 
 Notation " 'Ф_cancel_order_impl_ref_' '(' orders client_addr all_amount sell return_ownership process_queue incoming_val ')' " := 
 ( URResult ( Ф_cancel_order_impl_call 
 orders client_addr all_amount sell return_ownership process_queue incoming_val )) 
 (in custom URValue at level 0 , orders custom URValue at level 0 
 , client_addr custom ULValue at level 0 
 , all_amount custom ULValue at level 0 
 , sell custom ULValue at level 0 
 , return_ownership custom ULValue at level 0 
 , process_queue custom ULValue at level 0 
 , incoming_val custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_cancelSell_call  : LedgerT ( ControlResult PhantomType ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_cancelSell 
 . 
 Notation " 'Price_Ф_cancelSell_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_cancelSell_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_cancelBuy_call  : LedgerT ( ControlResult PhantomType ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_cancelBuy 
 . 
 Notation " 'Price_Ф_cancelBuy_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_cancelBuy_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getPrice_call  : LedgerT ( ControlResult XInteger128 false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getPrice 
 . 
 Notation " 'Price_Ф_getPrice_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getPrice_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getMinimumAmount_call  : LedgerT ( ControlResult XInteger128 false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getMinimumAmount 
 . 
 Notation " 'Price_Ф_getMinimumAmount_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getMinimumAmount_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getSellAmount_call  : LedgerT ( ControlResult XInteger128 false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getSellAmount 
 . 
 Notation " 'Price_Ф_getSellAmount_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getSellAmount_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getBuyAmount_call  : LedgerT ( ControlResult XInteger128 false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getBuyAmount 
 . 
 Notation " 'Price_Ф_getBuyAmount_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getBuyAmount_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getDetails_call  : LedgerT ( ControlResult DetailsInfoP false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getDetails 
 . 
 Notation " 'Price_Ф_getDetails_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getDetails_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getTonsCfg_call  : LedgerT ( ControlResult TonsConfigP false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getTonsCfg 
 . 
 Notation " 'Price_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getTonsCfg_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getSells_call  : LedgerT ( ControlResult ( XHMap XInteger ) false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getSells 
 . 
 Notation " 'Price_Ф_getSells_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getSells_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getBuys_call  : LedgerT ( ControlResult ( XHMap XInteger ) false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getBuys 
 . 
 Notation " 'Price_Ф_getBuys_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getBuys_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф__fallback_call { a1 }  ( cell : URValue (P a1 ) : LedgerT ( ControlResult XInteger false ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Price_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "cell" }} ( cell ) ) 
 . 
 Notation " 'Price_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( Price_Ф__fallback_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope . 
 
 Definition Ф_prepare_price_state_init_and_addr_call { a1 a2 }  ( price_data : URValue DPriceP a1 ) ( price_code : URValue XCell a2 ) : LedgerT ( ControlResult ( StateInitP # XInteger256 )%sol false ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_price_state_init_and_addr 
 ( SimpleLedgerableArg URValue {{ Λ "price_data" }} ( price_data ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} ( price_code ) ) 
 . 
 Notation " 'Ф_prepare_price_state_init_and_addr_ref_' '(' price_data price_code ')' " := 
 ( URResult ( Ф_prepare_price_state_init_and_addr_call 
 price_data price_code )) 
 (in custom URValue at level 0 , price_data custom URValue at level 0 
 , price_code custom ULValue at level 0 ) : ursus_scope . 

End Calls. 

End FuncNotations.
