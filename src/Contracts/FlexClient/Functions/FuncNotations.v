Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import Project.CommonConstSig.

Require Import Contracts.FlexClient.Ledger.
Require Import Contracts.FlexClient.Functions.FuncSig.

Module FuncNotations (xt: XTypesSig) 
                          (sm: StateMonadSig) 
                          (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

Module Export SpecModuleForFuncNotations :=  Spec xt sm.

Import UrsusNotations.

Local Open Scope ursus_scope.

Notation " 'TickTock.tick' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TickTock_ι_tick ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TickTock.tick' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TickTock_ι_tick ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TickTock.tock' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TickTock_ι_tock ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TickTock.tock' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TickTock_ι_tock ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.split_depth' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_split_depth ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.split_depth' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_split_depth ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.special' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_special ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.special' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_special ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.data' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_data ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.data' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_data ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.library' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_library ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.library' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) StateInit_ι_library ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'anycast_info.rewrite_pfx' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) anycast_info_ι_rewrite_pfx ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'anycast_info.rewrite_pfx' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) anycast_info_ι_rewrite_pfx ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.kind' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_ι_kind ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.kind' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_ι_kind ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.Anycast' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_ι_Anycast ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.Anycast' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_ι_Anycast ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.workchain_id' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.workchain_id' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.address' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_ι_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.address' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_ι_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.workchain_id' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_fixed_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.workchain_id' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_fixed_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.address' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_fixed_ι_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.address' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) addr_std_fixed_ι_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'SellArgs.amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'SellArgs.amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'SellArgs.receive_wallet' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SellArgs_ι_receive_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'SellArgs.receive_wallet' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SellArgs_ι_receive_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.tons_value' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBurnWalletArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.tons_value' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBurnWalletArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_pubkey' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBurnWalletArgs_ι_out_pubkey ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_pubkey' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBurnWalletArgs_ι_out_pubkey ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_internal_owner' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBurnWalletArgs_ι_out_internal_owner ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_internal_owner' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBurnWalletArgs_ι_out_internal_owner ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.my_tip3_addr' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBurnWalletArgs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.my_tip3_addr' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBurnWalletArgs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.transfer_tip3' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_transfer_tip3 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.transfer_tip3' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_transfer_tip3 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.return_ownership' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_return_ownership ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.return_ownership' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_return_ownership ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.trading_pair_deploy' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_trading_pair_deploy ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.trading_pair_deploy' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_trading_pair_deploy ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.order_answer' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_order_answer ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.order_answer' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_order_answer ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.process_queue' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_process_queue ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.process_queue' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_process_queue ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.send_notify' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_send_notify ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.send_notify' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TonsConfig_ι_send_notify ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.owner_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_owner_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.owner_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_owner_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.trading_pair_code_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_trading_pair_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.trading_pair_code_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_trading_pair_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.xchg_pair_code_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_xchg_pair_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.xchg_pair_code_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_xchg_pair_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.workchain_id_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.workchain_id_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.tons_cfg_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.tons_cfg_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.notify_addr_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.notify_addr_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.ext_wallet_code_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_ext_wallet_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.ext_wallet_code_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_ext_wallet_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wallet_code_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_flex_wallet_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wallet_code_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_flex_wallet_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wrapper_code_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_flex_wrapper_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wrapper_code_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexClient_ι_flex_wrapper_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgsAddrs.my_tip3_addr' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgsAddrs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgsAddrs.my_tip3_addr' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgsAddrs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.lend_finish_time' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.lend_finish_time' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.min_amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.min_amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.deals_limit' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.deals_limit' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tons_value' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tons_value' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.addrs' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_addrs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.addrs' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_addrs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3cfg' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3cfg' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexSellArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.order_finish_time' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.order_finish_time' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.min_amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.min_amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deals_limit' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deals_limit' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deploy_value' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_deploy_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deploy_value' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_deploy_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.my_tip3_addr' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.my_tip3_addr' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3cfg' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3cfg' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexBuyArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.major_tip3cfg' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCfgs_ι_major_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.major_tip3cfg' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCfgs_ι_major_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.minor_tip3cfg' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCfgs_ι_minor_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.minor_tip3cfg' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCfgs_ι_minor_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.sell' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.sell' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_num' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_price_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_num' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_price_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_denum' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_price_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_denum' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_price_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_lend_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_lend_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_finish_time' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_finish_time' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.min_amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.min_amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.deals_limit' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.deals_limit' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tons_value' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tons_value' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.xchg_price_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.xchg_price_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_xchg_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.addrs' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_addrs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.addrs' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_addrs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3cfgs' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_tip3cfgs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3cfgs' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgArgs_ι_tip3cfgs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.min_amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.min_amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.deals_limit' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.deals_limit' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.value' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.value' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3cfg' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3cfg' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexCancelArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.sell' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.sell' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_num' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_price_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_num' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_price_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_denum' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_price_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_denum' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_price_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.min_amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.min_amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.deals_limit' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.deals_limit' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.value' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.value' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.xchg_price_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.xchg_price_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_xchg_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3_code' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3_code' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3cfgs' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_tip3cfgs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3cfgs' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) FlexXchgCancelArgs_ι_tip3cfgs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.flex_addr_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) XchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.flex_addr_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) XchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_major_root_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) XchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_major_root_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) XchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_minor_root_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) XchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_minor_root_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) XchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.deploy_value_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) XchgPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.deploy_value_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) XchgPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.original_amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_original_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.original_amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_original_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.account' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_account ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.account' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_account ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.tip3_wallet' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.tip3_wallet' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_tip3_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.client_addr' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.client_addr' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_client_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.order_finish_time' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.order_finish_time' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) OrderInfo_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.name' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract)  Tip3Config_ι_name ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.name' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) Tip3Config_ι_name ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.symbol' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) Tip3Config_ι_symbol ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.symbol' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) Tip3Config_ι_symbol ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.decimals' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) Tip3Config_ι_decimals ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.decimals' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) Tip3Config_ι_decimals ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_public_key' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) Tip3Config_ι_root_public_key ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_public_key' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) Tip3Config_ι_root_public_key ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_address' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) Tip3Config_ι_root_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_address' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) Tip3Config_ι_root_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.price_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_price_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.price_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_price_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.buys_amount_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.buys_amount_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.flex_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.flex_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.min_amount_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.min_amount_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.deals_limit_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.deals_limit_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.notify_addr_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.notify_addr_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.workchain_id_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.workchain_id_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tons_cfg_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tons_cfg_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tip3_code_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tip3_code_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tip3cfg_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tip3cfg_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.buys_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.buys_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPrice_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.num' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) RationalPrice_ι_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.num' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) RationalPrice_ι_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.denum' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) RationalPrice_ι_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.denum' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) RationalPrice_ι_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.price_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_price_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.price_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_price_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.sells_amount_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.sells_amount_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.buys_amount_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.buys_amount_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.flex_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.flex_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.min_amount_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.min_amount_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.deals_limit_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.deals_limit_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.notify_addr_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.notify_addr_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.workchain_id_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.workchain_id_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.tons_cfg_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.tons_cfg_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.tip3_code_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.tip3_code_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.major_tip3cfg_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_major_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.major_tip3cfg_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_major_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.minor_tip3cfg_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_minor_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DPriceXchg.minor_tip3cfg_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) DPriceXchg_ι_minor_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TradingPair.flex_addr_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TradingPair.flex_addr_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TradingPair.tip3_root_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TradingPair.tip3_root_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TradingPair.deploy_value_' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TradingPair.deploy_value_' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) TradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.sell' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) PayloadArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.sell' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) PayloadArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.amount' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) PayloadArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.amount' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) PayloadArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) PayloadArgs_ι_receive_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) PayloadArgs_ι_receive_tip3_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.client_addr' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) PayloadArgs_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.client_addr' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) PayloadArgs_ι_client_addr ) (in custom URValue at level 0) : ursus_scope.

Notation " 'error_code::zero_owner_pubkey' " := (sInject error_code_ι_zero_owner_pubkey) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wallet_code' " := (sInject error_code_ι_missed_flex_wallet_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wrapper_code' " := (sInject error_code_ι_missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 
(*TODO*)
Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 


Module Calls (tc : FlexClientSpecSig).

Export tc.

Local Open Scope string_scope.

 Definition FlexClient_Ф_constructor_call { a1 a2 a3 }  ( pubkey : URValue XInteger256 a1 ) ( trading_pair_code : URValue XCell a2 ) ( xchg_pair_code : URValue XCell a3 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FlexClient_Ф_constructor 
 ( SimpleLedgerableArg URValue {{ Λ "pubkey" }} ( pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "trading_pair_code" }} ( trading_pair_code ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "xchg_pair_code" }} ( xchg_pair_code ) ) 
 . 
 Notation " 'FlexClient_Ф_constructor_ref_' '(' pubkey trading_pair_code xchg_pair_code ')' " := 
 ( FuncallExpression ( FlexClient_Ф_constructor_call 
 pubkey trading_pair_code xchg_pair_code ) )
 ( in custom URValue at level 0 , pubkey custom URValue at level 0 
 , trading_pair_code custom URValue at level 0 
 , xchg_pair_code custom URValue at level 0 ) : ursus_scope . 

 Definition FlexClient_Ф_setFlexCfg_call { a1 a2 a3 }  
( tons_cfg : URValue TonsConfigStateLRecord a1 ) 
( flex : URValue addr_std_compact a2 ) 
( notify_addr : URValue addr_std_compact a3 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FlexClient_Ф_setFlexCfg 
 ( SimpleLedgerableArg URValue {{ Λ "tons_cfg" }} ( tons_cfg ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "flex" }} ( flex ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "notify_addr" }} ( notify_addr ) ) 
 . 
 Notation " 'FlexClient_Ф_setFlexCfg_ref_' '(' tons_cfg flex notify_addr ')' " := 
 ( FuncallExpression ( FlexClient_Ф_setFlexCfg_call 
 tons_cfg flex notify_addr ) )
 (in custom ULValue at level 0 , tons_cfg custom URValue at level 0 
 , flex custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_setExtWalletCode_call { a1 }  ( ext_wallet_code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FlexClient_Ф_setExtWalletCode 
 ( SimpleLedgerableArg URValue {{ Λ "ext_wallet_code" }} ( ext_wallet_code ) ) 
 . 
 Notation " 'FlexClient_Ф_setExtWalletCode_ref_' '(' ext_wallet_code ')' " := 
 ( FuncallExpression ( FlexClient_Ф_setExtWalletCode_call 
 ext_wallet_code ) )
 (in custom ULValue at level 0 , ext_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_setFlexWalletCode_call { a1 }  ( flex_wallet_code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FlexClient_Ф_setFlexWalletCode 
 ( SimpleLedgerableArg URValue {{ Λ "flex_wallet_code" }} ( flex_wallet_code ) ) 
 . 
 Notation " 'FlexClient_Ф_setFlexWalletCode_ref_' '(' flex_wallet_code ')' " := 
 ( FuncallExpression ( FlexClient_Ф_setFlexWalletCode_call 
 flex_wallet_code ) )
 (in custom ULValue at level 0 , flex_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_setFlexWrapperCode_call { a1 }  ( flex_wrapper_code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FlexClient_Ф_setFlexWrapperCode 
 ( SimpleLedgerableArg URValue {{ Λ "flex_wrapper_code" }} ( flex_wrapper_code ) ) 
 . 
 Notation " 'FlexClient_Ф_setFlexWrapperCode_ref_' '(' flex_wrapper_code ')' " := 
 ( FuncallExpression ( FlexClient_Ф_setFlexWrapperCode_call 
 flex_wrapper_code ) )
 (in custom ULValue at level 0 , flex_wrapper_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_deployTradingPair_call { a1 a2 a3 a4 }  ( tip3_root : URValue addr_std_compact a1 ) ( deploy_min_value : URValue XInteger128 a2 ) ( deploy_value : URValue XInteger128 a3 ) ( min_trade_amount : URValue XInteger128 a4 ) : LedgerT ( ControlResult XAddress true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ4 ) FlexClient_Ф_deployTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_root" }} ( tip3_root ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deploy_min_value" }} ( deploy_min_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deploy_value" }} ( deploy_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_trade_amount" }} ( min_trade_amount ) ) 
 . 
 Notation " 'FlexClient_Ф_deployTradingPair_ref_' '(' tip3_root deploy_min_value deploy_value min_trade_amount ')' " := 
 ( URResult ( FlexClient_Ф_deployTradingPair_call 
 tip3_root deploy_min_value deploy_value min_trade_amount ) )
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_deployXchgPair_call { a1 a2 a3 a4 a5 }  ( tip3_major_root : URValue addr_std_compact a1 ) ( tip3_minor_root : URValue addr_std_compact a2 ) ( deploy_min_value : URValue XInteger128 a3 ) ( deploy_value : URValue XInteger128 a4 ) ( min_trade_amount : URValue XInteger128 a5 ) : LedgerT ( ControlResult XAddress true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ5 ) FlexClient_Ф_deployXchgPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_major_root" }} ( tip3_major_root ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_minor_root" }} ( tip3_minor_root ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deploy_min_value" }} ( deploy_min_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deploy_value" }} ( deploy_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_trade_amount" }} ( min_trade_amount ) ) 
 . 
 Notation " 'FlexClient_Ф_deployXchgPair_ref_' '(' tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount ')' " := 
 ( URResult ( FlexClient_Ф_deployXchgPair_call 
 tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount ) )
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_preparePrice_call { a1 a2 a3 a4 a5 a6 }  
( price : URValue XInteger128 a1 ) 
( min_amount : URValue XInteger128 a2 ) 
( deals_limit : URValue XInteger8 a3 ) 
( tip3_code : URValue XCell a4 ) 
( tip3cfg : URValue Tip3ConfigStateLRecord a5 ) 
( price_code : URValue XCell a6 ) 
: LedgerT ( ControlResult ( StateInitStateLRecord # XAddress # XInteger256 )%sol 
(orb (orb (orb (orb (orb a6 a5) a4) a3) a2) a1) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ6 ) FlexClient_Ф_preparePrice 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} ( price ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} ( min_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_code" }} ( tip3_code ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3cfg" }} ( tip3cfg ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} ( price_code ) ) 
 . 
 Notation " 'FlexClient_Ф_preparePrice_ref_' '(' price min_amount deals_limit tip3_code tip3cfg price_code ')' " := 
 ( URResult ( FlexClient_Ф_preparePrice_call 
 price min_amount deals_limit tip3_code tip3cfg price_code ) )
 (in custom URValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tip3_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , price_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_deployPriceWithSell_call { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  
( price : URValue XInteger128 a1 ) ( amount : URValue XInteger128 a2 ) 
( lend_finish_time : URValue XInteger32 a3 ) ( min_amount : URValue XInteger128 a4 ) 
( deals_limit : URValue XInteger8 a5 ) ( tons_value : URValue XInteger128 a6 )
 ( price_code : URValue XCell a7 ) ( my_tip3_addr : URValue addr_std_compact a8 ) 
( receive_wallet : URValue addr_std_compact a9 ) ( tip3cfg : URValue Tip3ConfigStateLRecord a10 ) : LedgerT ( ControlResult XAddress true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ10 ) FlexClient_Ф_deployPriceWithSell 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} ( price ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} ( amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "lend_finish_time" }} ( lend_finish_time ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} ( min_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tons_value" }} ( tons_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} ( price_code ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "my_tip3_addr" }} ( my_tip3_addr ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "receive_wallet" }} ( receive_wallet ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3cfg" }} ( tip3cfg ) ) 
 . 
 Notation " 'FlexClient_Ф_deployPriceWithSell_ref_' '(' price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg ')' " := 
 ( URResult ( FlexClient_Ф_deployPriceWithSell_call 
 price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg ) )
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , receive_wallet custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_deployPriceWithBuy_call { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  
( price : URValue XInteger128 a1 ) ( amount : URValue XInteger128 a2 ) 
( order_finish_time : URValue XInteger32 a3 ) ( min_amount : URValue XInteger128 a4 ) 
( deals_limit : URValue XInteger8 a5 ) ( deploy_value : URValue XInteger128 a6 ) 
( price_code : URValue XCell a7 ) ( my_tip3_addr : URValue addr_std_compact a8 ) 
( tip3cfg : URValue Tip3ConfigStateLRecord a9 ) : LedgerT ( ControlResult XAddress true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ9 ) FlexClient_Ф_deployPriceWithBuy 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} ( price ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} ( amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "order_finish_time" }} ( order_finish_time ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} ( min_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deploy_value" }} ( deploy_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} ( price_code ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "my_tip3_addr" }} ( my_tip3_addr ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3cfg" }} ( tip3cfg ) ) 
 . 
 Notation " 'FlexClient_Ф_deployPriceWithBuy_ref_' '(' price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg ')' " := 
 ( URResult ( FlexClient_Ф_deployPriceWithBuy_call 
 price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg ) )
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 
 , order_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_cancelSellOrder_call { a1 a2 a3 a4 a5 a6 }  
( price : URValue XInteger128 a1 ) ( min_amount : URValue XInteger128 a2 ) 
( deals_limit : URValue XInteger8 a3 ) ( value : URValue XInteger128 a4 )
 ( price_code : URValue XCell a5 ) ( tip3cfg : URValue Tip3ConfigStateLRecord a6 ) 
: LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ6 ) FlexClient_Ф_cancelSellOrder 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} ( price ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} ( min_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "value" }} ( value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} ( price_code ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3cfg" }} ( tip3cfg ) ) 
 . 
 Notation " 'FlexClient_Ф_cancelSellOrder_ref_' '(' price min_amount deals_limit value price_code tip3cfg ')' " := 
 ( FuncallExpression ( FlexClient_Ф_cancelSellOrder_call 
 price min_amount deals_limit value price_code tip3cfg ) )
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_cancelBuyOrder_call { a1 a2 a3 a4 a5 a6 }  ( price : URValue XInteger128 a1 ) 
( min_amount : URValue XInteger128 a2 ) ( deals_limit : URValue XInteger8 a3 ) 
( value : URValue XInteger128 a4 ) ( price_code : URValue XCell a5 ) 
( tip3cfg : URValue Tip3ConfigStateLRecord a6 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ6 ) FlexClient_Ф_cancelBuyOrder 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} ( price ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} ( min_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "value" }} ( value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} ( price_code ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3cfg" }} ( tip3cfg ) ) 
 . 
 Notation " 'FlexClient_Ф_cancelBuyOrder_ref_' '(' price min_amount deals_limit value price_code tip3cfg ')' " := 
 ( FuncallExpression ( FlexClient_Ф_cancelBuyOrder_call 
 price min_amount deals_limit value price_code tip3cfg ) )
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_preparePriceXchg_call { a1 a2 a3 a4 a5 a6 a7 }  
  ( price_num : URValue XInteger128 a1 )
  ( price_denum : URValue XInteger128 a2 ) 
  ( min_amount : URValue XInteger128 a3 )
  ( deals_limit : URValue XInteger8 a4 )
  ( major_tip3cfg : URValue Tip3ConfigStateLRecord a5 ) 
  ( minor_tip3cfg : URValue Tip3ConfigStateLRecord a6 ) 
  ( price_code : URValue XCell a7 ) 
: LedgerT ( ControlResult ( StateInitStateLRecord # XAddress # XInteger256 )%sol 
(orb (orb (orb (orb (orb (orb a7 a6) a5) a4) a3) a2) a1) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ7 ) FlexClient_Ф_preparePriceXchg 
 ( SimpleLedgerableArg URValue {{ Λ "price_num" }} ( price_num ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_denum" }} ( price_denum ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} ( min_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "major_tip3cfg" }} ( major_tip3cfg ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "minor_tip3cfg" }} ( minor_tip3cfg ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} ( price_code ) ) 
 . 
 Notation " 'FlexClient_Ф_preparePriceXchg_ref_' '(' price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code ')' " := 
 ( URResult ( FlexClient_Ф_preparePriceXchg_call 
 price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code ) )
 (in custom URValue at level 0 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 
 , price_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_cancelXchgOrder_call { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( sell : URValue XBool a1 ) 
( price_num : URValue XInteger128 a2 ) ( price_denum : URValue XInteger128 a3 ) 
( min_amount : URValue XInteger128 a4 ) ( deals_limit : URValue XInteger8 a5 ) 
( value : URValue XInteger128 a6 ) ( xchg_price_code : URValue XCell a7 ) 
( major_tip3cfg : URValue Tip3ConfigStateLRecord a8 ) ( minor_tip3cfg : URValue Tip3ConfigStateLRecord a9 ) 
: LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ9 ) FlexClient_Ф_cancelXchgOrder 
 ( SimpleLedgerableArg URValue {{ Λ "sell" }} ( sell ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_num" }} ( price_num ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_denum" }} ( price_denum ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} ( min_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "value" }} ( value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "xchg_price_code" }} ( xchg_price_code ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "major_tip3cfg" }} ( major_tip3cfg ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "minor_tip3cfg" }} ( minor_tip3cfg ) ) 
 . 
 Notation " 'FlexClient_Ф_cancelXchgOrder_ref_' '(' sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg ')' " := 
 ( FuncallExpression ( FlexClient_Ф_cancelXchgOrder_call 
 sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg ) )
 (in custom ULValue at level 0 , sell custom URValue at level 0 
 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , xchg_price_code custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_transfer_call { a1 a2 a3 }  ( dest : URValue addr_std_compact a1 ) 
( value : URValue XInteger128 a2 ) ( bounce : URValue XBool a3 ) 
: LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FlexClient_Ф_transfer 
 ( SimpleLedgerableArg URValue {{ Λ "dest" }} ( dest ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "value" }} ( value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "bounce" }} ( bounce ) ) 
 . 
 Notation " 'FlexClient_Ф_transfer_ref_' '(' dest value bounce ')' " := 
 ( FuncallExpression ( FlexClient_Ф_transfer_call 
 dest value bounce ) )
 (in custom ULValue at level 0 , dest custom URValue at level 0 
 , value custom URValue at level 0 
 , bounce custom URValue at level 0 ) : ursus_scope . 
 
 (* Definition FlexClient_Ф_deployDPriceXchg_call { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 } 
 ( sell : URValue XBool a1 ) ( price_num : URValue XInteger128 a2 ) 
( price_denum : URValue XInteger128 a3 ) ( amount : URValue XInteger128 a4 )
 ( lend_amount : URValue XInteger128 a5 ) ( lend_finish_time : URValue XInteger32 a6 )
 ( min_amount : URValue XInteger128 a7 ) ( deals_limit : URValue XInteger8 a8 ) 
( tons_value : URValue XInteger128 a9 ) ( xchg_price_code : URValue XCell a10 ) 
( my_tip3_addr : URValue addr_std_compact a11 ) ( receive_wallet : URValue addr_std_compact a12 ) 
( major_tip3cfg : URValue Tip3ConfigStateLRecord a13 ) ( minor_tip3cfg : URValue Tip3ConfigStateLRecord a14 ) 
: LedgerT ( ControlResult XAddress  
( orb a14 ( orb a13 ( orb a12 ( orb a11 ( orb a10 ( orb a9 ( orb a8 ( orb a7 ( orb a6 ( orb a5 ( orb a4 ( orb a3 ( orb a2 a1 ) ) ) ) ) ) ) ) ) ) ) ) ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ14 ) FlexClient_Ф_deployDPriceXchg 
 ( SimpleLedgerableArg URValue {{ Λ "sell" }} ( sell ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_num" }} ( price_num ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_denum" }} ( price_denum ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} ( amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "lend_amount" }} ( lend_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "lend_finish_time" }} ( lend_finish_time ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} ( min_amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tons_value" }} ( tons_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "xchg_price_code" }} ( xchg_price_code ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "my_tip3_addr" }} ( my_tip3_addr ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "receive_wallet" }} ( receive_wallet ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "major_tip3cfg" }} ( major_tip3cfg ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "minor_tip3cfg" }} ( minor_tip3cfg ) ) 
 . 
 Notation " 'FlexClient_Ф_deployDPriceXchg_ref_' '(' sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg ')' " := 
 ( URResult ( FlexClient_Ф_deployDPriceXchg_call 
 sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg ) )
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , amount custom URValue at level 0 
 , lend_amount custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_value custom URValue at level 0 
 , xchg_price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , receive_wallet custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 ) : ursus_scope . 
  *)
 Definition FlexClient_Ф_deployWrapperWithWallet_call { a1 a2 a3 a4 a5 a6 } 
 ( wrapper_pubkey : URValue XInteger256 a1 ) ( wrapper_deploy_value : URValue XInteger128 a2 )
 ( wrapper_keep_balance : URValue XInteger128 a3 ) ( ext_wallet_balance : URValue XInteger128 a4 ) 
( set_internal_wallet_value : URValue XInteger128 a5 ) ( tip3cfg : URValue Tip3ConfigStateLRecord a6 ) 
: LedgerT ( ControlResult XAddress true  ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ6 ) FlexClient_Ф_deployWrapperWithWallet 
 ( SimpleLedgerableArg URValue {{ Λ "wrapper_pubkey" }} ( wrapper_pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "wrapper_deploy_value" }} ( wrapper_deploy_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "wrapper_keep_balance" }} ( wrapper_keep_balance ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "ext_wallet_balance" }} ( ext_wallet_balance ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "set_internal_wallet_value" }} ( set_internal_wallet_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3cfg" }} ( tip3cfg ) ) 
 . 
 Notation " 'FlexClient_Ф_deployWrapperWithWallet_ref_' '(' wrapper_pubkey wrapper_deploy_value wrapper_keep_balance ext_wallet_balance set_internal_wallet_value tip3cfg ')' " := 
 ( URResult ( FlexClient_Ф_deployWrapperWithWallet_call 
 wrapper_pubkey wrapper_deploy_value wrapper_keep_balance ext_wallet_balance set_internal_wallet_value tip3cfg ) )
 (in custom URValue at level 0 , wrapper_pubkey custom URValue at level 0 
 , wrapper_deploy_value custom URValue at level 0 
 , wrapper_keep_balance custom URValue at level 0 
 , ext_wallet_balance custom URValue at level 0 
 , set_internal_wallet_value custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_deployEmptyFlexWallet_call { a1 a2 a3 }  ( pubkey : URValue XInteger256 a1 ) 
( tons_to_wallet : URValue XInteger128 a2 ) ( tip3cfg : URValue Tip3ConfigStateLRecord a3 ) 
: LedgerT ( ControlResult XAddress true  ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FlexClient_Ф_deployEmptyFlexWallet 
 ( SimpleLedgerableArg URValue {{ Λ "pubkey" }} ( pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tons_to_wallet" }} ( tons_to_wallet ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3cfg" }} ( tip3cfg ) ) 
 . 
 Notation " 'FlexClient_Ф_deployEmptyFlexWallet_ref_' '(' pubkey tons_to_wallet tip3cfg ')' " := 
 ( URResult ( FlexClient_Ф_deployEmptyFlexWallet_call 
 pubkey tons_to_wallet tip3cfg ) )
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , tons_to_wallet custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_burnWallet_call { a1 a2 a3 a4 }  ( tons_value : URValue XInteger128 a1 ) 
( out_pubkey : URValue XInteger256 a2 ) ( out_internal_owner : URValue addr_std_compact a3 ) 
( my_tip3_addr : URValue addr_std_compact a4 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ4 ) FlexClient_Ф_burnWallet 
 ( SimpleLedgerableArg URValue {{ Λ "tons_value" }} ( tons_value ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "out_pubkey" }} ( out_pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "out_internal_owner" }} ( out_internal_owner ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "my_tip3_addr" }} ( my_tip3_addr ) ) 
 . 
 Notation " 'FlexClient_Ф_burnWallet_ref_' '(' tons_value out_pubkey out_internal_owner my_tip3_addr ')' " := 
 ( FuncallExpression ( FlexClient_Ф_burnWallet_call 
 tons_value out_pubkey out_internal_owner my_tip3_addr ) )
 (in custom ULValue at level 0 , tons_value custom URValue at level 0 
 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_getOwner_call  : LedgerT ( ControlResult XInteger256 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_getOwner 
 . 
 Notation " 'FlexClient_Ф_getOwner_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_getOwner_call 
 ) )
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_getFlex_call  : LedgerT ( ControlResult XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_getFlex 
 . 
 Notation " 'FlexClient_Ф_getFlex_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_getFlex_call 
 ) )
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_hasExtWalletCode_call  : LedgerT ( ControlResult XBool false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_hasExtWalletCode 
 . 
 Notation " 'FlexClient_Ф_hasExtWalletCode_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_hasExtWalletCode_call 
 ) )
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_hasFlexWalletCode_call  : LedgerT ( ControlResult XBool false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_hasFlexWalletCode 
 . 
 Notation " 'FlexClient_Ф_hasFlexWalletCode_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_hasFlexWalletCode_call 
 ) )
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_hasFlexWrapperCode_call  : LedgerT ( ControlResult XBool false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_hasFlexWrapperCode 
 . 
 Notation " 'FlexClient_Ф_hasFlexWrapperCode_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_hasFlexWrapperCode_call 
 ) )
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_getPayloadForDeployInternalWallet_call { a1 a2 a3 } 
 ( owner_pubkey : URValue XInteger256 a1 ) ( owner_addr : URValue addr_std_compact a2 )
 ( tons : URValue XInteger128 a3 ) : LedgerT ( ControlResult XCell (orb (orb a3 a2) a1) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FlexClient_Ф_getPayloadForDeployInternalWallet 
 ( SimpleLedgerableArg URValue {{ Λ "owner_pubkey" }} ( owner_pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "owner_addr" }} ( owner_addr ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tons" }} ( tons ) ) 
 . 
 Notation " 'FlexClient_Ф_getPayloadForDeployInternalWallet_ref_' '(' owner_pubkey owner_addr tons ')' " := 
 ( URResult ( FlexClient_Ф_getPayloadForDeployInternalWallet_call 
 owner_pubkey owner_addr tons ) )
 (in custom URValue at level 0 , owner_pubkey custom URValue at level 0 
 , owner_addr custom URValue at level 0 
 , tons custom URValue at level 0 ) : ursus_scope . 

 Definition FlexClient_Ф__fallback_call { a1 }  ( x : URValue XCell a1 ) : LedgerT ( ControlResult XInteger a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FlexClient_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "x" }} ( x ) ) 
 . 
 Notation " 'FlexClient_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( FlexClient_Ф__fallback_call 
 cell ) )
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope . 



End Calls. 

End FuncNotations.
