
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
About ULState.

Check ULState (f:=_Contract) (H:=ContractLEmbeddedType deployer_pubkey_).

(* Notation " 'Flex.deployer_pubkey_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  deployer_pubkey_) ) (in custom ULValue at level 0) : ursus_scope.  *)
 (*дал так же*)
 
Notation " 'TickTock.tick' " := ( ULState  TickTock_ι_tick ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TickTock.tick' " := ( URState  TickTock_ι_tick ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TickTock.tock' " := ( ULState  TickTock_ι_tock ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TickTock.tock' " := ( URState  TickTock_ι_tock ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.split_depth' " := ( ULState  StateInit_ι_split_depth ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.split_depth' " := ( URState  StateInit_ι_split_depth ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.special' " := ( ULState  StateInit_ι_special ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.special' " := ( URState  StateInit_ι_special ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.code' " := ( ULState  StateInit_ι_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.code' " := ( URState  StateInit_ι_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.data' " := ( ULState  StateInit_ι_data ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.data' " := ( URState  StateInit_ι_data ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.library' " := ( ULState  StateInit_ι_library ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.library' " := ( URState  StateInit_ι_library ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'anycast_info.rewrite_pfx' " := ( ULState  anycast_info_ι_rewrite_pfx ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'anycast_info.rewrite_pfx' " := ( URState  anycast_info_ι_rewrite_pfx ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.kind' " := ( ULState  addr_std_ι_kind ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.kind' " := ( URState  addr_std_ι_kind ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.Anycast' " := ( ULState  addr_std_ι_Anycast ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.Anycast' " := ( URState  addr_std_ι_Anycast ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.workchain_id' " := ( ULState  addr_std_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.workchain_id' " := ( URState  addr_std_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.address' " := ( ULState  addr_std_ι_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.address' " := ( URState  addr_std_ι_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.workchain_id' " := ( ULState  addr_std_fixed_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.workchain_id' " := ( URState  addr_std_fixed_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.address' " := ( ULState  addr_std_fixed_ι_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.address' " := ( URState  addr_std_fixed_ι_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'SellArgs.amount' " := ( ULState  SellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'SellArgs.amount' " := ( URState  SellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'SellArgs.receive_wallet' " := ( ULState  SellArgs_ι_receive_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'SellArgs.receive_wallet' " := ( URState  SellArgs_ι_receive_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.tons_value' " := ( ULState  FlexBurnWalletArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.tons_value' " := ( URState  FlexBurnWalletArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_pubkey' " := ( ULState  FlexBurnWalletArgs_ι_out_pubkey ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_pubkey' " := ( URState  FlexBurnWalletArgs_ι_out_pubkey ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_internal_owner' " := ( ULState  FlexBurnWalletArgs_ι_out_internal_owner ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_internal_owner' " := ( URState  FlexBurnWalletArgs_ι_out_internal_owner ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.my_tip3_addr' " := ( ULState  FlexBurnWalletArgs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.my_tip3_addr' " := ( URState  FlexBurnWalletArgs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.transfer_tip3' " := ( ULState  TonsConfig_ι_transfer_tip3 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.transfer_tip3' " := ( URState  TonsConfig_ι_transfer_tip3 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.return_ownership' " := ( ULState  TonsConfig_ι_return_ownership ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.return_ownership' " := ( URState  TonsConfig_ι_return_ownership ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.trading_pair_deploy' " := ( ULState  TonsConfig_ι_trading_pair_deploy ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.trading_pair_deploy' " := ( URState  TonsConfig_ι_trading_pair_deploy ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.order_answer' " := ( ULState  TonsConfig_ι_order_answer ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.order_answer' " := ( URState  TonsConfig_ι_order_answer ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.process_queue' " := ( ULState  TonsConfig_ι_process_queue ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.process_queue' " := ( URState  TonsConfig_ι_process_queue ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.send_notify' " := ( ULState  TonsConfig_ι_send_notify ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.send_notify' " := ( URState  TonsConfig_ι_send_notify ) (in custom URValue at level 0) : ursus_scope.

 Notation " 'FlexClient.owner_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  owner_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.owner_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  owner_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.trading_pair_code_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  trading_pair_code_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.trading_pair_code_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  trading_pair_code_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.xchg_pair_code_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  xchg_pair_code_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.xchg_pair_code_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  xchg_pair_code_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.workchain_id_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  workchain_id_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.workchain_id_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  workchain_id_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.tons_cfg_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  tons_cfg_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.tons_cfg_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  tons_cfg_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  flex_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  flex_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.notify_addr_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  notify_addr_) ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.notify_addr_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  notify_addr_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.ext_wallet_code_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  ext_wallet_code_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.ext_wallet_code_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  ext_wallet_code_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wallet_code_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  flex_wallet_code_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wallet_code_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  flex_wallet_code_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wrapper_code_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  flex_wrapper_code_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wrapper_code_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType  flex_wrapper_code_ )) (in custom URValue at level 0) : ursus_scope.

 Notation " 'FlexSellArgsAddrs.my_tip3_addr' " := ( ULState  FlexSellArgsAddrs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgsAddrs.my_tip3_addr' " := ( URState  FlexSellArgsAddrs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price' " := ( ULState  FlexSellArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price' " := ( URState  FlexSellArgs_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.amount' " := ( ULState  FlexSellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.amount' " := ( URState  FlexSellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.lend_finish_time' " := ( ULState  FlexSellArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.lend_finish_time' " := ( URState  FlexSellArgs_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.min_amount' " := ( ULState  FlexSellArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.min_amount' " := ( URState  FlexSellArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.deals_limit' " := ( ULState  FlexSellArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.deals_limit' " := ( URState  FlexSellArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tons_value' " := ( ULState  FlexSellArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tons_value' " := ( URState  FlexSellArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price_code' " := ( ULState  FlexSellArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price_code' " := ( URState  FlexSellArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.addrs' " := ( ULState  FlexSellArgs_ι_addrs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.addrs' " := ( URState  FlexSellArgs_ι_addrs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3_code' " := ( ULState  FlexSellArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3_code' " := ( URState  FlexSellArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3cfg' " := ( ULState  FlexSellArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3cfg' " := ( URState  FlexSellArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price' " := ( ULState  FlexBuyArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price' " := ( URState  FlexBuyArgs_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.amount' " := ( ULState  FlexBuyArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.amount' " := ( URState  FlexBuyArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.order_finish_time' " := ( ULState  FlexBuyArgs_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.order_finish_time' " := ( URState  FlexBuyArgs_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.min_amount' " := ( ULState  FlexBuyArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.min_amount' " := ( URState  FlexBuyArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deals_limit' " := ( ULState  FlexBuyArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deals_limit' " := ( URState  FlexBuyArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deploy_value' " := ( ULState  FlexBuyArgs_ι_deploy_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deploy_value' " := ( URState  FlexBuyArgs_ι_deploy_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price_code' " := ( ULState  FlexBuyArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price_code' " := ( URState  FlexBuyArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.my_tip3_addr' " := ( ULState  FlexBuyArgs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.my_tip3_addr' " := ( URState  FlexBuyArgs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3_code' " := ( ULState  FlexBuyArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3_code' " := ( URState  FlexBuyArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3cfg' " := ( ULState  FlexBuyArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3cfg' " := ( URState  FlexBuyArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.major_tip3cfg' " := ( ULState  FlexXchgCfgs_ι_major_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.major_tip3cfg' " := ( URState  FlexXchgCfgs_ι_major_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.minor_tip3cfg' " := ( ULState  FlexXchgCfgs_ι_minor_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.minor_tip3cfg' " := ( URState  FlexXchgCfgs_ι_minor_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.sell' " := ( ULState  FlexXchgArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.sell' " := ( URState  FlexXchgArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_num' " := ( ULState  FlexXchgArgs_ι_price_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_num' " := ( URState  FlexXchgArgs_ι_price_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_denum' " := ( ULState  FlexXchgArgs_ι_price_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_denum' " := ( URState  FlexXchgArgs_ι_price_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.amount' " := ( ULState  FlexXchgArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.amount' " := ( URState  FlexXchgArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_amount' " := ( ULState  FlexXchgArgs_ι_lend_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_amount' " := ( URState  FlexXchgArgs_ι_lend_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_finish_time' " := ( ULState  FlexXchgArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_finish_time' " := ( URState  FlexXchgArgs_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.min_amount' " := ( ULState  FlexXchgArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.min_amount' " := ( URState  FlexXchgArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.deals_limit' " := ( ULState  FlexXchgArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.deals_limit' " := ( URState  FlexXchgArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tons_value' " := ( ULState  FlexXchgArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tons_value' " := ( URState  FlexXchgArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.xchg_price_code' " := ( ULState  FlexXchgArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.xchg_price_code' " := ( URState  FlexXchgArgs_ι_xchg_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.addrs' " := ( ULState  FlexXchgArgs_ι_addrs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.addrs' " := ( URState  FlexXchgArgs_ι_addrs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3_code' " := ( ULState  FlexXchgArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3_code' " := ( URState  FlexXchgArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3cfgs' " := ( ULState  FlexXchgArgs_ι_tip3cfgs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3cfgs' " := ( URState  FlexXchgArgs_ι_tip3cfgs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price' " := ( ULState  FlexCancelArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price' " := ( URState  FlexCancelArgs_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.min_amount' " := ( ULState  FlexCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.min_amount' " := ( URState  FlexCancelArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.deals_limit' " := ( ULState  FlexCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.deals_limit' " := ( URState  FlexCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.value' " := ( ULState  FlexCancelArgs_ι_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.value' " := ( URState  FlexCancelArgs_ι_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price_code' " := ( ULState  FlexCancelArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price_code' " := ( URState  FlexCancelArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3_code' " := ( ULState  FlexCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3_code' " := ( URState  FlexCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3cfg' " := ( ULState  FlexCancelArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3cfg' " := ( URState  FlexCancelArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.sell' " := ( ULState  FlexXchgCancelArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.sell' " := ( URState  FlexXchgCancelArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_num' " := ( ULState  FlexXchgCancelArgs_ι_price_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_num' " := ( URState  FlexXchgCancelArgs_ι_price_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_denum' " := ( ULState  FlexXchgCancelArgs_ι_price_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_denum' " := ( URState  FlexXchgCancelArgs_ι_price_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.min_amount' " := ( ULState  FlexXchgCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.min_amount' " := ( URState  FlexXchgCancelArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.deals_limit' " := ( ULState  FlexXchgCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.deals_limit' " := ( URState  FlexXchgCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.value' " := ( ULState  FlexXchgCancelArgs_ι_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.value' " := ( URState  FlexXchgCancelArgs_ι_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.xchg_price_code' " := ( ULState  FlexXchgCancelArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.xchg_price_code' " := ( URState  FlexXchgCancelArgs_ι_xchg_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3_code' " := ( ULState  FlexXchgCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3_code' " := ( URState  FlexXchgCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3cfgs' " := ( ULState  FlexXchgCancelArgs_ι_tip3cfgs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3cfgs' " := ( URState  FlexXchgCancelArgs_ι_tip3cfgs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.flex_addr_' " := ( ULState  XchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.flex_addr_' " := ( URState  XchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_major_root_' " := ( ULState  XchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_major_root_' " := ( URState  XchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_minor_root_' " := ( ULState  XchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_minor_root_' " := ( URState  XchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.deploy_value_' " := ( ULState  XchgPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.deploy_value_' " := ( URState  XchgPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.original_amount' " := ( ULState  OrderInfo_ι_original_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.original_amount' " := ( URState  OrderInfo_ι_original_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.amount' " := ( ULState  OrderInfo_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.amount' " := ( URState  OrderInfo_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.account' " := ( ULState  OrderInfo_ι_account ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.account' " := ( URState  OrderInfo_ι_account ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.tip3_wallet' " := ( ULState  OrderInfo_ι_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.tip3_wallet' " := ( URState  OrderInfo_ι_tip3_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.client_addr' " := ( ULState  OrderInfo_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.client_addr' " := ( URState  OrderInfo_ι_client_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.order_finish_time' " := ( ULState  OrderInfo_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.order_finish_time' " := ( URState  OrderInfo_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.name' " := ( ULState  Tip3Config_ι_name ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.name' " := ( URState  Tip3Config_ι_name ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.symbol' " := ( ULState  Tip3Config_ι_symbol ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.symbol' " := ( URState  Tip3Config_ι_symbol ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.decimals' " := ( ULState  Tip3Config_ι_decimals ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.decimals' " := ( URState  Tip3Config_ι_decimals ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_public_key' " := ( ULState  Tip3Config_ι_root_public_key ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_public_key' " := ( URState  Tip3Config_ι_root_public_key ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_address' " := ( ULState  Tip3Config_ι_root_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_address' " := ( URState  Tip3Config_ι_root_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.price_' " := ( ULState  Price_ι_price_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.price_' " := ( URState  Price_ι_price_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount_' " := ( ULState  Price_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount_' " := ( URState  Price_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.buys_amount_' " := ( ULState  Price_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.buys_amount_' " := ( URState  Price_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.flex_' " := ( ULState  Price_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.flex_' " := ( URState  Price_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.min_amount_' " := ( ULState  Price_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.min_amount_' " := ( URState  Price_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.deals_limit_' " := ( ULState  Price_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.deals_limit_' " := ( URState  Price_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.notify_addr_' " := ( ULState  Price_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.notify_addr_' " := ( URState  Price_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.workchain_id_' " := ( ULState  Price_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.workchain_id_' " := ( URState  Price_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tons_cfg_' " := ( ULState  Price_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tons_cfg_' " := ( URState  Price_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tip3_code_' " := ( ULState  Price_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tip3_code_' " := ( URState  Price_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tip3cfg_' " := ( ULState  Price_ι_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tip3cfg_' " := ( URState  Price_ι_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.sells_' " := ( ULState  Price_ι_sells_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.sells_' " := ( URState  Price_ι_sells_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.buys_' " := ( ULState  Price_ι_buys_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.buys_' " := ( URState  Price_ι_buys_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.num' " := ( ULState  RationalPrice_ι_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.num' " := ( URState  RationalPrice_ι_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.denum' " := ( ULState  RationalPrice_ι_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.denum' " := ( URState  RationalPrice_ι_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.price_' " := ( ULState  PriceXchg_ι_price_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.price_' " := ( URState  PriceXchg_ι_price_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.sells_amount_' " := ( ULState  PriceXchg_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.sells_amount_' " := ( URState  PriceXchg_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.buys_amount_' " := ( ULState  PriceXchg_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.buys_amount_' " := ( URState  PriceXchg_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.flex_' " := ( ULState  PriceXchg_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.flex_' " := ( URState  PriceXchg_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.min_amount_' " := ( ULState  PriceXchg_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.min_amount_' " := ( URState  PriceXchg_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.deals_limit_' " := ( ULState  PriceXchg_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.deals_limit_' " := ( URState  PriceXchg_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.notify_addr_' " := ( ULState  PriceXchg_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.notify_addr_' " := ( URState  PriceXchg_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.workchain_id_' " := ( ULState  PriceXchg_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.workchain_id_' " := ( URState  PriceXchg_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tons_cfg_' " := ( ULState  PriceXchg_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tons_cfg_' " := ( URState  PriceXchg_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tip3_code_' " := ( ULState  PriceXchg_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tip3_code_' " := ( URState  PriceXchg_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.major_tip3cfg_' " := ( ULState  PriceXchg_ι_major_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.major_tip3cfg_' " := ( URState  PriceXchg_ι_major_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( ULState  PriceXchg_ι_minor_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( URState  PriceXchg_ι_minor_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TradingPair.flex_addr_' " := ( ULState  TradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TradingPair.flex_addr_' " := ( URState  TradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TradingPair.tip3_root_' " := ( ULState  TradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TradingPair.tip3_root_' " := ( URState  TradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TradingPair.deploy_value_' " := ( ULState  TradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TradingPair.deploy_value_' " := ( URState  TradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.sell' " := ( ULState  PayloadArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.sell' " := ( URState  PayloadArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.amount' " := ( ULState  PayloadArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.amount' " := ( URState  PayloadArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( ULState  PayloadArgs_ι_receive_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( URState  PayloadArgs_ι_receive_tip3_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.client_addr' " := ( ULState  PayloadArgs_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.client_addr' " := ( URState  PayloadArgs_ι_client_addr ) (in custom URValue at level 0) : ursus_scope.

Notation " 'error_code::zero_owner_pubkey' " := (sInject error_code_ι_zero_owner_pubkey) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wallet_code' " := (sInject error_code_ι_missed_flex_wallet_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wrapper_code' " := (sInject error_code_ι_missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 
(*TODO*)
Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 

Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.


Definition Flex_Ф_constructor_call { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  
( deployer_pubkey : URValue XInteger256 a1 ) 
( transfer_tip3 : URValue XInteger128 a2 ) 
( return_ownership : URValue XInteger128 a3 ) 
( trading_pair_deploy : URValue XInteger128 a4 ) 
( order_answer : URValue XInteger128 a5 ) 
( process_queue : URValue XInteger128 a6 ) 
( send_notify : URValue XInteger128 a7 ) 
( deals_limit : URValue XInteger8 a8 ) 
( notify_addr : URValue XAddress a9 ) 
: LedgerT ( ControlResult PhantomType ( orb(orb (orb (orb (orb (orb (orb (orb a9 a8) a7) a6) a5) a4) a3) a2) a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ9 ) Flex_Ф_constructor 
 ( SimpleLedgerableArg URValue {{ Λ "deployer_pubkey" }} ( deployer_pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "transfer_tip3" }} ( transfer_tip3 ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "return_ownership" }} ( return_ownership ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "trading_pair_deploy" }} ( trading_pair_deploy ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "order_answer" }} ( order_answer ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "process_queue" }} ( process_queue ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "send_notify" }} ( send_notify ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "notify_addr" }} ( notify_addr ) ) 
 . 
 Notation " 'Flex_Ф_constructor_ref_' '(' deployer_pubkey transfer_tip3 return_ownership trading_pair_deploy order_answer process_queue send_notify deals_limit notify_addr ')' " := 
 ( FuncallExpression ( Flex_Ф_constructor_call 
 deployer_pubkey transfer_tip3 return_ownership trading_pair_deploy order_answer process_queue send_notify deals_limit notify_addr )) 
 (in custom ULValue at level 0 , deployer_pubkey custom URValue at level 0 
 , transfer_tip3 custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , trading_pair_deploy custom URValue at level 0 
 , order_answer custom URValue at level 0 
 , process_queue custom URValue at level 0 
 , send_notify custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

 Definition Flex_Ф_setPairCode_call { a1 }  ( code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Flex_Ф_setPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} ( code ) ) 
 . 
 Notation " 'Flex_Ф_setPairCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( Flex_Ф_setPairCode_call 
 code )) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 

 Definition Flex_Ф_setXchgPairCode_call { a1 }  ( code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Flex_Ф_setXchgPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} ( code ) ) 
 . 
 Notation " 'Flex_Ф_setXchgPairCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( Flex_Ф_setXchgPairCode_call 
 code )) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_setPriceCode_call { a1 }  ( code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Flex_Ф_setPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} ( code ) ) 
 . 
 Notation " 'Flex_Ф_setPriceCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( Flex_Ф_setPriceCode_call 
 code )) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_setXchgPriceCode_call { a1 }  ( code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Flex_Ф_setXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} ( code ) ) 
 . 
 Notation " 'Flex_Ф_setXchgPriceCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( Flex_Ф_setXchgPriceCode_call 
 code )) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_isFullyInitialized_call  : LedgerT ( ControlResult XBool false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Flex_Ф_isFullyInitialized 
 . 
 Notation " 'Flex_Ф_isFullyInitialized_ref_' '(' ')' " := 
 ( URResult ( Flex_Ф_isFullyInitialized_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition Flex_Ф_getTonsCfg_call  : LedgerT ( ControlResult TonsConfigStateLRecord false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Flex_Ф_getTonsCfg .

 Notation " 'Flex_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( URResult ( Flex_Ф_getTonsCfg_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_getTradingPairCode_call  : LedgerT ( ControlResult XCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Flex_Ф_getTradingPairCode 
 . 
 Notation " 'Flex_Ф_getTradingPairCode_ref_' '(' ')' " := 
 ( URResult ( Flex_Ф_getTradingPairCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_getXchgPairCode_call  : LedgerT ( ControlResult XCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Flex_Ф_getXchgPairCode 
 . 
 Notation " 'Flex_Ф_getXchgPairCode_ref_' '(' ')' " := 
 ( URResult ( Flex_Ф_getXchgPairCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_getSellPriceCode_call { a1 }  ( tip3_addr : URValue XAddress a1 ) : LedgerT ( ControlResult XCell true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Flex_Ф_getSellPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr" }} ( tip3_addr ) ) 
 . 
 Notation " 'Flex_Ф_getSellPriceCode_ref_' '(' tip3_addr ')' " := 
 ( URResult ( Flex_Ф_getSellPriceCode_call 
 tip3_addr )) 
 (in custom URValue at level 0 , tip3_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_getXchgPriceCode_call { a1 a2 }  ( tip3_addr1 : URValue XAddress a1 ) ( tip3_addr2 : URValue XAddress a2 ) : LedgerT ( ControlResult XCell true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Flex_Ф_getXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr1" }} ( tip3_addr1 ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr2" }} ( tip3_addr2 ) ) 
 . 
 Notation " 'Flex_Ф_getXchgPriceCode_ref_' '(' tip3_addr1 tip3_addr2 ')' " := 
 ( URResult ( Flex_Ф_getXchgPriceCode_call 
 tip3_addr1 tip3_addr2 )) 
 (in custom URValue at level 0 , tip3_addr1 custom URValue at level 0 
 , tip3_addr2 custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_getSellTradingPair_call { a1 }  ( tip3_root : URValue XAddress a1 ) : LedgerT ( ControlResult XAddress a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Flex_Ф_getSellTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_root" }} ( tip3_root ) ) 
 . 
 Notation " 'Flex_Ф_getSellTradingPair_ref_' '(' tip3_root ')' " := 
 ( URResult ( Flex_Ф_getSellTradingPair_call 
 tip3_root )) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_getXchgTradingPair_call { a1 a2 }  ( tip3_major_root : URValue XAddress a1 ) ( tip3_minor_root : URValue XAddress a2 ) : LedgerT ( ControlResult XAddress ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Flex_Ф_getXchgTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_major_root" }} ( tip3_major_root ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_minor_root" }} ( tip3_minor_root ) ) 
 . 
 Notation " 'Flex_Ф_getXchgTradingPair_ref_' '(' tip3_major_root tip3_minor_root ')' " := 
 ( URResult ( Flex_Ф_getXchgTradingPair_call 
 tip3_major_root tip3_minor_root )) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_getDealsLimit_call  : LedgerT ( ControlResult XInteger8 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Flex_Ф_getDealsLimit 
 . 
 Notation " 'Flex_Ф_getDealsLimit_ref_' '(' ')' " := 
 ( URResult ( Flex_Ф_getDealsLimit_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф_getNotifyAddr_call  : LedgerT ( ControlResult XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Flex_Ф_getNotifyAddr 
 . 
 Notation " 'Flex_Ф_getNotifyAddr_ref_' '(' ')' " := 
 ( URResult ( Flex_Ф_getNotifyAddr_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Flex_Ф__fallback_call ( x : URValue XCell false ) : LedgerT ( ControlResult XInteger false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Flex_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "x" }} ( x ) ) .

 Notation " 'Flex_Ф__fallback_ref_' '(' x ')' " := 
 ( URResult ( Flex_Ф__fallback_call x )) 
 (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope . 



End Calls. 

End FuncNotations.
