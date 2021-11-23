
Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.BasicModuleTypes.
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
 Notation " 'Price.price_' " := ( ULState  DPrice_ι_price_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.price_' " := ( URState  DPrice_ι_price_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount_' " := ( ULState  DPrice_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount_' " := ( URState  DPrice_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.buys_amount_' " := ( ULState  DPrice_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.buys_amount_' " := ( URState  DPrice_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.flex_' " := ( ULState  DPrice_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.flex_' " := ( URState  DPrice_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.min_amount_' " := ( ULState  DPrice_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.min_amount_' " := ( URState  DPrice_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.deals_limit_' " := ( ULState  DPrice_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.deals_limit_' " := ( URState  DPrice_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.notify_addr_' " := ( ULState  DPrice_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.notify_addr_' " := ( URState  DPrice_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.workchain_id_' " := ( ULState  DPrice_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.workchain_id_' " := ( URState  DPrice_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tons_cfg_' " := ( ULState  DPrice_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tons_cfg_' " := ( URState  DPrice_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tip3_code_' " := ( ULState  DPrice_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tip3_code_' " := ( URState  DPrice_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tip3cfg_' " := ( ULState  DPrice_ι_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tip3cfg_' " := ( URState  DPrice_ι_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.num' " := ( ULState  RationalPrice_ι_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.num' " := ( URState  RationalPrice_ι_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.denum' " := ( ULState  RationalPrice_ι_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.denum' " := ( URState  RationalPrice_ι_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.price_' " := ( ULState  DPriceXchg_ι_price_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.price_' " := ( URState  DPriceXchg_ι_price_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.sells_amount_' " := ( ULState  DPriceXchg_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.sells_amount_' " := ( URState  DPriceXchg_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.buys_amount_' " := ( ULState  DPriceXchg_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.buys_amount_' " := ( URState  DPriceXchg_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.flex_' " := ( ULState  DPriceXchg_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.flex_' " := ( URState  DPriceXchg_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.min_amount_' " := ( ULState  DPriceXchg_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.min_amount_' " := ( URState  DPriceXchg_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.deals_limit_' " := ( ULState  DPriceXchg_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.deals_limit_' " := ( URState  DPriceXchg_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.notify_addr_' " := ( ULState  DPriceXchg_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.notify_addr_' " := ( URState  DPriceXchg_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.workchain_id_' " := ( ULState  DPriceXchg_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.workchain_id_' " := ( URState  DPriceXchg_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tons_cfg_' " := ( ULState  DPriceXchg_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tons_cfg_' " := ( URState  DPriceXchg_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tip3_code_' " := ( ULState  DPriceXchg_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tip3_code_' " := ( URState  DPriceXchg_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.major_tip3cfg_' " := ( ULState  DPriceXchg_ι_major_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.major_tip3cfg_' " := ( URState  DPriceXchg_ι_major_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( ULState  DPriceXchg_ι_minor_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( URState  DPriceXchg_ι_minor_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
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


End Calls. 

End FuncNotations.
