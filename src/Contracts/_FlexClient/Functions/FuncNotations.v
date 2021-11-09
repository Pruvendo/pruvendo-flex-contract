
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

Require Import Contracts.FlexClient.Ledger.
Require Import Contracts.FlexClient.Functions.FuncSig.

(* здесь инмпортируем все внешние интерфейсы *)
Require Import Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module FlexPublicInterface := PublicInterface xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.


Import xt.

Import UrsusNotations.

Local Open Scope ursus_scope.

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
 
 Definition owner__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType owner_ ) : ULValue XInteger256 ) . 
 Definition owner__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType owner_ ) : URValue XInteger256 false ) . 
 Notation " '_owner_' " := ( owner__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_owner_' " := ( owner__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition trading_pair_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType trading_pair_code_ ) : ULValue XCell ) . 
 Definition trading_pair_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType trading_pair_code_ ) : URValue XCell false ) . 
 Notation " '_trading_pair_code_' " := ( trading_pair_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_trading_pair_code_' " := ( trading_pair_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition xchg_pair_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_code_ ) : ULValue XCell ) . 
 Definition xchg_pair_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_code_ ) : URValue XCell false ) . 
 Notation " '_xchg_pair_code_' " := ( xchg_pair_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_xchg_pair_code_' " := ( xchg_pair_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : ULValue XInteger8 ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : URValue XInteger8 false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tons_cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : ULValue TonsConfigLRecord ) . 
 Definition tons_cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : URValue TonsConfigLRecord false ) . 
 Notation " '_tons_cfg_' " := ( tons_cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tons_cfg_' " := ( tons_cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : ULValue XAddress (* addr_std_compact *) ) . 
 Definition flex__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : URValue XAddress (* addr_std_compact *) false ) . 
 Notation " '_flex_' " := ( flex__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_' " := ( flex__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition ext_wallet_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType ext_wallet_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition ext_wallet_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType ext_wallet_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_ext_wallet_code_' " := ( ext_wallet_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_ext_wallet_code_' " := ( ext_wallet_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex_wallet_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType flex_wallet_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition flex_wallet_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType flex_wallet_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_flex_wallet_code_' " := ( flex_wallet_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_wallet_code_' " := ( flex_wallet_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex_wrapper_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType flex_wrapper_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition flex_wrapper_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType flex_wrapper_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_flex_wrapper_code_' " := ( flex_wrapper_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_wrapper_code_' " := ( flex_wrapper_code__right ) (in custom URValue at level 0) : ursus_scope. 
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
 Notation " 'anycast_info.rewrite_pfx' " := ( anycast_info_ι_rewrite_pfx ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'anycast_info.rewrite_pfx' " := ( anycast_info_ι_rewrite_pfx ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std.kind' " := ( addr_std_ι_kind ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std.kind' " := ( addr_std_ι_kind ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std.Anycast' " := ( addr_std_ι_Anycast ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std.Anycast' " := ( addr_std_ι_Anycast ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std.workchain_id' " := ( addr_std_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std.workchain_id' " := ( addr_std_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std.address' " := ( addr_std_ι_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std.address' " := ( addr_std_ι_address ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'SellArgs.amount' " := ( SellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'SellArgs.amount' " := ( SellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'SellArgs.receive_wallet' " := ( SellArgs_ι_receive_wallet ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'SellArgs.receive_wallet' " := ( SellArgs_ι_receive_wallet ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBurnWalletArgs.tons_value' " := ( FlexBurnWalletArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBurnWalletArgs.tons_value' " := ( FlexBurnWalletArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBurnWalletArgs.out_pubkey' " := ( FlexBurnWalletArgs_ι_out_pubkey ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBurnWalletArgs.out_pubkey' " := ( FlexBurnWalletArgs_ι_out_pubkey ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBurnWalletArgs.out_internal_owner' " := ( FlexBurnWalletArgs_ι_out_internal_owner ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBurnWalletArgs.out_internal_owner' " := ( FlexBurnWalletArgs_ι_out_internal_owner ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBurnWalletArgs.my_tip3_addr' " := ( FlexBurnWalletArgs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBurnWalletArgs.my_tip3_addr' " := ( FlexBurnWalletArgs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope. 
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
 Notation " 'FlexSellArgsAddrs.my_tip3_addr' " := ( FlexSellArgsAddrs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgsAddrs.my_tip3_addr' " := ( FlexSellArgsAddrs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.price' " := ( FlexSellArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.price' " := ( FlexSellArgs_ι_price ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.amount' " := ( FlexSellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.amount' " := ( FlexSellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.lend_finish_time' " := ( FlexSellArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.lend_finish_time' " := ( FlexSellArgs_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.min_amount' " := ( FlexSellArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.min_amount' " := ( FlexSellArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.deals_limit' " := ( FlexSellArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.deals_limit' " := ( FlexSellArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.tons_value' " := ( FlexSellArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.tons_value' " := ( FlexSellArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.price_code' " := ( FlexSellArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.price_code' " := ( FlexSellArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.addrs' " := ( FlexSellArgs_ι_addrs ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.addrs' " := ( FlexSellArgs_ι_addrs ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.tip3_code' " := ( FlexSellArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.tip3_code' " := ( FlexSellArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.tip3cfg' " := ( FlexSellArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexSellArgs.tip3cfg' " := ( FlexSellArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.price' " := ( FlexBuyArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.price' " := ( FlexBuyArgs_ι_price ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.amount' " := ( FlexBuyArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.amount' " := ( FlexBuyArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.order_finish_time' " := ( FlexBuyArgs_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.order_finish_time' " := ( FlexBuyArgs_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.min_amount' " := ( FlexBuyArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.min_amount' " := ( FlexBuyArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.deals_limit' " := ( FlexBuyArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.deals_limit' " := ( FlexBuyArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.deploy_value' " := ( FlexBuyArgs_ι_deploy_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.deploy_value' " := ( FlexBuyArgs_ι_deploy_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.price_code' " := ( FlexBuyArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.price_code' " := ( FlexBuyArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.my_tip3_addr' " := ( FlexBuyArgs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.my_tip3_addr' " := ( FlexBuyArgs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.tip3_code' " := ( FlexBuyArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.tip3_code' " := ( FlexBuyArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.tip3cfg' " := ( FlexBuyArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexBuyArgs.tip3cfg' " := ( FlexBuyArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCfgs.major_tip3cfg' " := ( FlexXchgCfgs_ι_major_tip3cfg ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCfgs.major_tip3cfg' " := ( FlexXchgCfgs_ι_major_tip3cfg ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCfgs.minor_tip3cfg' " := ( FlexXchgCfgs_ι_minor_tip3cfg ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCfgs.minor_tip3cfg' " := ( FlexXchgCfgs_ι_minor_tip3cfg ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.sell' " := ( FlexXchgArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.sell' " := ( FlexXchgArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.price_num' " := ( FlexXchgArgs_ι_price_num ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.price_num' " := ( FlexXchgArgs_ι_price_num ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.price_denum' " := ( FlexXchgArgs_ι_price_denum ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.price_denum' " := ( FlexXchgArgs_ι_price_denum ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.amount' " := ( FlexXchgArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.amount' " := ( FlexXchgArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.lend_amount' " := ( FlexXchgArgs_ι_lend_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.lend_amount' " := ( FlexXchgArgs_ι_lend_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.lend_finish_time' " := ( FlexXchgArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.lend_finish_time' " := ( FlexXchgArgs_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.min_amount' " := ( FlexXchgArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.min_amount' " := ( FlexXchgArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.deals_limit' " := ( FlexXchgArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.deals_limit' " := ( FlexXchgArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.tons_value' " := ( FlexXchgArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.tons_value' " := ( FlexXchgArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.xchg_price_code' " := ( FlexXchgArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.xchg_price_code' " := ( FlexXchgArgs_ι_xchg_price_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.addrs' " := ( FlexXchgArgs_ι_addrs ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.addrs' " := ( FlexXchgArgs_ι_addrs ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.tip3_code' " := ( FlexXchgArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.tip3_code' " := ( FlexXchgArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.tip3cfgs' " := ( FlexXchgArgs_ι_tip3cfgs ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgArgs.tip3cfgs' " := ( FlexXchgArgs_ι_tip3cfgs ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.price' " := ( FlexCancelArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.price' " := ( FlexCancelArgs_ι_price ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.min_amount' " := ( FlexCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.min_amount' " := ( FlexCancelArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.deals_limit' " := ( FlexCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.deals_limit' " := ( FlexCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.value' " := ( FlexCancelArgs_ι_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.value' " := ( FlexCancelArgs_ι_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.price_code' " := ( FlexCancelArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.price_code' " := ( FlexCancelArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.tip3_code' " := ( FlexCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.tip3_code' " := ( FlexCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.tip3cfg' " := ( FlexCancelArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexCancelArgs.tip3cfg' " := ( FlexCancelArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.sell' " := ( FlexXchgCancelArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.sell' " := ( FlexXchgCancelArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.price_num' " := ( FlexXchgCancelArgs_ι_price_num ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.price_num' " := ( FlexXchgCancelArgs_ι_price_num ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.price_denum' " := ( FlexXchgCancelArgs_ι_price_denum ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.price_denum' " := ( FlexXchgCancelArgs_ι_price_denum ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.min_amount' " := ( FlexXchgCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.min_amount' " := ( FlexXchgCancelArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.deals_limit' " := ( FlexXchgCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.deals_limit' " := ( FlexXchgCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.value' " := ( FlexXchgCancelArgs_ι_value ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.value' " := ( FlexXchgCancelArgs_ι_value ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.xchg_price_code' " := ( FlexXchgCancelArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.xchg_price_code' " := ( FlexXchgCancelArgs_ι_xchg_price_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.tip3_code' " := ( FlexXchgCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.tip3_code' " := ( FlexXchgCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.tip3cfgs' " := ( FlexXchgCancelArgs_ι_tip3cfgs ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexXchgCancelArgs.tip3cfgs' " := ( FlexXchgCancelArgs_ι_tip3cfgs ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.flex_addr_' " := ( XchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.flex_addr_' " := ( XchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_major_root_' " := ( XchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_major_root_' " := ( XchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_minor_root_' " := ( XchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_minor_root_' " := ( XchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.notify_addr_' " := ( XchgPair_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.notify_addr_' " := ( XchgPair_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 
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
 Notation " 'Price.price_' " := ( DPrice_ι_price_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.price_' " := ( DPrice_ι_price_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.sells_amount_' " := ( DPrice_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.sells_amount_' " := ( DPrice_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.buys_amount_' " := ( DPrice_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.buys_amount_' " := ( DPrice_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.flex_' " := ( DPrice_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.flex_' " := ( DPrice_ι_flex_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.min_amount_' " := ( DPrice_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.min_amount_' " := ( DPrice_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.deals_limit_' " := ( DPrice_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.deals_limit_' " := ( DPrice_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.notify_addr_' " := ( DPrice_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.notify_addr_' " := ( DPrice_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.workchain_id_' " := ( DPrice_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.workchain_id_' " := ( DPrice_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.tons_cfg_' " := ( DPrice_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.tons_cfg_' " := ( DPrice_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.tip3_code_' " := ( DPrice_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.tip3_code_' " := ( DPrice_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.tip3cfg_' " := ( DPrice_ι_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.tip3cfg_' " := ( DPrice_ι_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.num' " := ( RationalPrice_ι_num ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.num' " := ( RationalPrice_ι_num ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.denum' " := ( RationalPrice_ι_denum ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.denum' " := ( RationalPrice_ι_denum ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.price_' " := ( DPriceXchg_ι_price_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.price_' " := ( DPriceXchg_ι_price_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.sells_amount_' " := ( DPriceXchg_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.sells_amount_' " := ( DPriceXchg_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.buys_amount_' " := ( DPriceXchg_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.buys_amount_' " := ( DPriceXchg_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.flex_' " := ( DPriceXchg_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.flex_' " := ( DPriceXchg_ι_flex_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.min_amount_' " := ( DPriceXchg_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.min_amount_' " := ( DPriceXchg_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.deals_limit_' " := ( DPriceXchg_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.deals_limit_' " := ( DPriceXchg_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.notify_addr_' " := ( DPriceXchg_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.notify_addr_' " := ( DPriceXchg_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.workchain_id_' " := ( DPriceXchg_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.workchain_id_' " := ( DPriceXchg_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.tons_cfg_' " := ( DPriceXchg_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.tons_cfg_' " := ( DPriceXchg_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.tip3_code_' " := ( DPriceXchg_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.tip3_code_' " := ( DPriceXchg_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.major_tip3cfg_' " := ( DPriceXchg_ι_major_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.major_tip3cfg_' " := ( DPriceXchg_ι_major_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( DPriceXchg_ι_minor_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( DPriceXchg_ι_minor_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.flex_addr_' " := ( TradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.flex_addr_' " := ( TradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( TradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( TradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( TradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( TradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.notify_addr_' " := ( TradingPair_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.notify_addr_' " := ( TradingPair_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.sell' " := ( PayloadArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.sell' " := ( PayloadArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.amount' " := ( PayloadArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.amount' " := ( PayloadArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_ι_receive_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_ι_receive_tip3_wallet ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( PayloadArgs_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( PayloadArgs_ι_client_addr ) (in custom URValue at level 0) : ursus_scope. 
 
Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_ext_wallet_code' " := (sInject error_code_ι_missed_ext_wallet_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wallet_code' " := (sInject error_code_ι_missed_flex_wallet_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wrapper_code' " := (sInject error_code_ι_missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::zero_owner_pubkey' " := (sInject error_code_ι_zero_owner_pubkey) (in custom URValue at level 0) : ursus_scope. 

Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

 Definition constructor_left { R a1 a2 a3 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( trading_pair_code : URValue ( XCell ) a2 ) ( xchg_pair_code : URValue ( XCell ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) constructor 
 pubkey trading_pair_code xchg_pair_code ) . 
 
 Notation " 'constructor_' '(' pubkey trading_pair_code xchg_pair_code ')' " := 
 ( constructor_left 
 pubkey trading_pair_code xchg_pair_code ) 
 (in custom ULValue at level 0 , pubkey custom URValue at level 0 
 , trading_pair_code custom URValue at level 0 
 , xchg_pair_code custom URValue at level 0 ) : ursus_scope .
 
 Definition setFlexCfg_left { R a1 a2 }  ( tons_cfg : URValue ( TonsConfigLRecord ) a1 ) ( flex : URValue ( XAddress ) a2 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) setFlexCfg 
 tons_cfg flex ) . 
 
 Notation " 'setFlexCfg_' '(' tons_cfg flex ')' " := 
 ( setFlexCfg_left 
 tons_cfg flex ) 
 (in custom ULValue at level 0 , tons_cfg custom URValue at level 0 
 , flex custom URValue at level 0 ) : ursus_scope . 
 
 Definition setExtWalletCode_left { R a1 }  ( ext_wallet_code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setExtWalletCode 
 ext_wallet_code ) . 
 
 Notation " 'setExtWalletCode_' '(' ext_wallet_code ')' " := 
 ( setExtWalletCode_left 
 ext_wallet_code ) 
 (in custom ULValue at level 0 , ext_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setFlexWalletCode_left { R a1 }  ( flex_wallet_code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setFlexWalletCode 
 flex_wallet_code ) . 
 
 Notation " 'setFlexWalletCode_' '(' flex_wallet_code ')' " := 
 ( setFlexWalletCode_left 
 flex_wallet_code ) 
 (in custom ULValue at level 0 , flex_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setFlexWrapperCode_left { R a1 }  ( flex_wrapper_code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setFlexWrapperCode 
 flex_wrapper_code ) . 
 
 Notation " 'setFlexWrapperCode_' '(' flex_wrapper_code ')' " := 
 ( setFlexWrapperCode_left 
 flex_wrapper_code ) 
 (in custom ULValue at level 0 , flex_wrapper_code custom URValue at level 0 ) : ursus_scope .

 Definition deployTradingPair_right { a1 a2 a3 a4 a5 }  ( tip3_root : URValue ( XAddress ) a1 ) ( deploy_min_value : URValue ( XInteger128 ) a2 ) ( deploy_value : URValue ( XInteger128 ) a3 ) ( min_trade_amount : URValue ( XInteger128 ) a4 ) ( notify_addr : URValue ( XAddress ) a5 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) deployTradingPair 
 tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ) . 
 
 Notation " 'deployTradingPair_' '(' tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ')' " := 
 ( deployTradingPair_right 
 tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition deployXchgPair_right { a1 a2 a3 a4 a5 a6 }  ( tip3_major_root : URValue ( address_t ) a1 ) ( tip3_minor_root : URValue ( address_t ) a2 ) ( deploy_min_value : URValue ( XInteger128 ) a3 ) ( deploy_value : URValue ( XInteger128 ) a4 ) ( min_trade_amount : URValue ( XInteger128 ) a5 ) ( notify_addr : URValue ( address_t ) a6 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) deployXchgPair 
 tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ) . 
 
 Notation " 'deployXchgPair_' '(' tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ')' " := 
 ( deployXchgPair_right 
 tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition deployPriceWithSell_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 }  
( price : URValue ( XInteger128 ) a1 ) 
( amount : URValue ( XInteger128 ) a2 ) 
( lend_finish_time : URValue ( XInteger32 ) a3 ) 
( min_amount : URValue ( XInteger128 ) a4 ) 
( deals_limit : URValue ( XInteger8 ) a5 ) 
( tons_value : URValue ( XInteger128 ) a6 ) 
( price_code : URValue ( XCell ) a7 ) 
( my_tip3_addr : URValue ( XAddress ) a8 ) 
( receive_wallet : URValue ( XAddress ) a9 ) 
( tip3cfg : URValue ( Tip3ConfigLRecord ) a10 ) 
( notify_addr : URValue ( XAddress ) a11 ) 
: URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ11 ) deployPriceWithSell 
 price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceWithSell_' '(' price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ')' " := 
 ( deployPriceWithSell_right 
 price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , receive_wallet custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

 Definition deployPriceWithBuy_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  ( price : URValue ( XInteger128 ) a1 ) ( amount : URValue ( XInteger128 ) a2 ) ( order_finish_time : URValue ( XInteger32 ) a3 ) ( min_amount : URValue ( XInteger128 ) a4 ) ( deals_limit : URValue ( XInteger8 ) a5 ) ( deploy_value : URValue ( XInteger128 ) a6 ) ( price_code : URValue ( XCell ) a7 ) ( my_tip3_addr : URValue ( address_t ) a8 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a9 ) ( notify_addr : URValue ( address_t ) a10 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ10 ) deployPriceWithBuy 
 price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceWithBuy_' '(' price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ')' " := 
 ( deployPriceWithBuy_right 
 price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 
 , order_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition cancelSellOrder_left { R a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue ( XInteger128 ) a1 ) ( min_amount : URValue ( XInteger128 ) a2 ) ( deals_limit : URValue ( XInteger8 ) a3 ) ( value : URValue ( XInteger128 ) a4 ) ( price_code : URValue ( XCell ) a5 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) ( notify_addr : URValue ( address_t ) a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancelSellOrder 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) . 
 
 Notation " 'cancelSellOrder_' '(' price min_amount deals_limit value price_code tip3cfg notify_addr ')' " := 
 ( cancelSellOrder_left 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition cancelBuyOrder_left { R a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue ( XInteger128 ) a1 ) ( min_amount : URValue ( XInteger128 ) a2 ) ( deals_limit : URValue ( XInteger8 ) a3 ) ( value : URValue ( XInteger128 ) a4 ) ( price_code : URValue ( XCell ) a5 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) ( notify_addr : URValue ( address_t ) a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancelBuyOrder 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) . 
 
 Notation " 'cancelBuyOrder_' '(' price min_amount deals_limit value price_code tip3cfg notify_addr ')' " := 
 ( cancelBuyOrder_left 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition cancelXchgOrder_left { R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  ( sell : URValue ( XBool ) a1 ) ( price_num : URValue ( XInteger128 ) a2 ) ( price_denum : URValue ( XInteger128 ) a3 ) ( min_amount : URValue ( XInteger128 ) a4 ) ( deals_limit : URValue ( XInteger8 ) a5 ) ( value : URValue ( XInteger128 ) a6 ) ( xchg_price_code : URValue ( XCell ) a7 ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) a8 ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) a9 ) ( notify_addr : URValue ( address_t ) a10 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ10 ) cancelXchgOrder 
 sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ) . 
 
 Notation " 'cancelXchgOrder_' '(' sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ')' " := 
 ( cancelXchgOrder_left 
 sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , sell custom URValue at level 0 
 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , xchg_price_code custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_left { R a1 a2 a3 }  ( dest : URValue ( address_t ) a1 ) ( value : URValue ( XInteger128 ) a2 ) ( bounce : URValue ( XBool ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) transfer 
 dest value bounce ) . 
 
 Notation " 'transfer_' '(' dest value bounce ')' " := 
 ( transfer_left 
 dest value bounce ) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 
 , value custom URValue at level 0 
 , bounce custom URValue at level 0 ) : ursus_scope . 
 Definition deployPriceXchg_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 }  ( sell : URValue ( XBool ) a1 ) ( price_num : URValue ( XInteger128 ) a2 ) ( price_denum : URValue ( XInteger128 ) a3 ) ( amount : URValue ( XInteger128 ) a4 ) ( lend_amount : URValue ( XInteger128 ) a5 ) ( lend_finish_time : URValue ( XInteger32 ) a6 ) ( min_amount : URValue ( XInteger128 ) a7 ) ( deals_limit : URValue ( XInteger8 ) a8 ) ( tons_value : URValue ( XInteger128 ) a9 ) ( xchg_price_code : URValue ( XCell ) a10 ) ( my_tip3_addr : URValue ( address_t ) a11 ) ( receive_wallet : URValue ( address_t ) a12 ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) a13 ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) a14 ) ( notify_addr : URValue ( address_t ) a15 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ15 ) deployPriceXchg 
 sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceXchg_' '(' sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ')' " := 
 ( deployPriceXchg_right 
 sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ) 
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
 , minor_tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition deployWrapperWithWallet_right { a1 a2 a3 a4 a5 a6 }  ( wrapper_pubkey : URValue ( XInteger256 ) a1 ) ( wrapper_deploy_value : URValue ( XInteger128 ) a2 ) ( wrapper_keep_balance : URValue ( XInteger128 ) a3 ) ( ext_wallet_balance : URValue ( XInteger128 ) a4 ) ( set_internal_wallet_value : URValue ( XInteger128 ) a5 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) deployWrapperWithWallet 
 wrapper_pubkey wrapper_deploy_value wrapper_keep_balance ext_wallet_balance set_internal_wallet_value tip3cfg ) . 
 
 Notation " 'deployWrapperWithWallet_' '(' wrapper_pubkey wrapper_deploy_value wrapper_keep_balance ext_wallet_balance set_internal_wallet_value tip3cfg ')' " := 
 ( deployWrapperWithWallet_right 
 wrapper_pubkey wrapper_deploy_value wrapper_keep_balance ext_wallet_balance set_internal_wallet_value tip3cfg ) 
 (in custom URValue at level 0 , wrapper_pubkey custom URValue at level 0 
 , wrapper_deploy_value custom URValue at level 0 
 , wrapper_keep_balance custom URValue at level 0 
 , ext_wallet_balance custom URValue at level 0 
 , set_internal_wallet_value custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 Definition deployEmptyFlexWallet_right { a1 a2 a3 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( tons_to_wallet : URValue ( XInteger128 ) a2 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a3 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) deployEmptyFlexWallet 
 pubkey tons_to_wallet tip3cfg ) . 
 
 Notation " 'deployEmptyFlexWallet_' '(' pubkey tons_to_wallet tip3cfg ')' " := 
 ( deployEmptyFlexWallet_right 
 pubkey tons_to_wallet tip3cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , tons_to_wallet custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition burnWallet_left { R a1 a2 a3 a4 }  ( tons_value : URValue ( XInteger128 ) a1 ) ( out_pubkey : URValue ( XInteger256 ) a2 ) ( out_internal_owner : URValue ( address_t ) a3 ) ( my_tip3_addr : URValue ( address_t ) a4 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) burnWallet 
 tons_value out_pubkey out_internal_owner my_tip3_addr ) . 
 
 Notation " 'burnWallet_' '(' tons_value out_pubkey out_internal_owner my_tip3_addr ')' " := 
 ( burnWallet_left 
 tons_value out_pubkey out_internal_owner my_tip3_addr ) 
 (in custom ULValue at level 0 , tons_value custom URValue at level 0 
 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 ) : ursus_scope . 
 Definition getOwner_right  : URValue XInteger256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwner 
 ) . 
 
 Notation " 'getOwner_' '(' ')' " := 
 ( getOwner_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getFlex_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getFlex 
 ) . 
 
 Notation " 'getFlex_' '(' ')' " := 
 ( getFlex_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition hasExtWalletCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasExtWalletCode 
 ) . 
 
 Notation " 'hasExtWalletCode_' '(' ')' " := 
 ( hasExtWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition hasFlexWalletCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasFlexWalletCode 
 ) . 
 
 Notation " 'hasFlexWalletCode_' '(' ')' " := 
 ( hasFlexWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition hasFlexWrapperCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasFlexWrapperCode 
 ) . 
 
 Notation " 'hasFlexWrapperCode_' '(' ')' " := 
 ( hasFlexWrapperCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getPayloadForDeployInternalWallet_right { a1 a2 a3 }  ( owner_pubkey : URValue ( XInteger256 ) a1 ) ( owner_addr : URValue ( address_t ) a2 ) ( tons : URValue ( XInteger128 ) a3 ) : URValue XCell ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) getPayloadForDeployInternalWallet 
 owner_pubkey owner_addr tons ) . 
 
 Notation " 'getPayloadForDeployInternalWallet_' '(' owner_pubkey owner_addr tons ')' " := 
 ( getPayloadForDeployInternalWallet_right 
 owner_pubkey owner_addr tons ) 
 (in custom URValue at level 0 , owner_pubkey custom URValue at level 0 
 , owner_addr custom URValue at level 0 
 , tons custom URValue at level 0 ) : ursus_scope . 
 Definition _fallback_right { a1 a2 }  ( msg : URValue ( XCell ) a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue XInteger ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 msg msg_body ) . 
 
 Notation " '_fallback_' '(' msg msg_body ')' " := 
 ( _fallback_right 
 msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 
 Definition preparePrice_right { a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue ( XInteger128 ) a1 ) ( min_amount : URValue ( XInteger128 ) a2 ) ( deals_limit : URValue ( XInteger8 ) a3 ) ( tip3_code : URValue ( XCell ) a4 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a5 ) ( price_code : URValue ( XCell ) a6 ) ( notify_addr : URValue ( address_t ) a7 ) : URValue ( StateInitLRecord # XAddress # XInteger256 )%sol ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ):= 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) preparePrice 
 price min_amount deals_limit tip3_code tip3cfg price_code notify_addr ) . 
 
 Notation " 'preparePrice_' '(' price min_amount deals_limit tip3_code tip3cfg price_code notify_addr ')' " := 
 ( preparePrice_right 
 price min_amount deals_limit tip3_code tip3cfg price_code notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tip3_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , price_code custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition preparePriceXchg_right { a1 a2 a3 a4 a5 a6 a7 a8 }  ( price_num : URValue ( XInteger128 ) a1 ) ( price_denum : URValue ( XInteger128 ) a2 ) ( min_amount : URValue ( XInteger128 ) a3 ) ( deals_limit : URValue ( XInteger8 ) a4 ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) a5 ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) ( price_code : URValue ( XCell ) a7 ) ( notify_addr : URValue ( address_t ) a8 ) : URValue ( StateInitLRecord # XAddress # XInteger256 )%sol ( orb ( orb ( orb ( orb ( orb ( orb ( orb a8 a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ8 ) preparePriceXchg 
 price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ) . 
 
 Notation " 'preparePriceXchg_' '(' price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ')' " := 
 ( preparePriceXchg_right 
 price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ) 
 (in custom URValue at level 0 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 
 , price_code custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope .

End Calls. 

End FuncNotations.