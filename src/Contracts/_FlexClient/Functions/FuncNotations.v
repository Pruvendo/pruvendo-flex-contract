
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
 
 Definition flex__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : ULValue addr_std_compactLRecord ) . 
 Definition flex__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : URValue addr_std_compactLRecord false ) . 
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
 Notation " 'XchgPair.deploy_value_' " := ( XchgPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.deploy_value_' " := ( XchgPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 
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
 Notation " 'Price.price_' " := ( Price_ι_price_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.price_' " := ( Price_ι_price_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.sells_amount_' " := ( Price_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.sells_amount_' " := ( Price_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.buys_amount_' " := ( Price_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.buys_amount_' " := ( Price_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.flex_' " := ( Price_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.flex_' " := ( Price_ι_flex_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.min_amount_' " := ( Price_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.min_amount_' " := ( Price_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.deals_limit_' " := ( Price_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.deals_limit_' " := ( Price_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.notify_addr_' " := ( Price_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.notify_addr_' " := ( Price_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.workchain_id_' " := ( Price_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.workchain_id_' " := ( Price_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.tons_cfg_' " := ( Price_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.tons_cfg_' " := ( Price_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.tip3_code_' " := ( Price_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.tip3_code_' " := ( Price_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.tip3cfg_' " := ( Price_ι_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.tip3cfg_' " := ( Price_ι_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.sells_' " := ( Price_ι_sells_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.sells_' " := ( Price_ι_sells_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Price.buys_' " := ( Price_ι_buys_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Price.buys_' " := ( Price_ι_buys_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.num' " := ( RationalPrice_ι_num ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.num' " := ( RationalPrice_ι_num ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.denum' " := ( RationalPrice_ι_denum ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.denum' " := ( RationalPrice_ι_denum ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.price_' " := ( PriceXchg_ι_price_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.price_' " := ( PriceXchg_ι_price_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.sells_amount_' " := ( PriceXchg_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.sells_amount_' " := ( PriceXchg_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.buys_amount_' " := ( PriceXchg_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.buys_amount_' " := ( PriceXchg_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.flex_' " := ( PriceXchg_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.flex_' " := ( PriceXchg_ι_flex_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.min_amount_' " := ( PriceXchg_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.min_amount_' " := ( PriceXchg_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.deals_limit_' " := ( PriceXchg_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.deals_limit_' " := ( PriceXchg_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.notify_addr_' " := ( PriceXchg_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.notify_addr_' " := ( PriceXchg_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.workchain_id_' " := ( PriceXchg_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.workchain_id_' " := ( PriceXchg_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.tons_cfg_' " := ( PriceXchg_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.tons_cfg_' " := ( PriceXchg_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.tip3_code_' " := ( PriceXchg_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.tip3_code_' " := ( PriceXchg_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.major_tip3cfg_' " := ( PriceXchg_ι_major_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.major_tip3cfg_' " := ( PriceXchg_ι_major_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( PriceXchg_ι_minor_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( PriceXchg_ι_minor_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.flex_addr_' " := ( TradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.flex_addr_' " := ( TradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( TradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( TradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( TradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( TradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.sell' " := ( PayloadArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.sell' " := ( PayloadArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.amount' " := ( PayloadArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.amount' " := ( PayloadArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_ι_receive_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_ι_receive_tip3_wallet ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( PayloadArgs_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( PayloadArgs_ι_client_addr ) (in custom URValue at level 0) : ursus_scope. 
 

Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 

Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.


End Calls. 

End FuncNotations.
