Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 
Require Import Coq.Lists.List.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.StateMonad21. 
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.ProofEnvironment2.
Require Import UMLang.SML_NG25.

Require Import classFlex.

Require Import FLeXContractTypes.

Require Import specFlex.
Require Import FLeXConstSig. 


Module FLeXFuncNotations (xt: XTypesSig) 
                          (sm: StateMonadSig) 
                          (dc : FLeXConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

Module Export specFlexSpec := specFlexSpec xt sm.
Locate ursus_call_with_args.
Locate UrsusNotations.
Import ListNotations.
Import UrsusNotations.

Local Open Scope record. 
Local Open Scope solidity_scope. 
Local Open Scope ursus_scope. 
Local Open Scope string_scope.
Local Open Scope program_scope. 

(* Unset Typeclasses Iterative Deepening. 
Set Typeclasses Depth 100.  *)
Import ListNotations.

(* Notation " 'record1.A' " := ( ULState (U:=Record1) record1_ι_A ) (in custom ULValue at level 0) : ursus_scope. *)

Notation " 'TickTock.tick' " := ( ULState (U:= TickTock ) TickTock_ι_tick ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'TickTock.tock' " := ( ULState (U:= TickTock ) TickTock_ι_tock ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'allowance_info.spender' " := ( ULState (U:= allowance_info ) allowance_info_ι_spender ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( ULState (U:= allowance_info ) allowance_info_ι_remainingTokens ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'StateInit.split_depth' " := ( ULState (U:= StateInit ) StateInit_ι_split_depth ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'StateInit.special' " := ( ULState (U:= StateInit ) StateInit_ι_special ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'StateInit.code' " := ( ULState (U:= StateInit ) StateInit_ι_code ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'StateInit.data' " := ( ULState (U:= StateInit ) StateInit_ι_data ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'StateInit.library' " := ( ULState (U:= StateInit ) StateInit_ι_library ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'DTONTokenWallet.name_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_name_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.symbol_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_symbol_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.decimals_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_decimals_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.balance_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_balance_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.root_public_key_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_root_public_key_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.wallet_public_key_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_wallet_public_key_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.root_address_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_root_address_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.owner_address_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_owner_address_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.code_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_code_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.allowance_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_allowance_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.workchain_id_' " := ( ULState (U:= DTONTokenWallet ) DTONTokenWallet_ι_workchain_id_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'TonsConfig.transfer_tip3' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.order_answer' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.process_queue' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.send_notify' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'addr_std_fixed.workchain_id' " := ( ULState (U:= addr_std_fixed ) addr_std_fixed_ι_workchain_id ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'addr_std_fixed.address' " := ( ULState (U:= addr_std_fixed ) addr_std_fixed_ι_address ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'OrderInfo.original_amount' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_original_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.amount' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.account' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_account ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.tip3_wallet' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_tip3_wallet ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.client_addr' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_client_addr ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.order_finish_time' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_order_finish_time ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'OrderRet.err_code' " := ( ULState (U:= OrderRet ) OrderRet_ι_err_code ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderRet.processed' " := ( ULState (U:= OrderRet ) OrderRet_ι_processed ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderRet.enqueued' " := ( ULState (U:= OrderRet ) OrderRet_ι_enqueued ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'dealer.tip3root_' " := ( ULState (U:= dealer ) dealer_ι_tip3root_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'dealer.notify_addr_' " := ( ULState (U:= dealer ) dealer_ι_notify_addr_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'dealer.price_' " := ( ULState (U:= dealer ) dealer_ι_price_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'dealer.deals_limit_' " := ( ULState (U:= dealer ) dealer_ι_deals_limit_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'dealer.tons_cfg_' " := ( ULState (U:= dealer ) dealer_ι_tons_cfg_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'dealer.sells_amount_' " := ( ULState (U:= dealer ) dealer_ι_sells_amount_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'dealer.buys_amount_' " := ( ULState (U:= dealer ) dealer_ι_buys_amount_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'dealer.ret_' " := ( ULState (U:= dealer ) dealer_ι_ret_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'FLeXSellArgsAddrs.my_tip3_addr' " := ( ULState (U:= FLeXSellArgsAddrs ) FLeXSellArgsAddrs_ι_my_tip3_addr ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgsAddrs.receive_wallet' " := ( ULState (U:= FLeXSellArgsAddrs ) FLeXSellArgsAddrs_ι_receive_wallet ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'Tip3Config.name' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_name ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.symbol' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_symbol ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.decimals' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_decimals ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.root_public_key' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_root_public_key ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.root_address' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_root_address ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'FLeXSellArgs.price' " := ( ULState (U:= FLeXSellArgs ) FLeXSellArgs_ι_price ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.amount' " := ( ULState (U:= FLeXSellArgs ) FLeXSellArgs_ι_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.lend_finish_time' " := ( ULState (U:= FLeXSellArgs ) FLeXSellArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.min_amount' " := ( ULState (U:= FLeXSellArgs ) FLeXSellArgs_ι_min_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.deals_limit' " := ( ULState (U:= FLeXSellArgs ) FLeXSellArgs_ι_deals_limit ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.tons_value' " := ( ULState (U:= FLeXSellArgs ) FLeXSellArgs_ι_tons_value ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.price_code' " := ( ULState (U:= FLeXSellArgs ) FLeXSellArgs_ι_price_code ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.tip3_code' " := ( ULState (U:= FLeXSellArgs ) FLeXSellArgs_ι_tip3_code ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'FLeXBuyArgs.price' " := ( ULState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_price ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.amount' " := ( ULState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.order_finish_time' " := ( ULState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_order_finish_time ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.min_amount' " := ( ULState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_min_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.deals_limit' " := ( ULState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_deals_limit ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.deploy_value' " := ( ULState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_deploy_value ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.price_code' " := ( ULState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_price_code ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.my_tip3_addr' " := ( ULState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_my_tip3_addr ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.tip3_code' " := ( ULState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_tip3_code ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'FLeXXchgArgs.sell' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_sell ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.price_num' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_price_num ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.price_denum' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_price_denum ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.amount' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.lend_amount' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_lend_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.lend_finish_time' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.min_amount' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_min_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.deals_limit' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_deals_limit ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.tons_value' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_tons_value ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.xchg_price_code' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.tip3_code' " := ( ULState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_tip3_code ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'FLeXCancelArgs.price' " := ( ULState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_price ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.min_amount' " := ( ULState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.deals_limit' " := ( ULState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.value' " := ( ULState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_value ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.price_code' " := ( ULState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_price_code ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.tip3_code' " := ( ULState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'FLeXXchgCancelArgs.sell' " := ( ULState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_sell ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.price_num' " := ( ULState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_price_num ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.price_denum' " := ( ULState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_price_denum ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.min_amount' " := ( ULState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.deals_limit' " := ( ULState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.value' " := ( ULState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_value ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.xchg_price_code' " := ( ULState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.tip3_code' " := ( ULState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'FLeXClient.owner_' " := ( ULState (U:= FLeXClient ) FLeXClient_ι_owner_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.trading_pair_code_' " := ( ULState (U:= FLeXClient ) FLeXClient_ι_trading_pair_code_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.xchg_pair_code_' " := ( ULState (U:= FLeXClient ) FLeXClient_ι_xchg_pair_code_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.workchain_id_' " := ( ULState (U:= FLeXClient ) FLeXClient_ι_workchain_id_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.tons_cfg_' " := ( ULState (U:= FLeXClient ) FLeXClient_ι_tons_cfg_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.flex_' " := ( ULState (U:= FLeXClient ) FLeXClient_ι_flex_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.notify_addr_' " := ( ULState (U:= FLeXClient ) FLeXClient_ι_notify_addr_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'FLeX.deployer_pubkey_' " := ( ULState (U:= FLeX ) FLeX_ι_deployer_pubkey_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeX.tons_cfg_' " := ( ULState (U:= FLeX ) FLeX_ι_tons_cfg_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeX.pair_code_' " := ( ULState (U:= FLeX ) FLeX_ι_pair_code_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeX.xchg_pair_code_' " := ( ULState (U:= FLeX ) FLeX_ι_xchg_pair_code_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeX.price_code_' " := ( ULState (U:= FLeX ) FLeX_ι_price_code_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeX.xchg_price_code_' " := ( ULState (U:= FLeX ) FLeX_ι_xchg_price_code_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeX.min_amount_' " := ( ULState (U:= FLeX ) FLeX_ι_min_amount_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeX.deals_limit_' " := ( ULState (U:= FLeX ) FLeX_ι_deals_limit_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'FLeX.notify_addr_' " := ( ULState (U:= FLeX ) FLeX_ι_notify_addr_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'process_ret.sells_amount' " := ( ULState (U:= process_ret ) process_ret_ι_sells_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'process_ret.buys_amount' " := ( ULState (U:= process_ret ) process_ret_ι_buys_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'process_ret.ret_' " := ( ULState (U:= process_ret ) process_ret_ι_ret_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'SellArgs.amount' " := ( ULState (U:= SellArgs ) SellArgs_ι_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'SellArgs.receive_wallet' " := ( ULState (U:= SellArgs ) SellArgs_ι_receive_wallet ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'DetailsInfo.price' " := ( ULState (U:= DetailsInfo ) DetailsInfo_ι_price ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.min_amount' " := ( ULState (U:= DetailsInfo ) DetailsInfo_ι_min_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.sell_amount' " := ( ULState (U:= DetailsInfo ) DetailsInfo_ι_sell_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.buy_amount' " := ( ULState (U:= DetailsInfo ) DetailsInfo_ι_buy_amount ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'Price.price_' " := ( ULState (U:= Price ) Price_ι_price_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.sells_amount_' " := ( ULState (U:= Price ) Price_ι_sells_amount_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.buys_amount_' " := ( ULState (U:= Price ) Price_ι_buys_amount_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.flex_' " := ( ULState (U:= Price ) Price_ι_flex_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.min_amount_' " := ( ULState (U:= Price ) Price_ι_min_amount_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.deals_limit_' " := ( ULState (U:= Price ) Price_ι_deals_limit_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.notify_addr_' " := ( ULState (U:= Price ) Price_ι_notify_addr_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.workchain_id_' " := ( ULState (U:= Price ) Price_ι_workchain_id_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.tons_cfg_' " := ( ULState (U:= Price ) Price_ι_tons_cfg_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.tip3_code_' " := ( ULState (U:= Price ) Price_ι_tip3_code_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'Price.tip3cfg_' " := ( ULState (U:= Price ) Price_ι_tip3cfg_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'RationalPrice.num' " := ( ULState (U:= RationalPrice ) RationalPrice_ι_num ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'RationalPrice.denum' " := ( ULState (U:= RationalPrice ) RationalPrice_ι_denum ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'PayloadArgs.sell' " := ( ULState (U:= PayloadArgs ) PayloadArgs_ι_sell ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.amount' " := ( ULState (U:= PayloadArgs ) PayloadArgs_ι_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( ULState (U:= PayloadArgs ) PayloadArgs_ι_receive_tip3_wallet ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( ULState (U:= PayloadArgs ) PayloadArgs_ι_client_addr ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'OrderInfoXchg.original_amount' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_original_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.amount' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.account' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_account ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_provide ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_receive ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.client_addr' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_client_addr ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.order_finish_time' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_order_finish_time ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'DetailsInfoXchg.price_num' " := ( ULState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_price_num ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.price_denum' " := ( ULState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_price_denum ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.min_amount' " := ( ULState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_min_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.sell_amount' " := ( ULState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_sell_amount ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.buy_amount' " := ( ULState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_buy_amount ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'PriceXchg.price_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_price_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.sells_amount_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_sells_amount_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.buys_amount_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_buys_amount_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.flex_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_flex_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.min_amount_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_min_amount_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.deals_limit_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_deals_limit_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.notify_addr_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_notify_addr_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.workchain_id_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_workchain_id_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.tons_cfg_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_tons_cfg_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.tip3_code_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_tip3_code_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.major_tip3cfg_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_major_tip3cfg_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_minor_tip3cfg_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'DTradingPair.flex_addr_' " := ( ULState (U:= DTradingPair ) DTradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTradingPair.tip3_root_' " := ( ULState (U:= DTradingPair ) DTradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DTradingPair.deploy_value_' " := ( ULState (U:= DTradingPair ) DTradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'DXchgPair.flex_addr_' " := ( ULState (U:= DXchgPair ) DXchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.tip3_major_root_' " := ( ULState (U:= DXchgPair ) DXchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.tip3_minor_root_' " := ( ULState (U:= DXchgPair ) DXchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.deploy_value_' " := ( ULState (U:= DXchgPair ) DXchgPair_ι_deploy_value_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'LocalState.uint256' " := ( ULState (U:= LocalState ) LocalState_ι_uint256 ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.cell' " := ( ULState (U:= LocalState ) LocalState_ι_cell ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.TonsConfig' " := ( ULState (U:= LocalState ) LocalState_ι_TonsConfig ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.address' " := ( ULState (U:= LocalState ) LocalState_ι_address ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint128' " := ( ULState (U:= LocalState ) LocalState_ι_uint128 ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.StateInit' " := ( ULState (U:= LocalState ) LocalState_ι_StateInit ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.DTradingPair' " := ( ULState (U:= LocalState ) LocalState_ι_DTradingPair ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITradingPair_' " := ( ULState (U:= LocalState ) LocalState_ι_handle_ITradingPair_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.DXchgPair' " := ( ULState (U:= LocalState ) LocalState_ι_DXchgPair ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IXchgPair_' " := ( ULState (U:= LocalState ) LocalState_ι_handle_IXchgPair_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXSellArgs_' " := ( ULState (U:= LocalState ) LocalState_ι_parse_FLeXSellArgs_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPrice_' " := ( ULState (U:= LocalState ) LocalState_ι_handle_IPrice_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.SellArgs' " := ( ULState (U:= LocalState ) LocalState_ι_SellArgs ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXBuyArgs_' " := ( ULState (U:= LocalState ) LocalState_ι_parse_FLeXBuyArgs_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXCancelArgs_' " := ( ULState (U:= LocalState ) LocalState_ι_parse_FLeXCancelArgs_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgCancelArgs_' " := ( ULState (U:= LocalState ) LocalState_ι_parse_FLeXXchgCancelArgs_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPriceXchg_' " := ( ULState (U:= LocalState ) LocalState_ι_handle_IPriceXchg_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool_t' " := ( ULState (U:= LocalState ) LocalState_ι_bool_t ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgArgs_' " := ( ULState (U:= LocalState ) LocalState_ι_parse_FLeXXchgArgs_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.PayloadArgs' " := ( ULState (U:= LocalState ) LocalState_ι_PayloadArgs ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITONTokenWallet_' " := ( ULState (U:= LocalState ) LocalState_ι_handle_ITONTokenWallet_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint8' " := ( ULState (U:= LocalState ) LocalState_ι_uint8 ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.Tip3Config' " := ( ULState (U:= LocalState ) LocalState_ι_Tip3Config ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPrice' " := ( ULState (U:= LocalState ) LocalState_ι_DPrice ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceXchg' " := ( ULState (U:= LocalState ) LocalState_ι_DPriceXchg ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.tuple_address_address' " := ( ULState (U:= LocalState ) LocalState_ι_tuple_address_address ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint32' " := ( ULState (U:= LocalState ) LocalState_ι_uint32 ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.unsigned' " := ( ULState (U:= LocalState ) LocalState_ι_unsigned ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.OrderInfo' " := ( ULState (U:= LocalState ) LocalState_ι_OrderInfo ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.int' " := ( ULState (U:= LocalState ) LocalState_ι_int ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_uint128_' " := ( ULState (U:= LocalState ) LocalState_ι_optional_uint128_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool' " := ( ULState (U:= LocalState ) LocalState_ι_bool ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_OrderInfoWithIdx_' " := ( ULState (U:= LocalState ) LocalState_ι_optional_OrderInfoWithIdx_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.queue_OrderInfo_' " := ( ULState (U:= LocalState ) LocalState_ι_queue_OrderInfo_ ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.pair_unsigned_OrderInfo_' " := ( ULState (U:= LocalState ) LocalState_ι_pair_unsigned_OrderInfo_ ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'TickTock.tick' " := ( URState (U:= TickTock ) TickTock_ι_tick ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'TickTock.tock' " := ( URState (U:= TickTock ) TickTock_ι_tock ) (in custom URValue at level 0) : sml_scope. 

Notation " 'allowance_info.spender' " := ( URState (U:= allowance_info ) allowance_info_ι_spender ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( URState (U:= allowance_info ) allowance_info_ι_remainingTokens ) (in custom URValue at level 0) : sml_scope. 

Notation " 'StateInit.split_depth' " := ( URState (U:= StateInit ) StateInit_ι_split_depth ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'StateInit.special' " := ( URState (U:= StateInit ) StateInit_ι_special ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'StateInit.code' " := ( URState (U:= StateInit ) StateInit_ι_code ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'StateInit.data' " := ( URState (U:= StateInit ) StateInit_ι_data ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'StateInit.library' " := ( URState (U:= StateInit ) StateInit_ι_library ) (in custom URValue at level 0) : sml_scope. 

Notation " 'DTONTokenWallet.name_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_name_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.symbol_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_symbol_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.decimals_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_decimals_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.balance_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_balance_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.root_public_key_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_root_public_key_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.wallet_public_key_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_wallet_public_key_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.root_address_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_root_address_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.owner_address_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_owner_address_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.code_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_code_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.allowance_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_allowance_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.workchain_id_' " := ( URState (U:= DTONTokenWallet ) DTONTokenWallet_ι_workchain_id_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'TonsConfig.transfer_tip3' " := ( URState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( URState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( URState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.order_answer' " := ( URState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.process_queue' " := ( URState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.send_notify' " := ( URState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom URValue at level 0) : sml_scope. 

Notation " 'addr_std_fixed.workchain_id' " := ( URState (U:= addr_std_fixed ) addr_std_fixed_ι_workchain_id ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'addr_std_fixed.address' " := ( URState (U:= addr_std_fixed ) addr_std_fixed_ι_address ) (in custom URValue at level 0) : sml_scope. 

Notation " 'OrderInfo.original_amount' " := ( URState (U:= OrderInfo ) OrderInfo_ι_original_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.amount' " := ( URState (U:= OrderInfo ) OrderInfo_ι_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.account' " := ( URState (U:= OrderInfo ) OrderInfo_ι_account ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.tip3_wallet' " := ( URState (U:= OrderInfo ) OrderInfo_ι_tip3_wallet ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.client_addr' " := ( URState (U:= OrderInfo ) OrderInfo_ι_client_addr ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.order_finish_time' " := ( URState (U:= OrderInfo ) OrderInfo_ι_order_finish_time ) (in custom URValue at level 0) : sml_scope. 

Notation " 'OrderRet.err_code' " := ( URState (U:= OrderRet ) OrderRet_ι_err_code ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderRet.processed' " := ( URState (U:= OrderRet ) OrderRet_ι_processed ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderRet.enqueued' " := ( URState (U:= OrderRet ) OrderRet_ι_enqueued ) (in custom URValue at level 0) : sml_scope. 

Notation " 'dealer.tip3root_' " := ( URState (U:= dealer ) dealer_ι_tip3root_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'dealer.notify_addr_' " := ( URState (U:= dealer ) dealer_ι_notify_addr_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'dealer.price_' " := ( URState (U:= dealer ) dealer_ι_price_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'dealer.deals_limit_' " := ( URState (U:= dealer ) dealer_ι_deals_limit_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'dealer.tons_cfg_' " := ( URState (U:= dealer ) dealer_ι_tons_cfg_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'dealer.sells_amount_' " := ( URState (U:= dealer ) dealer_ι_sells_amount_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'dealer.buys_amount_' " := ( URState (U:= dealer ) dealer_ι_buys_amount_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'dealer.ret_' " := ( URState (U:= dealer ) dealer_ι_ret_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'FLeXSellArgsAddrs.my_tip3_addr' " := ( URState (U:= FLeXSellArgsAddrs ) FLeXSellArgsAddrs_ι_my_tip3_addr ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgsAddrs.receive_wallet' " := ( URState (U:= FLeXSellArgsAddrs ) FLeXSellArgsAddrs_ι_receive_wallet ) (in custom URValue at level 0) : sml_scope. 

Notation " 'Tip3Config.name' " := ( URState (U:= Tip3Config ) Tip3Config_ι_name ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.symbol' " := ( URState (U:= Tip3Config ) Tip3Config_ι_symbol ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.decimals' " := ( URState (U:= Tip3Config ) Tip3Config_ι_decimals ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.root_public_key' " := ( URState (U:= Tip3Config ) Tip3Config_ι_root_public_key ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.root_address' " := ( URState (U:= Tip3Config ) Tip3Config_ι_root_address ) (in custom URValue at level 0) : sml_scope. 

Notation " 'FLeXSellArgs.price' " := ( URState (U:= FLeXSellArgs ) FLeXSellArgs_ι_price ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.amount' " := ( URState (U:= FLeXSellArgs ) FLeXSellArgs_ι_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.lend_finish_time' " := ( URState (U:= FLeXSellArgs ) FLeXSellArgs_ι_lend_finish_time ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.min_amount' " := ( URState (U:= FLeXSellArgs ) FLeXSellArgs_ι_min_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.deals_limit' " := ( URState (U:= FLeXSellArgs ) FLeXSellArgs_ι_deals_limit ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.tons_value' " := ( URState (U:= FLeXSellArgs ) FLeXSellArgs_ι_tons_value ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.price_code' " := ( URState (U:= FLeXSellArgs ) FLeXSellArgs_ι_price_code ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.tip3_code' " := ( URState (U:= FLeXSellArgs ) FLeXSellArgs_ι_tip3_code ) (in custom URValue at level 0) : sml_scope. 

Notation " 'FLeXBuyArgs.price' " := ( URState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_price ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.amount' " := ( URState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.order_finish_time' " := ( URState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_order_finish_time ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.min_amount' " := ( URState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_min_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.deals_limit' " := ( URState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_deals_limit ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.deploy_value' " := ( URState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_deploy_value ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.price_code' " := ( URState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_price_code ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.my_tip3_addr' " := ( URState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_my_tip3_addr ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.tip3_code' " := ( URState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_tip3_code ) (in custom URValue at level 0) : sml_scope. 

Notation " 'FLeXXchgArgs.sell' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_sell ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.price_num' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_price_num ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.price_denum' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_price_denum ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.amount' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.lend_amount' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_lend_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.lend_finish_time' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_lend_finish_time ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.min_amount' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_min_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.deals_limit' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_deals_limit ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.tons_value' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_tons_value ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.xchg_price_code' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_xchg_price_code ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.tip3_code' " := ( URState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_tip3_code ) (in custom URValue at level 0) : sml_scope. 

Notation " 'FLeXCancelArgs.price' " := ( URState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_price ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.min_amount' " := ( URState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_min_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.deals_limit' " := ( URState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.value' " := ( URState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_value ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.price_code' " := ( URState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_price_code ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.tip3_code' " := ( URState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : sml_scope. 

Notation " 'FLeXXchgCancelArgs.sell' " := ( URState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_sell ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.price_num' " := ( URState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_price_num ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.price_denum' " := ( URState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_price_denum ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.min_amount' " := ( URState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_min_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.deals_limit' " := ( URState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.value' " := ( URState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_value ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.xchg_price_code' " := ( URState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_xchg_price_code ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.tip3_code' " := ( URState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : sml_scope. 

Notation " 'FLeXClient.owner_' " := ( URState (U:= FLeXClient ) FLeXClient_ι_owner_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.trading_pair_code_' " := ( URState (U:= FLeXClient ) FLeXClient_ι_trading_pair_code_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.xchg_pair_code_' " := ( URState (U:= FLeXClient ) FLeXClient_ι_xchg_pair_code_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.workchain_id_' " := ( URState (U:= FLeXClient ) FLeXClient_ι_workchain_id_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.tons_cfg_' " := ( URState (U:= FLeXClient ) FLeXClient_ι_tons_cfg_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.flex_' " := ( URState (U:= FLeXClient ) FLeXClient_ι_flex_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.notify_addr_' " := ( URState (U:= FLeXClient ) FLeXClient_ι_notify_addr_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'FLeX.deployer_pubkey_' " := ( URState (U:= FLeX ) FLeX_ι_deployer_pubkey_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeX.tons_cfg_' " := ( URState (U:= FLeX ) FLeX_ι_tons_cfg_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeX.pair_code_' " := ( URState (U:= FLeX ) FLeX_ι_pair_code_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeX.xchg_pair_code_' " := ( URState (U:= FLeX ) FLeX_ι_xchg_pair_code_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeX.price_code_' " := ( URState (U:= FLeX ) FLeX_ι_price_code_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeX.xchg_price_code_' " := ( URState (U:= FLeX ) FLeX_ι_xchg_price_code_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeX.min_amount_' " := ( URState (U:= FLeX ) FLeX_ι_min_amount_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeX.deals_limit_' " := ( URState (U:= FLeX ) FLeX_ι_deals_limit_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'FLeX.notify_addr_' " := ( URState (U:= FLeX ) FLeX_ι_notify_addr_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'process_ret.sells_amount' " := ( URState (U:= process_ret ) process_ret_ι_sells_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'process_ret.buys_amount' " := ( URState (U:= process_ret ) process_ret_ι_buys_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'process_ret.ret_' " := ( URState (U:= process_ret ) process_ret_ι_ret_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'SellArgs.amount' " := ( URState (U:= SellArgs ) SellArgs_ι_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'SellArgs.receive_wallet' " := ( URState (U:= SellArgs ) SellArgs_ι_receive_wallet ) (in custom URValue at level 0) : sml_scope. 

Notation " 'DetailsInfo.price' " := ( URState (U:= DetailsInfo ) DetailsInfo_ι_price ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.min_amount' " := ( URState (U:= DetailsInfo ) DetailsInfo_ι_min_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.sell_amount' " := ( URState (U:= DetailsInfo ) DetailsInfo_ι_sell_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.buy_amount' " := ( URState (U:= DetailsInfo ) DetailsInfo_ι_buy_amount ) (in custom URValue at level 0) : sml_scope. 

Notation " 'Price.price_' " := ( URState (U:= Price ) Price_ι_price_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.sells_amount_' " := ( URState (U:= Price ) Price_ι_sells_amount_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.buys_amount_' " := ( URState (U:= Price ) Price_ι_buys_amount_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.flex_' " := ( URState (U:= Price ) Price_ι_flex_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.min_amount_' " := ( URState (U:= Price ) Price_ι_min_amount_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.deals_limit_' " := ( URState (U:= Price ) Price_ι_deals_limit_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.notify_addr_' " := ( URState (U:= Price ) Price_ι_notify_addr_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.workchain_id_' " := ( URState (U:= Price ) Price_ι_workchain_id_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.tons_cfg_' " := ( URState (U:= Price ) Price_ι_tons_cfg_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.tip3_code_' " := ( URState (U:= Price ) Price_ι_tip3_code_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'Price.tip3cfg_' " := ( URState (U:= Price ) Price_ι_tip3cfg_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'RationalPrice.num' " := ( URState (U:= RationalPrice ) RationalPrice_ι_num ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'RationalPrice.denum' " := ( URState (U:= RationalPrice ) RationalPrice_ι_denum ) (in custom URValue at level 0) : sml_scope. 

Notation " 'PayloadArgs.sell' " := ( URState (U:= PayloadArgs ) PayloadArgs_ι_sell ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.amount' " := ( URState (U:= PayloadArgs ) PayloadArgs_ι_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( URState (U:= PayloadArgs ) PayloadArgs_ι_receive_tip3_wallet ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( URState (U:= PayloadArgs ) PayloadArgs_ι_client_addr ) (in custom URValue at level 0) : sml_scope. 

Notation " 'OrderInfoXchg.original_amount' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_original_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.amount' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.account' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_account ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_provide ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_receive ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.client_addr' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_client_addr ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.order_finish_time' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_order_finish_time ) (in custom URValue at level 0) : sml_scope. 

Notation " 'DetailsInfoXchg.price_num' " := ( URState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_price_num ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.price_denum' " := ( URState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_price_denum ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.min_amount' " := ( URState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_min_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.sell_amount' " := ( URState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_sell_amount ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.buy_amount' " := ( URState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_buy_amount ) (in custom URValue at level 0) : sml_scope. 

Notation " 'PriceXchg.price_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_price_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.sells_amount_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_sells_amount_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.buys_amount_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_buys_amount_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.flex_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_flex_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.min_amount_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_min_amount_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.deals_limit_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_deals_limit_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.notify_addr_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_notify_addr_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.workchain_id_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_workchain_id_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.tons_cfg_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_tons_cfg_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.tip3_code_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_tip3_code_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.major_tip3cfg_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_major_tip3cfg_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_minor_tip3cfg_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'DTradingPair.flex_addr_' " := ( URState (U:= DTradingPair ) DTradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTradingPair.tip3_root_' " := ( URState (U:= DTradingPair ) DTradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DTradingPair.deploy_value_' " := ( URState (U:= DTradingPair ) DTradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'DXchgPair.flex_addr_' " := ( URState (U:= DXchgPair ) DXchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.tip3_major_root_' " := ( URState (U:= DXchgPair ) DXchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.tip3_minor_root_' " := ( URState (U:= DXchgPair ) DXchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.deploy_value_' " := ( URState (U:= DXchgPair ) DXchgPair_ι_deploy_value_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'LocalState.uint256' " := ( URState (U:= LocalState ) LocalState_ι_uint256 ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.cell' " := ( URState (U:= LocalState ) LocalState_ι_cell ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.TonsConfig' " := ( URState (U:= LocalState ) LocalState_ι_TonsConfig ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.address' " := ( URState (U:= LocalState ) LocalState_ι_address ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint128' " := ( URState (U:= LocalState ) LocalState_ι_uint128 ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.StateInit' " := ( URState (U:= LocalState ) LocalState_ι_StateInit ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.DTradingPair' " := ( URState (U:= LocalState ) LocalState_ι_DTradingPair ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITradingPair_' " := ( URState (U:= LocalState ) LocalState_ι_handle_ITradingPair_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.DXchgPair' " := ( URState (U:= LocalState ) LocalState_ι_DXchgPair ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IXchgPair_' " := ( URState (U:= LocalState ) LocalState_ι_handle_IXchgPair_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXSellArgs_' " := ( URState (U:= LocalState ) LocalState_ι_parse_FLeXSellArgs_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPrice_' " := ( URState (U:= LocalState ) LocalState_ι_handle_IPrice_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.SellArgs' " := ( URState (U:= LocalState ) LocalState_ι_SellArgs ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXBuyArgs_' " := ( URState (U:= LocalState ) LocalState_ι_parse_FLeXBuyArgs_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXCancelArgs_' " := ( URState (U:= LocalState ) LocalState_ι_parse_FLeXCancelArgs_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgCancelArgs_' " := ( URState (U:= LocalState ) LocalState_ι_parse_FLeXXchgCancelArgs_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPriceXchg_' " := ( URState (U:= LocalState ) LocalState_ι_handle_IPriceXchg_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool_t' " := ( URState (U:= LocalState ) LocalState_ι_bool_t ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgArgs_' " := ( URState (U:= LocalState ) LocalState_ι_parse_FLeXXchgArgs_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.PayloadArgs' " := ( URState (U:= LocalState ) LocalState_ι_PayloadArgs ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITONTokenWallet_' " := ( URState (U:= LocalState ) LocalState_ι_handle_ITONTokenWallet_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint8' " := ( URState (U:= LocalState ) LocalState_ι_uint8 ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.Tip3Config' " := ( URState (U:= LocalState ) LocalState_ι_Tip3Config ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPrice' " := ( URState (U:= LocalState ) LocalState_ι_DPrice ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceXchg' " := ( URState (U:= LocalState ) LocalState_ι_DPriceXchg ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.tuple_address_address' " := ( URState (U:= LocalState ) LocalState_ι_tuple_address_address ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint32' " := ( URState (U:= LocalState ) LocalState_ι_uint32 ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.unsigned' " := ( URState (U:= LocalState ) LocalState_ι_unsigned ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.OrderInfo' " := ( URState (U:= LocalState ) LocalState_ι_OrderInfo ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.int' " := ( URState (U:= LocalState ) LocalState_ι_int ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_uint128_' " := ( URState (U:= LocalState ) LocalState_ι_optional_uint128_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool' " := ( URState (U:= LocalState ) LocalState_ι_bool ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_OrderInfoWithIdx_' " := ( URState (U:= LocalState ) LocalState_ι_optional_OrderInfoWithIdx_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.queue_OrderInfo_' " := ( URState (U:= LocalState ) LocalState_ι_queue_OrderInfo_ ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.pair_unsigned_OrderInfo_' " := ( URState (U:= LocalState ) LocalState_ι_pair_unsigned_OrderInfo_ ) (in custom URValue at level 0) : sml_scope. 

Notation " 'LocalState.uint256Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint256Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.cellIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_cellIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.TonsConfigIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_TonsConfigIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.addressIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_addressIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint128Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint128Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.StateInitIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_StateInitIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.DTradingPairIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DTradingPairIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITradingPair_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_ITradingPair_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.DXchgPairIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DXchgPairIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IXchgPair_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IXchgPair_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXSellArgs_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXSellArgs_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPrice_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IPrice_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.SellArgsIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_SellArgsIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXBuyArgs_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXBuyArgs_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXCancelArgs_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXCancelArgs_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgCancelArgs_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXXchgCancelArgs_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPriceXchg_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IPriceXchg_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool_tIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_bool_tIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgArgs_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXXchgArgs_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.PayloadArgsIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_PayloadArgsIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITONTokenWallet_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_ITONTokenWallet_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint8Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint8Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.Tip3ConfigIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_Tip3ConfigIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DPriceIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceXchgIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DPriceXchgIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.tuple_address_addressIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_tuple_address_addressIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint32Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint32Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.unsignedIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_unsignedIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.OrderInfoIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_OrderInfoIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.intIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_intIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_uint128_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_optional_uint128_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.boolIndex' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_boolIndex ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_OrderInfoWithIdx_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_optional_OrderInfoWithIdx_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.queue_OrderInfo_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_queue_OrderInfo_Index ) (in custom ULValue at level 0) : sml_scope. 
 Notation " 'LocalState.pair_unsigned_OrderInfo_Index' " := ( ULState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_pair_unsigned_OrderInfo_Index ) (in custom ULValue at level 0) : sml_scope. 

Notation " 'LocalState.uint256Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint256Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.cellIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_cellIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.TonsConfigIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_TonsConfigIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.addressIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_addressIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint128Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint128Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.StateInitIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_StateInitIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.DTradingPairIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DTradingPairIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITradingPair_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_ITradingPair_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.DXchgPairIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DXchgPairIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IXchgPair_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IXchgPair_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXSellArgs_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXSellArgs_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPrice_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IPrice_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.SellArgsIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_SellArgsIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXBuyArgs_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXBuyArgs_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXCancelArgs_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXCancelArgs_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgCancelArgs_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXXchgCancelArgs_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPriceXchg_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IPriceXchg_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool_tIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_bool_tIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgArgs_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXXchgArgs_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.PayloadArgsIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_PayloadArgsIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITONTokenWallet_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_ITONTokenWallet_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint8Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint8Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.Tip3ConfigIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_Tip3ConfigIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DPriceIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceXchgIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DPriceXchgIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.tuple_address_addressIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_tuple_address_addressIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint32Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint32Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.unsignedIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_unsignedIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.OrderInfoIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_OrderInfoIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.intIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_intIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_uint128_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_optional_uint128_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.boolIndex' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_boolIndex ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_OrderInfoWithIdx_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_optional_OrderInfoWithIdx_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.queue_OrderInfo_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_queue_OrderInfo_Index ) (in custom URValue at level 0) : sml_scope. 
 Notation " 'LocalState.pair_unsigned_OrderInfo_Index' " := ( URState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_pair_unsigned_OrderInfo_Index ) (in custom URValue at level 0) : sml_scope. 

Notation " 'TIMESTAMP_DELAY' " := (sInject TIMESTAMP_DELAY) (in custom URValue at level 0) : sml_scope.
Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_message_sender_is_not_my_owner) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::sender_is_not_deployer' " := (sInject error_code_ι_sender_is_not_deployer) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::unexpected_refs_count_in_code' " := (sInject error_code_ι_unexpected_refs_count_in_code) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::cant_override_code' " := (sInject error_code_ι_cant_override_code) (in custom URValue at level 0) : sml_scope. 

Notation " 'ok' " := (sInject ok) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::out_of_tons' " := (sInject error_code_ι_out_of_tons) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::deals_limit' " := (sInject error_code_ι_deals_limit) (in custom URValue at level 0) : sml_scope.
Notation " 'error_code::not_enough_tons_to_process' " := (sInject error_code_ι_not_enough_tons_to_process) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::not_enough_tokens_amount' " := (sInject error_code_ι_not_enough_tokens_amount) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::too_big_tokens_amount' " := (sInject error_code_ι_too_big_tokens_amount) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::different_workchain_id' " := (sInject error_code_ι_different_workchain_id) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::unverified_tip3_wallet' " := (sInject error_code_ι_unverified_tip3_wallet) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::canceled' " := (sInject error_code_ι_canceled) (in custom URValue at level 0) : sml_scope. 
Notation " 'error_code::expired' " := (sInject error_code_ι_expired) (in custom URValue at level 0) : sml_scope. 
Notation " 'safe_delay_period' " := (sInject safe_delay_period) (in custom URValue at level 0) : sml_scope. 

Notation " 'error_code::not_enough_tons' " := (sInject error_code_ι_not_enough_tons) (in custom URValue at level 0) : sml_scope. 

(**************************************************************************************************)

Module FuncEx (tc : specFLeXSig).
Import UrsusNotations.
Local Open Scope ursus_scope.
Import tc.
Require Import String.
Local Open Scope string_scope.

(* Definition bar33_call (x y: URValue XBool false)  := 
   🏓 sml_call_with_args (LedgerableWithArgs := λ2) bar33 
(SimpleLedgerableArg URValue {{ Λ "b0" }} x) (SimpleLedgerableArg URValue {{ Λ "b1" }} y) .


Notation " 'bar33_' '(' x , y ')' " := ( ULRResult (bar33_call x y))  
   (in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : sml_scope.

Notation " 'bar33_' '(' x , y ')' " := ( FuncallExpression (bar33_call x y))  
   (in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : sml_scope.
 *) (*Здесь будут сгенерена последовательность параметров внутри модуля тайпа. Появится новый модуль который будет параметризован 
этим модулетайпом (можно и в этом же файле). Появится абстрактный инстанс этого модулетайпа импорт икс и вот эти все параметры поя
вятся в контексте. Тогда для них мы сможем написать определения . Тогда подключив новый модуль можно писать 
какую-то формулировку. Тогда в новом модуле Роберт сможет сформулировать спецификацию функций, считая то они есть
А потом мы сделаем модуль с самими функциями. *)
 
End FuncEx. 
End FLeXFuncNotations.
