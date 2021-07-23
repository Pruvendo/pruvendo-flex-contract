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
Local Open Scope record. 
Local Open Scope solidity_scope. 
Local Open Scope sml_scope. 
Local Open Scope string_scope.
Local Open Scope program_scope. 

(* Unset Typeclasses Iterative Deepening. 
Set Typeclasses Depth 100.  *)
Import ListNotations.
Import SMLNotations.

Notation " 'TickTock.tick' " := ( SMLLState (U:= TickTock ) TickTock_ι_tick ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'TickTock.tock' " := ( SMLLState (U:= TickTock ) TickTock_ι_tock ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'allowance_info.spender' " := ( SMLLState (U:= allowance_info ) allowance_info_ι_spender ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( SMLLState (U:= allowance_info ) allowance_info_ι_remainingTokens ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'StateInit.split_depth' " := ( SMLLState (U:= StateInit ) StateInit_ι_split_depth ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'StateInit.special' " := ( SMLLState (U:= StateInit ) StateInit_ι_special ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'StateInit.code' " := ( SMLLState (U:= StateInit ) StateInit_ι_code ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'StateInit.data' " := ( SMLLState (U:= StateInit ) StateInit_ι_data ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'StateInit.library' " := ( SMLLState (U:= StateInit ) StateInit_ι_library ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'DTONTokenWallet.name_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_name_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.symbol_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_symbol_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.decimals_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_decimals_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.balance_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_balance_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.root_public_key_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_root_public_key_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.wallet_public_key_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_wallet_public_key_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.root_address_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_root_address_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.owner_address_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_owner_address_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.code_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_code_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.allowance_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_allowance_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.workchain_id_' " := ( SMLLState (U:= DTONTokenWallet ) DTONTokenWallet_ι_workchain_id_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'TonsConfig.transfer_tip3' " := ( SMLLState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( SMLLState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( SMLLState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.order_answer' " := ( SMLLState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.process_queue' " := ( SMLLState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.send_notify' " := ( SMLLState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'addr_std_fixed.workchain_id' " := ( SMLLState (U:= addr_std_fixed ) addr_std_fixed_ι_workchain_id ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'addr_std_fixed.address' " := ( SMLLState (U:= addr_std_fixed ) addr_std_fixed_ι_address ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'OrderInfo.original_amount' " := ( SMLLState (U:= OrderInfo ) OrderInfo_ι_original_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.amount' " := ( SMLLState (U:= OrderInfo ) OrderInfo_ι_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.account' " := ( SMLLState (U:= OrderInfo ) OrderInfo_ι_account ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.tip3_wallet' " := ( SMLLState (U:= OrderInfo ) OrderInfo_ι_tip3_wallet ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.client_addr' " := ( SMLLState (U:= OrderInfo ) OrderInfo_ι_client_addr ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.order_finish_time' " := ( SMLLState (U:= OrderInfo ) OrderInfo_ι_order_finish_time ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'OrderRet.err_code' " := ( SMLLState (U:= OrderRet ) OrderRet_ι_err_code ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderRet.processed' " := ( SMLLState (U:= OrderRet ) OrderRet_ι_processed ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderRet.enqueued' " := ( SMLLState (U:= OrderRet ) OrderRet_ι_enqueued ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'dealer.tip3root_' " := ( SMLLState (U:= dealer ) dealer_ι_tip3root_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'dealer.notify_addr_' " := ( SMLLState (U:= dealer ) dealer_ι_notify_addr_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'dealer.price_' " := ( SMLLState (U:= dealer ) dealer_ι_price_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'dealer.deals_limit_' " := ( SMLLState (U:= dealer ) dealer_ι_deals_limit_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'dealer.tons_cfg_' " := ( SMLLState (U:= dealer ) dealer_ι_tons_cfg_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'dealer.sells_amount_' " := ( SMLLState (U:= dealer ) dealer_ι_sells_amount_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'dealer.buys_amount_' " := ( SMLLState (U:= dealer ) dealer_ι_buys_amount_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'dealer.ret_' " := ( SMLLState (U:= dealer ) dealer_ι_ret_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'FLeXSellArgsAddrs.my_tip3_addr' " := ( SMLLState (U:= FLeXSellArgsAddrs ) FLeXSellArgsAddrs_ι_my_tip3_addr ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgsAddrs.receive_wallet' " := ( SMLLState (U:= FLeXSellArgsAddrs ) FLeXSellArgsAddrs_ι_receive_wallet ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'Tip3Config.name' " := ( SMLLState (U:= Tip3Config ) Tip3Config_ι_name ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.symbol' " := ( SMLLState (U:= Tip3Config ) Tip3Config_ι_symbol ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.decimals' " := ( SMLLState (U:= Tip3Config ) Tip3Config_ι_decimals ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.root_public_key' " := ( SMLLState (U:= Tip3Config ) Tip3Config_ι_root_public_key ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.root_address' " := ( SMLLState (U:= Tip3Config ) Tip3Config_ι_root_address ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'FLeXSellArgs.price' " := ( SMLLState (U:= FLeXSellArgs ) FLeXSellArgs_ι_price ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.amount' " := ( SMLLState (U:= FLeXSellArgs ) FLeXSellArgs_ι_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.lend_finish_time' " := ( SMLLState (U:= FLeXSellArgs ) FLeXSellArgs_ι_lend_finish_time ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.min_amount' " := ( SMLLState (U:= FLeXSellArgs ) FLeXSellArgs_ι_min_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.deals_limit' " := ( SMLLState (U:= FLeXSellArgs ) FLeXSellArgs_ι_deals_limit ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.tons_value' " := ( SMLLState (U:= FLeXSellArgs ) FLeXSellArgs_ι_tons_value ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.price_code' " := ( SMLLState (U:= FLeXSellArgs ) FLeXSellArgs_ι_price_code ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.tip3_code' " := ( SMLLState (U:= FLeXSellArgs ) FLeXSellArgs_ι_tip3_code ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'FLeXBuyArgs.price' " := ( SMLLState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_price ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.amount' " := ( SMLLState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.order_finish_time' " := ( SMLLState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_order_finish_time ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.min_amount' " := ( SMLLState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_min_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.deals_limit' " := ( SMLLState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_deals_limit ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.deploy_value' " := ( SMLLState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_deploy_value ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.price_code' " := ( SMLLState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_price_code ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.my_tip3_addr' " := ( SMLLState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_my_tip3_addr ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.tip3_code' " := ( SMLLState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_tip3_code ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'FLeXXchgArgs.sell' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_sell ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.price_num' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_price_num ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.price_denum' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_price_denum ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.amount' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.lend_amount' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_lend_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.lend_finish_time' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_lend_finish_time ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.min_amount' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_min_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.deals_limit' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_deals_limit ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.tons_value' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_tons_value ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.xchg_price_code' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_xchg_price_code ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.tip3_code' " := ( SMLLState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_tip3_code ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'FLeXCancelArgs.price' " := ( SMLLState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_price ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.min_amount' " := ( SMLLState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_min_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.deals_limit' " := ( SMLLState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_deals_limit ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.value' " := ( SMLLState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_value ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.price_code' " := ( SMLLState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_price_code ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.tip3_code' " := ( SMLLState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_tip3_code ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'FLeXXchgCancelArgs.sell' " := ( SMLLState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_sell ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.price_num' " := ( SMLLState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_price_num ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.price_denum' " := ( SMLLState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_price_denum ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.min_amount' " := ( SMLLState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_min_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.deals_limit' " := ( SMLLState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_deals_limit ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.value' " := ( SMLLState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_value ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.xchg_price_code' " := ( SMLLState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_xchg_price_code ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.tip3_code' " := ( SMLLState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_tip3_code ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'FLeXClient.owner_' " := ( SMLLState (U:= FLeXClient ) FLeXClient_ι_owner_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.trading_pair_code_' " := ( SMLLState (U:= FLeXClient ) FLeXClient_ι_trading_pair_code_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.xchg_pair_code_' " := ( SMLLState (U:= FLeXClient ) FLeXClient_ι_xchg_pair_code_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.workchain_id_' " := ( SMLLState (U:= FLeXClient ) FLeXClient_ι_workchain_id_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.tons_cfg_' " := ( SMLLState (U:= FLeXClient ) FLeXClient_ι_tons_cfg_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.flex_' " := ( SMLLState (U:= FLeXClient ) FLeXClient_ι_flex_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.notify_addr_' " := ( SMLLState (U:= FLeXClient ) FLeXClient_ι_notify_addr_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'FLeX.deployer_pubkey_' " := ( SMLLState (U:= FLeX ) FLeX_ι_deployer_pubkey_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeX.tons_cfg_' " := ( SMLLState (U:= FLeX ) FLeX_ι_tons_cfg_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeX.pair_code_' " := ( SMLLState (U:= FLeX ) FLeX_ι_pair_code_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeX.xchg_pair_code_' " := ( SMLLState (U:= FLeX ) FLeX_ι_xchg_pair_code_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeX.price_code_' " := ( SMLLState (U:= FLeX ) FLeX_ι_price_code_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeX.xchg_price_code_' " := ( SMLLState (U:= FLeX ) FLeX_ι_xchg_price_code_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeX.min_amount_' " := ( SMLLState (U:= FLeX ) FLeX_ι_min_amount_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeX.deals_limit_' " := ( SMLLState (U:= FLeX ) FLeX_ι_deals_limit_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'FLeX.notify_addr_' " := ( SMLLState (U:= FLeX ) FLeX_ι_notify_addr_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'process_ret.sells_amount' " := ( SMLLState (U:= process_ret ) process_ret_ι_sells_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'process_ret.buys_amount' " := ( SMLLState (U:= process_ret ) process_ret_ι_buys_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'process_ret.ret_' " := ( SMLLState (U:= process_ret ) process_ret_ι_ret_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'SellArgs.amount' " := ( SMLLState (U:= SellArgs ) SellArgs_ι_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'SellArgs.receive_wallet' " := ( SMLLState (U:= SellArgs ) SellArgs_ι_receive_wallet ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'DetailsInfo.price' " := ( SMLLState (U:= DetailsInfo ) DetailsInfo_ι_price ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.min_amount' " := ( SMLLState (U:= DetailsInfo ) DetailsInfo_ι_min_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.sell_amount' " := ( SMLLState (U:= DetailsInfo ) DetailsInfo_ι_sell_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.buy_amount' " := ( SMLLState (U:= DetailsInfo ) DetailsInfo_ι_buy_amount ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'Price.price_' " := ( SMLLState (U:= Price ) Price_ι_price_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.sells_amount_' " := ( SMLLState (U:= Price ) Price_ι_sells_amount_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.buys_amount_' " := ( SMLLState (U:= Price ) Price_ι_buys_amount_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.flex_' " := ( SMLLState (U:= Price ) Price_ι_flex_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.min_amount_' " := ( SMLLState (U:= Price ) Price_ι_min_amount_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.deals_limit_' " := ( SMLLState (U:= Price ) Price_ι_deals_limit_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.notify_addr_' " := ( SMLLState (U:= Price ) Price_ι_notify_addr_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.workchain_id_' " := ( SMLLState (U:= Price ) Price_ι_workchain_id_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.tons_cfg_' " := ( SMLLState (U:= Price ) Price_ι_tons_cfg_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.tip3_code_' " := ( SMLLState (U:= Price ) Price_ι_tip3_code_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'Price.tip3cfg_' " := ( SMLLState (U:= Price ) Price_ι_tip3cfg_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'RationalPrice.num' " := ( SMLLState (U:= RationalPrice ) RationalPrice_ι_num ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'RationalPrice.denum' " := ( SMLLState (U:= RationalPrice ) RationalPrice_ι_denum ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'PayloadArgs.sell' " := ( SMLLState (U:= PayloadArgs ) PayloadArgs_ι_sell ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.amount' " := ( SMLLState (U:= PayloadArgs ) PayloadArgs_ι_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( SMLLState (U:= PayloadArgs ) PayloadArgs_ι_receive_tip3_wallet ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( SMLLState (U:= PayloadArgs ) PayloadArgs_ι_client_addr ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'OrderInfoXchg.original_amount' " := ( SMLLState (U:= OrderInfoXchg ) OrderInfoXchg_ι_original_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.amount' " := ( SMLLState (U:= OrderInfoXchg ) OrderInfoXchg_ι_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.account' " := ( SMLLState (U:= OrderInfoXchg ) OrderInfoXchg_ι_account ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( SMLLState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_provide ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( SMLLState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_receive ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.client_addr' " := ( SMLLState (U:= OrderInfoXchg ) OrderInfoXchg_ι_client_addr ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.order_finish_time' " := ( SMLLState (U:= OrderInfoXchg ) OrderInfoXchg_ι_order_finish_time ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'DetailsInfoXchg.price_num' " := ( SMLLState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_price_num ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.price_denum' " := ( SMLLState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_price_denum ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.min_amount' " := ( SMLLState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_min_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.sell_amount' " := ( SMLLState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_sell_amount ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.buy_amount' " := ( SMLLState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_buy_amount ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'PriceXchg.price_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_price_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.sells_amount_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_sells_amount_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.buys_amount_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_buys_amount_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.flex_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_flex_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.min_amount_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_min_amount_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.deals_limit_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_deals_limit_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.notify_addr_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_notify_addr_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.workchain_id_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_workchain_id_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.tons_cfg_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_tons_cfg_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.tip3_code_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_tip3_code_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.major_tip3cfg_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_major_tip3cfg_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( SMLLState (U:= PriceXchg ) PriceXchg_ι_minor_tip3cfg_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'DTradingPair.flex_addr_' " := ( SMLLState (U:= DTradingPair ) DTradingPair_ι_flex_addr_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTradingPair.tip3_root_' " := ( SMLLState (U:= DTradingPair ) DTradingPair_ι_tip3_root_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DTradingPair.deploy_value_' " := ( SMLLState (U:= DTradingPair ) DTradingPair_ι_deploy_value_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'DXchgPair.flex_addr_' " := ( SMLLState (U:= DXchgPair ) DXchgPair_ι_flex_addr_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.tip3_major_root_' " := ( SMLLState (U:= DXchgPair ) DXchgPair_ι_tip3_major_root_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.tip3_minor_root_' " := ( SMLLState (U:= DXchgPair ) DXchgPair_ι_tip3_minor_root_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.deploy_value_' " := ( SMLLState (U:= DXchgPair ) DXchgPair_ι_deploy_value_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'LocalState.uint256' " := ( SMLLState (U:= LocalState ) LocalState_ι_uint256 ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.cell' " := ( SMLLState (U:= LocalState ) LocalState_ι_cell ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.TonsConfig' " := ( SMLLState (U:= LocalState ) LocalState_ι_TonsConfig ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.address' " := ( SMLLState (U:= LocalState ) LocalState_ι_address ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint128' " := ( SMLLState (U:= LocalState ) LocalState_ι_uint128 ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.StateInit' " := ( SMLLState (U:= LocalState ) LocalState_ι_StateInit ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.DTradingPair' " := ( SMLLState (U:= LocalState ) LocalState_ι_DTradingPair ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITradingPair_' " := ( SMLLState (U:= LocalState ) LocalState_ι_handle_ITradingPair_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.DXchgPair' " := ( SMLLState (U:= LocalState ) LocalState_ι_DXchgPair ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IXchgPair_' " := ( SMLLState (U:= LocalState ) LocalState_ι_handle_IXchgPair_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXSellArgs_' " := ( SMLLState (U:= LocalState ) LocalState_ι_parse_FLeXSellArgs_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPrice_' " := ( SMLLState (U:= LocalState ) LocalState_ι_handle_IPrice_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.SellArgs' " := ( SMLLState (U:= LocalState ) LocalState_ι_SellArgs ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXBuyArgs_' " := ( SMLLState (U:= LocalState ) LocalState_ι_parse_FLeXBuyArgs_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXCancelArgs_' " := ( SMLLState (U:= LocalState ) LocalState_ι_parse_FLeXCancelArgs_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgCancelArgs_' " := ( SMLLState (U:= LocalState ) LocalState_ι_parse_FLeXXchgCancelArgs_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPriceXchg_' " := ( SMLLState (U:= LocalState ) LocalState_ι_handle_IPriceXchg_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool_t' " := ( SMLLState (U:= LocalState ) LocalState_ι_bool_t ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgArgs_' " := ( SMLLState (U:= LocalState ) LocalState_ι_parse_FLeXXchgArgs_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.PayloadArgs' " := ( SMLLState (U:= LocalState ) LocalState_ι_PayloadArgs ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITONTokenWallet_' " := ( SMLLState (U:= LocalState ) LocalState_ι_handle_ITONTokenWallet_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint8' " := ( SMLLState (U:= LocalState ) LocalState_ι_uint8 ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.Tip3Config' " := ( SMLLState (U:= LocalState ) LocalState_ι_Tip3Config ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPrice' " := ( SMLLState (U:= LocalState ) LocalState_ι_DPrice ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceXchg' " := ( SMLLState (U:= LocalState ) LocalState_ι_DPriceXchg ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.tuple_address_address' " := ( SMLLState (U:= LocalState ) LocalState_ι_tuple_address_address ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint32' " := ( SMLLState (U:= LocalState ) LocalState_ι_uint32 ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.unsigned' " := ( SMLLState (U:= LocalState ) LocalState_ι_unsigned ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.OrderInfo' " := ( SMLLState (U:= LocalState ) LocalState_ι_OrderInfo ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.int' " := ( SMLLState (U:= LocalState ) LocalState_ι_int ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_uint128_' " := ( SMLLState (U:= LocalState ) LocalState_ι_optional_uint128_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool' " := ( SMLLState (U:= LocalState ) LocalState_ι_bool ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_OrderInfoWithIdx_' " := ( SMLLState (U:= LocalState ) LocalState_ι_optional_OrderInfoWithIdx_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.queue_OrderInfo_' " := ( SMLLState (U:= LocalState ) LocalState_ι_queue_OrderInfo_ ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.pair_unsigned_OrderInfo_' " := ( SMLLState (U:= LocalState ) LocalState_ι_pair_unsigned_OrderInfo_ ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'TickTock.tick' " := ( SMLRState (U:= TickTock ) TickTock_ι_tick ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'TickTock.tock' " := ( SMLRState (U:= TickTock ) TickTock_ι_tock ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'allowance_info.spender' " := ( SMLRState (U:= allowance_info ) allowance_info_ι_spender ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( SMLRState (U:= allowance_info ) allowance_info_ι_remainingTokens ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'StateInit.split_depth' " := ( SMLRState (U:= StateInit ) StateInit_ι_split_depth ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'StateInit.special' " := ( SMLRState (U:= StateInit ) StateInit_ι_special ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'StateInit.code' " := ( SMLRState (U:= StateInit ) StateInit_ι_code ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'StateInit.data' " := ( SMLRState (U:= StateInit ) StateInit_ι_data ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'StateInit.library' " := ( SMLRState (U:= StateInit ) StateInit_ι_library ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'DTONTokenWallet.name_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_name_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.symbol_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_symbol_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.decimals_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_decimals_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.balance_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_balance_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.root_public_key_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_root_public_key_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.wallet_public_key_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_wallet_public_key_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.root_address_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_root_address_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.owner_address_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_owner_address_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.code_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_code_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.allowance_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_allowance_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTONTokenWallet.workchain_id_' " := ( SMLRState (U:= DTONTokenWallet ) DTONTokenWallet_ι_workchain_id_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'TonsConfig.transfer_tip3' " := ( SMLRState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( SMLRState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( SMLRState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.order_answer' " := ( SMLRState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.process_queue' " := ( SMLRState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'TonsConfig.send_notify' " := ( SMLRState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'addr_std_fixed.workchain_id' " := ( SMLRState (U:= addr_std_fixed ) addr_std_fixed_ι_workchain_id ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'addr_std_fixed.address' " := ( SMLRState (U:= addr_std_fixed ) addr_std_fixed_ι_address ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'OrderInfo.original_amount' " := ( SMLRState (U:= OrderInfo ) OrderInfo_ι_original_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.amount' " := ( SMLRState (U:= OrderInfo ) OrderInfo_ι_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.account' " := ( SMLRState (U:= OrderInfo ) OrderInfo_ι_account ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.tip3_wallet' " := ( SMLRState (U:= OrderInfo ) OrderInfo_ι_tip3_wallet ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.client_addr' " := ( SMLRState (U:= OrderInfo ) OrderInfo_ι_client_addr ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfo.order_finish_time' " := ( SMLRState (U:= OrderInfo ) OrderInfo_ι_order_finish_time ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'OrderRet.err_code' " := ( SMLRState (U:= OrderRet ) OrderRet_ι_err_code ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderRet.processed' " := ( SMLRState (U:= OrderRet ) OrderRet_ι_processed ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderRet.enqueued' " := ( SMLRState (U:= OrderRet ) OrderRet_ι_enqueued ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'dealer.tip3root_' " := ( SMLRState (U:= dealer ) dealer_ι_tip3root_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'dealer.notify_addr_' " := ( SMLRState (U:= dealer ) dealer_ι_notify_addr_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'dealer.price_' " := ( SMLRState (U:= dealer ) dealer_ι_price_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'dealer.deals_limit_' " := ( SMLRState (U:= dealer ) dealer_ι_deals_limit_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'dealer.tons_cfg_' " := ( SMLRState (U:= dealer ) dealer_ι_tons_cfg_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'dealer.sells_amount_' " := ( SMLRState (U:= dealer ) dealer_ι_sells_amount_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'dealer.buys_amount_' " := ( SMLRState (U:= dealer ) dealer_ι_buys_amount_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'dealer.ret_' " := ( SMLRState (U:= dealer ) dealer_ι_ret_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'FLeXSellArgsAddrs.my_tip3_addr' " := ( SMLRState (U:= FLeXSellArgsAddrs ) FLeXSellArgsAddrs_ι_my_tip3_addr ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgsAddrs.receive_wallet' " := ( SMLRState (U:= FLeXSellArgsAddrs ) FLeXSellArgsAddrs_ι_receive_wallet ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'Tip3Config.name' " := ( SMLRState (U:= Tip3Config ) Tip3Config_ι_name ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.symbol' " := ( SMLRState (U:= Tip3Config ) Tip3Config_ι_symbol ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.decimals' " := ( SMLRState (U:= Tip3Config ) Tip3Config_ι_decimals ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.root_public_key' " := ( SMLRState (U:= Tip3Config ) Tip3Config_ι_root_public_key ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Tip3Config.root_address' " := ( SMLRState (U:= Tip3Config ) Tip3Config_ι_root_address ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'FLeXSellArgs.price' " := ( SMLRState (U:= FLeXSellArgs ) FLeXSellArgs_ι_price ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.amount' " := ( SMLRState (U:= FLeXSellArgs ) FLeXSellArgs_ι_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.lend_finish_time' " := ( SMLRState (U:= FLeXSellArgs ) FLeXSellArgs_ι_lend_finish_time ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.min_amount' " := ( SMLRState (U:= FLeXSellArgs ) FLeXSellArgs_ι_min_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.deals_limit' " := ( SMLRState (U:= FLeXSellArgs ) FLeXSellArgs_ι_deals_limit ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.tons_value' " := ( SMLRState (U:= FLeXSellArgs ) FLeXSellArgs_ι_tons_value ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.price_code' " := ( SMLRState (U:= FLeXSellArgs ) FLeXSellArgs_ι_price_code ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXSellArgs.tip3_code' " := ( SMLRState (U:= FLeXSellArgs ) FLeXSellArgs_ι_tip3_code ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'FLeXBuyArgs.price' " := ( SMLRState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_price ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.amount' " := ( SMLRState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.order_finish_time' " := ( SMLRState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_order_finish_time ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.min_amount' " := ( SMLRState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_min_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.deals_limit' " := ( SMLRState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_deals_limit ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.deploy_value' " := ( SMLRState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_deploy_value ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.price_code' " := ( SMLRState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_price_code ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.my_tip3_addr' " := ( SMLRState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_my_tip3_addr ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXBuyArgs.tip3_code' " := ( SMLRState (U:= FLeXBuyArgs ) FLeXBuyArgs_ι_tip3_code ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'FLeXXchgArgs.sell' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_sell ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.price_num' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_price_num ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.price_denum' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_price_denum ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.amount' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.lend_amount' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_lend_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.lend_finish_time' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_lend_finish_time ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.min_amount' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_min_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.deals_limit' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_deals_limit ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.tons_value' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_tons_value ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.xchg_price_code' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_xchg_price_code ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgArgs.tip3_code' " := ( SMLRState (U:= FLeXXchgArgs ) FLeXXchgArgs_ι_tip3_code ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'FLeXCancelArgs.price' " := ( SMLRState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_price ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.min_amount' " := ( SMLRState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_min_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.deals_limit' " := ( SMLRState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_deals_limit ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.value' " := ( SMLRState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_value ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.price_code' " := ( SMLRState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_price_code ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXCancelArgs.tip3_code' " := ( SMLRState (U:= FLeXCancelArgs ) FLeXCancelArgs_ι_tip3_code ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'FLeXXchgCancelArgs.sell' " := ( SMLRState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_sell ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.price_num' " := ( SMLRState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_price_num ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.price_denum' " := ( SMLRState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_price_denum ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.min_amount' " := ( SMLRState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_min_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.deals_limit' " := ( SMLRState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_deals_limit ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.value' " := ( SMLRState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_value ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.xchg_price_code' " := ( SMLRState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_xchg_price_code ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXXchgCancelArgs.tip3_code' " := ( SMLRState (U:= FLeXXchgCancelArgs ) FLeXXchgCancelArgs_ι_tip3_code ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'FLeXClient.owner_' " := ( SMLRState (U:= FLeXClient ) FLeXClient_ι_owner_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.trading_pair_code_' " := ( SMLRState (U:= FLeXClient ) FLeXClient_ι_trading_pair_code_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.xchg_pair_code_' " := ( SMLRState (U:= FLeXClient ) FLeXClient_ι_xchg_pair_code_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.workchain_id_' " := ( SMLRState (U:= FLeXClient ) FLeXClient_ι_workchain_id_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.tons_cfg_' " := ( SMLRState (U:= FLeXClient ) FLeXClient_ι_tons_cfg_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.flex_' " := ( SMLRState (U:= FLeXClient ) FLeXClient_ι_flex_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeXClient.notify_addr_' " := ( SMLRState (U:= FLeXClient ) FLeXClient_ι_notify_addr_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'FLeX.deployer_pubkey_' " := ( SMLRState (U:= FLeX ) FLeX_ι_deployer_pubkey_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeX.tons_cfg_' " := ( SMLRState (U:= FLeX ) FLeX_ι_tons_cfg_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeX.pair_code_' " := ( SMLRState (U:= FLeX ) FLeX_ι_pair_code_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeX.xchg_pair_code_' " := ( SMLRState (U:= FLeX ) FLeX_ι_xchg_pair_code_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeX.price_code_' " := ( SMLRState (U:= FLeX ) FLeX_ι_price_code_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeX.xchg_price_code_' " := ( SMLRState (U:= FLeX ) FLeX_ι_xchg_price_code_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeX.min_amount_' " := ( SMLRState (U:= FLeX ) FLeX_ι_min_amount_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeX.deals_limit_' " := ( SMLRState (U:= FLeX ) FLeX_ι_deals_limit_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'FLeX.notify_addr_' " := ( SMLRState (U:= FLeX ) FLeX_ι_notify_addr_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'process_ret.sells_amount' " := ( SMLRState (U:= process_ret ) process_ret_ι_sells_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'process_ret.buys_amount' " := ( SMLRState (U:= process_ret ) process_ret_ι_buys_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'process_ret.ret_' " := ( SMLRState (U:= process_ret ) process_ret_ι_ret_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'SellArgs.amount' " := ( SMLRState (U:= SellArgs ) SellArgs_ι_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'SellArgs.receive_wallet' " := ( SMLRState (U:= SellArgs ) SellArgs_ι_receive_wallet ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'DetailsInfo.price' " := ( SMLRState (U:= DetailsInfo ) DetailsInfo_ι_price ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.min_amount' " := ( SMLRState (U:= DetailsInfo ) DetailsInfo_ι_min_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.sell_amount' " := ( SMLRState (U:= DetailsInfo ) DetailsInfo_ι_sell_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DetailsInfo.buy_amount' " := ( SMLRState (U:= DetailsInfo ) DetailsInfo_ι_buy_amount ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'Price.price_' " := ( SMLRState (U:= Price ) Price_ι_price_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.sells_amount_' " := ( SMLRState (U:= Price ) Price_ι_sells_amount_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.buys_amount_' " := ( SMLRState (U:= Price ) Price_ι_buys_amount_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.flex_' " := ( SMLRState (U:= Price ) Price_ι_flex_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.min_amount_' " := ( SMLRState (U:= Price ) Price_ι_min_amount_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.deals_limit_' " := ( SMLRState (U:= Price ) Price_ι_deals_limit_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.notify_addr_' " := ( SMLRState (U:= Price ) Price_ι_notify_addr_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.workchain_id_' " := ( SMLRState (U:= Price ) Price_ι_workchain_id_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.tons_cfg_' " := ( SMLRState (U:= Price ) Price_ι_tons_cfg_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.tip3_code_' " := ( SMLRState (U:= Price ) Price_ι_tip3_code_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'Price.tip3cfg_' " := ( SMLRState (U:= Price ) Price_ι_tip3cfg_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'RationalPrice.num' " := ( SMLRState (U:= RationalPrice ) RationalPrice_ι_num ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'RationalPrice.denum' " := ( SMLRState (U:= RationalPrice ) RationalPrice_ι_denum ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'PayloadArgs.sell' " := ( SMLRState (U:= PayloadArgs ) PayloadArgs_ι_sell ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.amount' " := ( SMLRState (U:= PayloadArgs ) PayloadArgs_ι_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( SMLRState (U:= PayloadArgs ) PayloadArgs_ι_receive_tip3_wallet ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( SMLRState (U:= PayloadArgs ) PayloadArgs_ι_client_addr ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'OrderInfoXchg.original_amount' " := ( SMLRState (U:= OrderInfoXchg ) OrderInfoXchg_ι_original_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.amount' " := ( SMLRState (U:= OrderInfoXchg ) OrderInfoXchg_ι_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.account' " := ( SMLRState (U:= OrderInfoXchg ) OrderInfoXchg_ι_account ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( SMLRState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_provide ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( SMLRState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_receive ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.client_addr' " := ( SMLRState (U:= OrderInfoXchg ) OrderInfoXchg_ι_client_addr ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'OrderInfoXchg.order_finish_time' " := ( SMLRState (U:= OrderInfoXchg ) OrderInfoXchg_ι_order_finish_time ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'DetailsInfoXchg.price_num' " := ( SMLRState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_price_num ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.price_denum' " := ( SMLRState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_price_denum ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.min_amount' " := ( SMLRState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_min_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.sell_amount' " := ( SMLRState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_sell_amount ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DetailsInfoXchg.buy_amount' " := ( SMLRState (U:= DetailsInfoXchg ) DetailsInfoXchg_ι_buy_amount ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'PriceXchg.price_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_price_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.sells_amount_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_sells_amount_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.buys_amount_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_buys_amount_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.flex_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_flex_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.min_amount_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_min_amount_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.deals_limit_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_deals_limit_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.notify_addr_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_notify_addr_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.workchain_id_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_workchain_id_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.tons_cfg_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_tons_cfg_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.tip3_code_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_tip3_code_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.major_tip3cfg_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_major_tip3cfg_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( SMLRState (U:= PriceXchg ) PriceXchg_ι_minor_tip3cfg_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'DTradingPair.flex_addr_' " := ( SMLRState (U:= DTradingPair ) DTradingPair_ι_flex_addr_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTradingPair.tip3_root_' " := ( SMLRState (U:= DTradingPair ) DTradingPair_ι_tip3_root_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DTradingPair.deploy_value_' " := ( SMLRState (U:= DTradingPair ) DTradingPair_ι_deploy_value_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'DXchgPair.flex_addr_' " := ( SMLRState (U:= DXchgPair ) DXchgPair_ι_flex_addr_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.tip3_major_root_' " := ( SMLRState (U:= DXchgPair ) DXchgPair_ι_tip3_major_root_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.tip3_minor_root_' " := ( SMLRState (U:= DXchgPair ) DXchgPair_ι_tip3_minor_root_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'DXchgPair.deploy_value_' " := ( SMLRState (U:= DXchgPair ) DXchgPair_ι_deploy_value_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'LocalState.uint256' " := ( SMLRState (U:= LocalState ) LocalState_ι_uint256 ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.cell' " := ( SMLRState (U:= LocalState ) LocalState_ι_cell ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.TonsConfig' " := ( SMLRState (U:= LocalState ) LocalState_ι_TonsConfig ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.address' " := ( SMLRState (U:= LocalState ) LocalState_ι_address ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint128' " := ( SMLRState (U:= LocalState ) LocalState_ι_uint128 ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.StateInit' " := ( SMLRState (U:= LocalState ) LocalState_ι_StateInit ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.DTradingPair' " := ( SMLRState (U:= LocalState ) LocalState_ι_DTradingPair ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITradingPair_' " := ( SMLRState (U:= LocalState ) LocalState_ι_handle_ITradingPair_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.DXchgPair' " := ( SMLRState (U:= LocalState ) LocalState_ι_DXchgPair ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IXchgPair_' " := ( SMLRState (U:= LocalState ) LocalState_ι_handle_IXchgPair_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXSellArgs_' " := ( SMLRState (U:= LocalState ) LocalState_ι_parse_FLeXSellArgs_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPrice_' " := ( SMLRState (U:= LocalState ) LocalState_ι_handle_IPrice_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.SellArgs' " := ( SMLRState (U:= LocalState ) LocalState_ι_SellArgs ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXBuyArgs_' " := ( SMLRState (U:= LocalState ) LocalState_ι_parse_FLeXBuyArgs_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXCancelArgs_' " := ( SMLRState (U:= LocalState ) LocalState_ι_parse_FLeXCancelArgs_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgCancelArgs_' " := ( SMLRState (U:= LocalState ) LocalState_ι_parse_FLeXXchgCancelArgs_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPriceXchg_' " := ( SMLRState (U:= LocalState ) LocalState_ι_handle_IPriceXchg_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool_t' " := ( SMLRState (U:= LocalState ) LocalState_ι_bool_t ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgArgs_' " := ( SMLRState (U:= LocalState ) LocalState_ι_parse_FLeXXchgArgs_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.PayloadArgs' " := ( SMLRState (U:= LocalState ) LocalState_ι_PayloadArgs ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITONTokenWallet_' " := ( SMLRState (U:= LocalState ) LocalState_ι_handle_ITONTokenWallet_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint8' " := ( SMLRState (U:= LocalState ) LocalState_ι_uint8 ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.Tip3Config' " := ( SMLRState (U:= LocalState ) LocalState_ι_Tip3Config ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPrice' " := ( SMLRState (U:= LocalState ) LocalState_ι_DPrice ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceXchg' " := ( SMLRState (U:= LocalState ) LocalState_ι_DPriceXchg ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.tuple_address_address' " := ( SMLRState (U:= LocalState ) LocalState_ι_tuple_address_address ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint32' " := ( SMLRState (U:= LocalState ) LocalState_ι_uint32 ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.unsigned' " := ( SMLRState (U:= LocalState ) LocalState_ι_unsigned ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.OrderInfo' " := ( SMLRState (U:= LocalState ) LocalState_ι_OrderInfo ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.int' " := ( SMLRState (U:= LocalState ) LocalState_ι_int ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_uint128_' " := ( SMLRState (U:= LocalState ) LocalState_ι_optional_uint128_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool' " := ( SMLRState (U:= LocalState ) LocalState_ι_bool ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_OrderInfoWithIdx_' " := ( SMLRState (U:= LocalState ) LocalState_ι_optional_OrderInfoWithIdx_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.queue_OrderInfo_' " := ( SMLRState (U:= LocalState ) LocalState_ι_queue_OrderInfo_ ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.pair_unsigned_OrderInfo_' " := ( SMLRState (U:= LocalState ) LocalState_ι_pair_unsigned_OrderInfo_ ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'LocalState.uint256Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint256Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.cellIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_cellIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.TonsConfigIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_TonsConfigIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.addressIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_addressIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint128Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint128Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.StateInitIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_StateInitIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.DTradingPairIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DTradingPairIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITradingPair_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_ITradingPair_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.DXchgPairIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DXchgPairIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IXchgPair_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IXchgPair_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXSellArgs_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXSellArgs_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPrice_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IPrice_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.SellArgsIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_SellArgsIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXBuyArgs_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXBuyArgs_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXCancelArgs_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXCancelArgs_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgCancelArgs_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXXchgCancelArgs_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPriceXchg_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IPriceXchg_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool_tIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_bool_tIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgArgs_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXXchgArgs_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.PayloadArgsIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_PayloadArgsIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITONTokenWallet_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_ITONTokenWallet_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint8Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint8Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.Tip3ConfigIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_Tip3ConfigIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DPriceIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceXchgIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DPriceXchgIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.tuple_address_addressIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_tuple_address_addressIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint32Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint32Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.unsignedIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_unsignedIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.OrderInfoIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_OrderInfoIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.intIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_intIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_uint128_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_optional_uint128_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.boolIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_boolIndex ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_OrderInfoWithIdx_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_optional_OrderInfoWithIdx_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.queue_OrderInfo_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_queue_OrderInfo_Index ) (in custom SMLLValue at level 0) : sml_scope. 
 Notation " 'LocalState.pair_unsigned_OrderInfo_Index' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_pair_unsigned_OrderInfo_Index ) (in custom SMLLValue at level 0) : sml_scope. 

Notation " 'LocalState.uint256Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint256Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.cellIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_cellIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.TonsConfigIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_TonsConfigIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.addressIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_addressIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint128Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint128Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.StateInitIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_StateInitIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.DTradingPairIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DTradingPairIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITradingPair_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_ITradingPair_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.DXchgPairIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DXchgPairIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IXchgPair_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IXchgPair_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXSellArgs_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXSellArgs_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPrice_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IPrice_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.SellArgsIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_SellArgsIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXBuyArgs_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXBuyArgs_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXCancelArgs_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXCancelArgs_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgCancelArgs_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXXchgCancelArgs_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_IPriceXchg_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_IPriceXchg_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.bool_tIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_bool_tIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.parse_FLeXXchgArgs_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_parse_FLeXXchgArgs_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.PayloadArgsIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_PayloadArgsIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.handle_ITONTokenWallet_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_handle_ITONTokenWallet_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint8Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint8Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.Tip3ConfigIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_Tip3ConfigIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DPriceIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.DPriceXchgIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_DPriceXchgIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.tuple_address_addressIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_tuple_address_addressIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.uint32Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_uint32Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.unsignedIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_unsignedIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.OrderInfoIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_OrderInfoIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.intIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_intIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_uint128_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_optional_uint128_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.boolIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_boolIndex ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.optional_OrderInfoWithIdx_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_optional_OrderInfoWithIdx_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.queue_OrderInfo_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_queue_OrderInfo_Index ) (in custom SMLRValue at level 0) : sml_scope. 
 Notation " 'LocalState.pair_unsigned_OrderInfo_Index' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_pair_unsigned_OrderInfo_Index ) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'TIMESTAMP_DELAY' " := (sInject TIMESTAMP_DELAY) (in custom SMLRValue at level 0) : sml_scope.
Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_message_sender_is_not_my_owner) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::sender_is_not_deployer' " := (sInject error_code_ι_sender_is_not_deployer) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::unexpected_refs_count_in_code' " := (sInject error_code_ι_unexpected_refs_count_in_code) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::cant_override_code' " := (sInject error_code_ι_cant_override_code) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'ok' " := (sInject ok) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::out_of_tons' " := (sInject error_code_ι_out_of_tons) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::deals_limit' " := (sInject error_code_ι_deals_limit) (in custom SMLRValue at level 0) : sml_scope.
Notation " 'error_code::not_enough_tons_to_process' " := (sInject error_code_ι_not_enough_tons_to_process) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::not_enough_tokens_amount' " := (sInject error_code_ι_not_enough_tokens_amount) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::too_big_tokens_amount' " := (sInject error_code_ι_too_big_tokens_amount) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::different_workchain_id' " := (sInject error_code_ι_different_workchain_id) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::unverified_tip3_wallet' " := (sInject error_code_ι_unverified_tip3_wallet) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::canceled' " := (sInject error_code_ι_canceled) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::expired' " := (sInject error_code_ι_expired) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'safe_delay_period' " := (sInject safe_delay_period) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'error_code::not_enough_tons' " := (sInject error_code_ι_not_enough_tons) (in custom SMLRValue at level 0) : sml_scope. 

(**************************************************************************************************)

Module FuncEx (tc : specFLeXSig).
Import SMLNotations.
Local Open Scope sml_scope.
Import tc.
Require Import String.
Local Open Scope string_scope.

(* Definition bar33_call (x y: SMLRValue XBool false)  := 
   🏓 sml_call_with_args (LedgerableWithArgs := λ2) bar33 
(SimpleLedgerableArg SMLRValue {{ Λ "b0" }} x) (SimpleLedgerableArg SMLRValue {{ Λ "b1" }} y) .


Notation " 'bar33_' '(' x , y ')' " := ( SMLRResult (bar33_call x y))  
   (in custom SMLRValue at level 0 , x custom SMLRValue at level 0, y custom SMLRValue at level 0) : sml_scope.

Notation " 'bar33_' '(' x , y ')' " := ( FuncallExpression (bar33_call x y))  
   (in custom SMLLValue at level 0 , x custom SMLRValue at level 0, y custom SMLRValue at level 0) : sml_scope.
 *) (*Здесь будут сгенерена последовательность параметров внутри модуля тайпа. Появится новый модуль который будет параметризован 
этим модулетайпом (можно и в этом же файле). Появится абстрактный инстанс этого модулетайпа импорт икс и вот эти все параметры поя
вятся в контексте. Тогда для них мы сможем написать определения . Тогда подключив новый модуль можно писать 
какую-то формулировку. Тогда в новом модуле Роберт сможет сформулировать спецификацию функций, считая то они есть
А потом мы сделаем модуль с самими функциями. *)
 
End FuncEx. 
End FLeXFuncNotations.
