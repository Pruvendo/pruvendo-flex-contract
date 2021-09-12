
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
Require Import UMLang.SML_NG26.

Require Import FLeXContractTypes.

Require Import PriceClass.
Require Import PriceSpecs.
Require Import FLeXConstSig. 
Require Import UrsusStdLib.stdFunc.

Module PriceFuncNotations (xt: XTypesSig) 
                          (sm: StateMonadSig) 
                          (dc : FLeXConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

Module Export specPriceSpec := specPriceSpec xt sm.
Locate ursus_call_with_args.
Locate UrsusNotations.
Import ListNotations.
Import UrsusNotations.

Local Open Scope record. 
Local Open Scope solidity_scope. 
Local Open Scope ursus_scope. 
Local Open Scope string_scope.
Local Open Scope program_scope. 

Import ListNotations.



Parameter Ф_calc_cost : XInteger128 -> XInteger128 -> UExpression ( XMaybe XInteger128 ) false . 
 Parameter dealer_Ф_make_deal : OrderInfo -> OrderInfo -> UExpression ( XBool # XBool # XInteger128 )%sol false . 
 Parameter Ф_is_active_time : XInteger32 -> UExpression XBool false . 
 Parameter dealer_Ф_extract_active_order : ( XMaybe (XInteger # OrderInfo)%sol ) -> XList OrderInfo -> XInteger128 -> XBool -> UExpression ( ( XMaybe (XInteger # OrderInfo)%sol ) # (XList OrderInfo) # XInteger128 )%sol false . 
 Parameter Price_Ф_processQueue : UExpression PhantomType false . 
 Parameter dealer_Ф_process_queue : XInteger -> XInteger -> UExpression PhantomType false . 
 Parameter Price_Ф_onTip3LendOwnershipMinValue : UExpression XInteger128 false . 
 Parameter Price_Ф_expected_wallet_address : XInteger256 -> XInteger256 -> UExpression XInteger256 false . 
 Parameter Price_Ф_verify_tip3_addr : XAddress -> XInteger256 -> XInteger256 -> UExpression XBool false . 
 Parameter Price_Ф_on_sell_fail : XInteger -> ITONTokenWalletPtr -> UExpression OrderRet false . 
 Parameter Price_Ф_onTip3LendOwnership : XAddress -> XInteger128 -> XInteger32 -> XInteger256 -> XAddress -> TvmCell -> UExpression OrderRet false . 
 Parameter Price_Ф_buyTip3MinValue : XInteger128 -> UExpression XInteger128 false . 
 Parameter Price_Ф_buyTip3 : XInteger128 -> XAddress -> XInteger32 -> UExpression OrderRet true . 
 Parameter Ф_cancel_order_impl : XList OrderInfo -> addr_std_fixed -> XInteger128 -> XBool -> Grams -> Grams -> Grams -> UExpression ( XList OrderInfo ) false . 
 Parameter Price_Ф_cancelSell : UExpression PhantomType false . 
 Parameter Price_Ф_cancelBuy : UExpression PhantomType false . 
 Parameter Price_Ф_getPrice : UExpression XInteger128 false . 
 Parameter Price_Ф_getMinimumAmount : UExpression XInteger128 false . 
 Parameter Price_Ф_getSellAmount : UExpression XInteger128 false . 
 Parameter Price_Ф_getBuyAmount : UExpression XInteger128 false . 
 Parameter Price_Ф_getDetails : UExpression DetailsInfo false . 
 Parameter Price_Ф_getTonsCfg : UExpression TonsConfig false . 
 Parameter Price_Ф_getSells : UExpression ( XHMap XInteger OrderInfo) false . 
 Parameter Price_Ф_getBuys : UExpression ( XHMap XInteger OrderInfo) false . 
 Parameter Price_Ф__fallback : TvmCell -> UExpression XInteger false . 



 Notation " 'TickTock.tick' " := ( ULState (U:= TickTock ) TickTock_ι_tick ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TickTock.tick' " := ( URState (U:= TickTock ) TickTock_ι_tick ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TickTock.tock' " := ( ULState (U:= TickTock ) TickTock_ι_tock ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TickTock.tock' " := ( URState (U:= TickTock ) TickTock_ι_tock ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.split_depth' " := ( ULState (U:= StateInit ) StateInit_ι_split_depth ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.split_depth' " := ( URState (U:= StateInit ) StateInit_ι_split_depth ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.special' " := ( ULState (U:= StateInit ) StateInit_ι_special ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.special' " := ( URState (U:= StateInit ) StateInit_ι_special ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.code' " := ( ULState (U:= StateInit ) StateInit_ι_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.code' " := ( URState (U:= StateInit ) StateInit_ι_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.data' " := ( ULState (U:= StateInit ) StateInit_ι_data ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.data' " := ( URState (U:= StateInit ) StateInit_ι_data ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'StateInit.library' " := ( ULState (U:= StateInit ) StateInit_ι_library ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'StateInit.library' " := ( URState (U:= StateInit ) StateInit_ι_library ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.workchain_id' " := ( ULState (U:= addr_std_fixed ) addr_std_fixed_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.workchain_id' " := ( URState (U:= addr_std_fixed ) addr_std_fixed_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.address' " := ( ULState (U:= addr_std_fixed ) addr_std_fixed_ι_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.address' " := ( URState (U:= addr_std_fixed ) addr_std_fixed_ι_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.transfer_tip3' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.transfer_tip3' " := ( URState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.return_ownership' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.return_ownership' " := ( URState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.trading_pair_deploy' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.trading_pair_deploy' " := ( URState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.order_answer' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.order_answer' " := ( URState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.process_queue' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.process_queue' " := ( URState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.send_notify' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.send_notify' " := ( URState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderRet.err_code' " := ( ULState (U:= OrderRet ) OrderRet_ι_err_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderRet.err_code' " := ( URState (U:= OrderRet ) OrderRet_ι_err_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderRet.processed' " := ( ULState (U:= OrderRet ) OrderRet_ι_processed ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderRet.processed' " := ( URState (U:= OrderRet ) OrderRet_ι_processed ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderRet.enqueued' " := ( ULState (U:= OrderRet ) OrderRet_ι_enqueued ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderRet.enqueued' " := ( URState (U:= OrderRet ) OrderRet_ι_enqueued ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'SellArgs.amount' " := ( ULState (U:= SellArgs ) SellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'SellArgs.amount' " := ( URState (U:= SellArgs ) SellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'SellArgs.receive_wallet' " := ( ULState (U:= SellArgs ) SellArgs_ι_receive_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'SellArgs.receive_wallet' " := ( URState (U:= SellArgs ) SellArgs_ι_receive_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.original_amount' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_original_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.original_amount' " := ( URState (U:= OrderInfo ) OrderInfo_ι_original_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.amount' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.amount' " := ( URState (U:= OrderInfo ) OrderInfo_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.account' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_account ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.account' " := ( URState (U:= OrderInfo ) OrderInfo_ι_account ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.tip3_wallet' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.tip3_wallet' " := ( URState (U:= OrderInfo ) OrderInfo_ι_tip3_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.client_addr' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.client_addr' " := ( URState (U:= OrderInfo ) OrderInfo_ι_client_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.order_finish_time' " := ( ULState (U:= OrderInfo ) OrderInfo_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfo.order_finish_time' " := ( URState (U:= OrderInfo ) OrderInfo_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DetailsInfo.price' " := ( ULState (U:= DetailsInfo ) DetailsInfo_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DetailsInfo.price' " := ( URState (U:= DetailsInfo ) DetailsInfo_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DetailsInfo.min_amount' " := ( ULState (U:= DetailsInfo ) DetailsInfo_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DetailsInfo.min_amount' " := ( URState (U:= DetailsInfo ) DetailsInfo_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DetailsInfo.sell_amount' " := ( ULState (U:= DetailsInfo ) DetailsInfo_ι_sell_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DetailsInfo.sell_amount' " := ( URState (U:= DetailsInfo ) DetailsInfo_ι_sell_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DetailsInfo.buy_amount' " := ( ULState (U:= DetailsInfo ) DetailsInfo_ι_buy_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DetailsInfo.buy_amount' " := ( URState (U:= DetailsInfo ) DetailsInfo_ι_buy_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.name' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_name ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.name' " := ( URState (U:= Tip3Config ) Tip3Config_ι_name ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.symbol' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_symbol ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.symbol' " := ( URState (U:= Tip3Config ) Tip3Config_ι_symbol ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.decimals' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_decimals ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.decimals' " := ( URState (U:= Tip3Config ) Tip3Config_ι_decimals ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_public_key' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_root_public_key ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_public_key' " := ( URState (U:= Tip3Config ) Tip3Config_ι_root_public_key ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_address' " := ( ULState (U:= Tip3Config ) Tip3Config_ι_root_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Tip3Config.root_address' " := ( URState (U:= Tip3Config ) Tip3Config_ι_root_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.price_' " := ( ULState (U:= Price ) Price_ι_price_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.price_' " := ( URState (U:= Price ) Price_ι_price_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount_' " := ( ULState (U:= Price ) Price_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.sells_amount_' " := ( URState (U:= Price ) Price_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.buys_amount_' " := ( ULState (U:= Price ) Price_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.buys_amount_' " := ( URState (U:= Price ) Price_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.flex_' " := ( ULState (U:= Price ) Price_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.flex_' " := ( URState (U:= Price ) Price_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.min_amount_' " := ( ULState (U:= Price ) Price_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.min_amount_' " := ( URState (U:= Price ) Price_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.deals_limit_' " := ( ULState (U:= Price ) Price_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.deals_limit_' " := ( URState (U:= Price ) Price_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.notify_addr_' " := ( ULState (U:= Price ) Price_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.notify_addr_' " := ( URState (U:= Price ) Price_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.workchain_id_' " := ( ULState (U:= Price ) Price_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.workchain_id_' " := ( URState (U:= Price ) Price_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tons_cfg_' " := ( ULState (U:= Price ) Price_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tons_cfg_' " := ( URState (U:= Price ) Price_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tip3_code_' " := ( ULState (U:= Price ) Price_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tip3_code_' " := ( URState (U:= Price ) Price_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.tip3cfg_' " := ( ULState (U:= Price ) Price_ι_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.tip3cfg_' " := ( URState (U:= Price ) Price_ι_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.sells_' " := ( ULState (U:= Price ) Price_ι_sells_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.sells_' " := ( URState (U:= Price ) Price_ι_sells_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Price.buys_' " := ( ULState (U:= Price ) Price_ι_buys_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Price.buys_' " := ( URState (U:= Price ) Price_ι_buys_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.tip3root_' " := ( ULState (U:= dealer ) dealer_ι_tip3root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.tip3root_' " := ( URState (U:= dealer ) dealer_ι_tip3root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.notify_addr_' " := ( ULState (U:= dealer ) dealer_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.notify_addr_' " := ( URState (U:= dealer ) dealer_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.price_' " := ( ULState (U:= dealer ) dealer_ι_price_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.price_' " := ( URState (U:= dealer ) dealer_ι_price_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.deals_limit_' " := ( ULState (U:= dealer ) dealer_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.deals_limit_' " := ( URState (U:= dealer ) dealer_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.tons_cfg_' " := ( ULState (U:= dealer ) dealer_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.tons_cfg_' " := ( URState (U:= dealer ) dealer_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.sells_amount_' " := ( ULState (U:= dealer ) dealer_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.sells_amount_' " := ( URState (U:= dealer ) dealer_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.sells_' " := ( ULState (U:= dealer ) dealer_ι_sells_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.sells_' " := ( URState (U:= dealer ) dealer_ι_sells_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.buys_amount_' " := ( ULState (U:= dealer ) dealer_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.buys_amount_' " := ( URState (U:= dealer ) dealer_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.buys_' " := ( ULState (U:= dealer ) dealer_ι_buys_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.buys_' " := ( URState (U:= dealer ) dealer_ι_buys_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'dealer.ret_' " := ( ULState (U:= dealer ) dealer_ι_ret_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'dealer.ret_' " := ( URState (U:= dealer ) dealer_ι_ret_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'process_ret.sells_amount' " := ( ULState (U:= process_ret ) process_ret_ι_sells_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'process_ret.sells_amount' " := ( URState (U:= process_ret ) process_ret_ι_sells_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'process_ret.sells_' " := ( ULState (U:= process_ret ) process_ret_ι_sells_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'process_ret.sells_' " := ( URState (U:= process_ret ) process_ret_ι_sells_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'process_ret.buys_amount' " := ( ULState (U:= process_ret ) process_ret_ι_buys_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'process_ret.buys_amount' " := ( URState (U:= process_ret ) process_ret_ι_buys_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'process_ret.buys_' " := ( ULState (U:= process_ret ) process_ret_ι_buys_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'process_ret.buys_' " := ( URState (U:= process_ret ) process_ret_ι_buys_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'process_ret.ret_' " := ( ULState (U:= process_ret ) process_ret_ι_ret_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'process_ret.ret_' " := ( URState (U:= process_ret ) process_ret_ι_ret_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'lend_ownership_info.owner' " := ( ULState (U:= lend_ownership_info ) lend_ownership_info_ι_owner ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'lend_ownership_info.owner' " := ( URState (U:= lend_ownership_info ) lend_ownership_info_ι_owner ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'lend_ownership_info.lend_balance' " := ( ULState (U:= lend_ownership_info ) lend_ownership_info_ι_lend_balance ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'lend_ownership_info.lend_balance' " := ( URState (U:= lend_ownership_info ) lend_ownership_info_ι_lend_balance ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'lend_ownership_info.lend_finish_time' " := ( ULState (U:= lend_ownership_info ) lend_ownership_info_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'lend_ownership_info.lend_finish_time' " := ( URState (U:= lend_ownership_info ) lend_ownership_info_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'allowance_info.spender' " := ( ULState (U:= allowance_info ) allowance_info_ι_spender ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'allowance_info.spender' " := ( URState (U:= allowance_info ) allowance_info_ι_spender ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'allowance_info.remainingTokens' " := ( ULState (U:= allowance_info ) allowance_info_ι_remainingTokens ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'allowance_info.remainingTokens' " := ( URState (U:= allowance_info ) allowance_info_ι_remainingTokens ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.name_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_name_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.name_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_name_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.symbol_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_symbol_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.symbol_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_symbol_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.decimals_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_decimals_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.decimals_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_decimals_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.balance_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_balance_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.balance_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_balance_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.root_public_key_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_root_public_key_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.root_public_key_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_root_public_key_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.wallet_public_key_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_wallet_public_key_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.wallet_public_key_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_wallet_public_key_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.root_address_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_root_address_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.root_address_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_root_address_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.owner_address_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_owner_address_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.owner_address_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_owner_address_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.lend_ownership_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_lend_ownership_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.lend_ownership_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_lend_ownership_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.code_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.code_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.allowance_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_allowance_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.allowance_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_allowance_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.workchain_id_' " := ( ULState (U:= TONTokenWallet ) TONTokenWallet_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TONTokenWallet.workchain_id_' " := ( URState (U:= TONTokenWallet ) TONTokenWallet_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.original_amount' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_original_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.original_amount' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_original_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.amount' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.amount' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.account' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_account ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.account' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_account ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_provide ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_provide ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_receive ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_tip3_wallet_receive ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.client_addr' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.client_addr' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_client_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.order_finish_time' " := ( ULState (U:= OrderInfoXchg ) OrderInfoXchg_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'OrderInfoXchg.order_finish_time' " := ( URState (U:= OrderInfoXchg ) OrderInfoXchg_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.cell' " := ( ULState (U:= LocalState ) LocalState_ι_cell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.cell' " := ( URState (U:= LocalState ) LocalState_ι_cell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.StateInit' " := ( ULState (U:= LocalState ) LocalState_ι_StateInit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.StateInit' " := ( URState (U:= LocalState ) LocalState_ι_StateInit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInituint256' " := ( ULState (U:= LocalState ) LocalState_ι_tplStateInituint256 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInituint256' " := ( URState (U:= LocalState ) LocalState_ι_tplStateInituint256 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.bool' " := ( ULState (U:= LocalState ) LocalState_ι_bool ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.bool' " := ( URState (U:= LocalState ) LocalState_ι_bool ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint32' " := ( ULState (U:= LocalState ) LocalState_ι_uint32 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint32' " := ( URState (U:= LocalState ) LocalState_ι_uint32 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.Price' " := ( ULState (U:= LocalState ) LocalState_ι_Price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.Price' " := ( URState (U:= LocalState ) LocalState_ι_Price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.optuint128' " := ( ULState (U:= LocalState ) LocalState_ι_optuint128 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.optuint128' " := ( URState (U:= LocalState ) LocalState_ι_optuint128 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint128' " := ( ULState (U:= LocalState ) LocalState_ι_uint128 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint128' " := ( URState (U:= LocalState ) LocalState_ι_uint128 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplboolbool' " := ( ULState (U:= LocalState ) LocalState_ι_tplboolbool ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplboolbool' " := ( URState (U:= LocalState ) LocalState_ι_tplboolbool ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.OrderInfo' " := ( ULState (U:= LocalState ) LocalState_ι_OrderInfo ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.OrderInfo' " := ( URState (U:= LocalState ) LocalState_ι_OrderInfo ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.int' " := ( ULState (U:= LocalState ) LocalState_ι_int ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.int' " := ( URState (U:= LocalState ) LocalState_ι_int ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tploptional_pair_unsigned_OrderInfoqueue_OrderInfo' " := ( ULState (U:= LocalState ) LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfo ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tploptional_pair_unsigned_OrderInfoqueue_OrderInfo' " := ( URState (U:= LocalState ) LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfo ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.optpair_unsigned_OrderInfo__' " := ( ULState (U:= LocalState ) LocalState_ι_optpair_unsigned_OrderInfo__ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.optpair_unsigned_OrderInfo__' " := ( URState (U:= LocalState ) LocalState_ι_optpair_unsigned_OrderInfo__ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.queueOrderInfo' " := ( ULState (U:= LocalState ) LocalState_ι_queueOrderInfo ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.queueOrderInfo' " := ( URState (U:= LocalState ) LocalState_ι_queueOrderInfo ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.OrderRet' " := ( ULState (U:= LocalState ) LocalState_ι_OrderRet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.OrderRet' " := ( URState (U:= LocalState ) LocalState_ι_OrderRet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.unsigned' " := ( ULState (U:= LocalState ) LocalState_ι_unsigned ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.unsigned' " := ( URState (U:= LocalState ) LocalState_ι_unsigned ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.dealer' " := ( ULState (U:= LocalState ) LocalState_ι_dealer ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.dealer' " := ( URState (U:= LocalState ) LocalState_ι_dealer ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.process_ret' " := ( ULState (U:= LocalState ) LocalState_ι_process_ret ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.process_ret' " := ( URState (U:= LocalState ) LocalState_ι_process_ret ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint8' " := ( ULState (U:= LocalState ) LocalState_ι_uint8 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint8' " := ( URState (U:= LocalState ) LocalState_ι_uint8 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TonsConfig' " := ( ULState (U:= LocalState ) LocalState_ι_TonsConfig ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TonsConfig' " := ( URState (U:= LocalState ) LocalState_ι_TonsConfig ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplqueue_OrderInfouint128' " := ( ULState (U:= LocalState ) LocalState_ι_tplqueue_OrderInfouint128 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplqueue_OrderInfouint128' " := ( URState (U:= LocalState ) LocalState_ι_tplqueue_OrderInfouint128 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.addr_std_fixed' " := ( ULState (U:= LocalState ) LocalState_ι_addr_std_fixed ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.addr_std_fixed' " := ( URState (U:= LocalState ) LocalState_ι_addr_std_fixed ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.Grams' " := ( ULState (U:= LocalState ) LocalState_ι_Grams ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.Grams' " := ( URState (U:= LocalState ) LocalState_ι_Grams ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.SellArgs' " := ( ULState (U:= LocalState ) LocalState_ι_SellArgs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.SellArgs' " := ( URState (U:= LocalState ) LocalState_ι_SellArgs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.address' " := ( ULState (U:= LocalState ) LocalState_ι_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.address' " := ( URState (U:= LocalState ) LocalState_ι_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.DetailsInfo' " := ( ULState (U:= LocalState ) LocalState_ι_DetailsInfo ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.DetailsInfo' " := ( URState (U:= LocalState ) LocalState_ι_DetailsInfo ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.dict_arrayOrderInfo' " := ( ULState (U:= LocalState ) LocalState_ι_dict_arrayOrderInfo ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.dict_arrayOrderInfo' " := ( URState (U:= LocalState ) LocalState_ι_dict_arrayOrderInfo ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.optaddress' " := ( ULState (U:= LocalState ) LocalState_ι_optaddress ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.optaddress' " := ( URState (U:= LocalState ) LocalState_ι_optaddress ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TONTokenWallet' " := ( ULState (U:= LocalState ) LocalState_ι_TONTokenWallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TONTokenWallet' " := ( URState (U:= LocalState ) LocalState_ι_TONTokenWallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tpladdressGrams' " := ( ULState (U:= LocalState ) LocalState_ι_tpladdressGrams ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tpladdressGrams' " := ( URState (U:= LocalState ) LocalState_ι_tpladdressGrams ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TvmSlice' " := ( ULState (U:= LocalState ) LocalState_ι_TvmSlice ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TvmSlice' " := ( URState (U:= LocalState ) LocalState_ι_TvmSlice ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.optOrderRet' " := ( ULState (U:= LocalState ) LocalState_ι_optOrderRet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.optOrderRet' " := ( URState (U:= LocalState ) LocalState_ι_optOrderRet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.cellIndex' " := ( ULState (U:= LocalState ) LocalState_ι_cellIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.cellIndex' " := ( URState (U:= LocalState ) LocalState_ι_cellIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.StateInitIndex' " := ( ULState (U:= LocalState ) LocalState_ι_StateInitIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.StateInitIndex' " := ( URState (U:= LocalState ) LocalState_ι_StateInitIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInituint256Index' " := ( ULState (U:= LocalState ) LocalState_ι_tplStateInituint256Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInituint256Index' " := ( URState (U:= LocalState ) LocalState_ι_tplStateInituint256Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.boolIndex' " := ( ULState (U:= LocalState ) LocalState_ι_boolIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.boolIndex' " := ( URState (U:= LocalState ) LocalState_ι_boolIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint32Index' " := ( ULState (U:= LocalState ) LocalState_ι_uint32Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint32Index' " := ( URState (U:= LocalState ) LocalState_ι_uint32Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.PriceIndex' " := ( ULState (U:= LocalState ) LocalState_ι_PriceIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.PriceIndex' " := ( URState (U:= LocalState ) LocalState_ι_PriceIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.optuint128Index' " := ( ULState (U:= LocalState ) LocalState_ι_optuint128Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.optuint128Index' " := ( URState (U:= LocalState ) LocalState_ι_optuint128Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint128Index' " := ( ULState (U:= LocalState ) LocalState_ι_uint128Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint128Index' " := ( URState (U:= LocalState ) LocalState_ι_uint128Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplboolboolIndex' " := ( ULState (U:= LocalState ) LocalState_ι_tplboolboolIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplboolboolIndex' " := ( URState (U:= LocalState ) LocalState_ι_tplboolboolIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.OrderInfoIndex' " := ( ULState (U:= LocalState ) LocalState_ι_OrderInfoIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.OrderInfoIndex' " := ( URState (U:= LocalState ) LocalState_ι_OrderInfoIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.intIndex' " := ( ULState (U:= LocalState ) LocalState_ι_intIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.intIndex' " := ( URState (U:= LocalState ) LocalState_ι_intIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex' " := ( ULState (U:= LocalState ) LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex' " := ( URState (U:= LocalState ) LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.optpair_unsigned_OrderInfo__Index' " := ( ULState (U:= LocalState ) LocalState_ι_optpair_unsigned_OrderInfo__Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.optpair_unsigned_OrderInfo__Index' " := ( URState (U:= LocalState ) LocalState_ι_optpair_unsigned_OrderInfo__Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.queueOrderInfoIndex' " := ( ULState (U:= LocalState ) LocalState_ι_queueOrderInfoIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.queueOrderInfoIndex' " := ( URState (U:= LocalState ) LocalState_ι_queueOrderInfoIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.OrderRetIndex' " := ( ULState (U:= LocalState ) LocalState_ι_OrderRetIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.OrderRetIndex' " := ( URState (U:= LocalState ) LocalState_ι_OrderRetIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.unsignedIndex' " := ( ULState (U:= LocalState ) LocalState_ι_unsignedIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.unsignedIndex' " := ( URState (U:= LocalState ) LocalState_ι_unsignedIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.dealerIndex' " := ( ULState (U:= LocalState ) LocalState_ι_dealerIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.dealerIndex' " := ( URState (U:= LocalState ) LocalState_ι_dealerIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.process_retIndex' " := ( ULState (U:= LocalState ) LocalState_ι_process_retIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.process_retIndex' " := ( URState (U:= LocalState ) LocalState_ι_process_retIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint8Index' " := ( ULState (U:= LocalState ) LocalState_ι_uint8Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint8Index' " := ( URState (U:= LocalState ) LocalState_ι_uint8Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TonsConfigIndex' " := ( ULState (U:= LocalState ) LocalState_ι_TonsConfigIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TonsConfigIndex' " := ( URState (U:= LocalState ) LocalState_ι_TonsConfigIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplqueue_OrderInfouint128Index' " := ( ULState (U:= LocalState ) LocalState_ι_tplqueue_OrderInfouint128Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplqueue_OrderInfouint128Index' " := ( URState (U:= LocalState ) LocalState_ι_tplqueue_OrderInfouint128Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.addr_std_fixedIndex' " := ( ULState (U:= LocalState ) LocalState_ι_addr_std_fixedIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.addr_std_fixedIndex' " := ( URState (U:= LocalState ) LocalState_ι_addr_std_fixedIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.GramsIndex' " := ( ULState (U:= LocalState ) LocalState_ι_GramsIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.GramsIndex' " := ( URState (U:= LocalState ) LocalState_ι_GramsIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.SellArgsIndex' " := ( ULState (U:= LocalState ) LocalState_ι_SellArgsIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.SellArgsIndex' " := ( URState (U:= LocalState ) LocalState_ι_SellArgsIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.addressIndex' " := ( ULState (U:= LocalState ) LocalState_ι_addressIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.addressIndex' " := ( URState (U:= LocalState ) LocalState_ι_addressIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.DetailsInfoIndex' " := ( ULState (U:= LocalState ) LocalState_ι_DetailsInfoIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.DetailsInfoIndex' " := ( URState (U:= LocalState ) LocalState_ι_DetailsInfoIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.dict_arrayOrderInfoIndex' " := ( ULState (U:= LocalState ) LocalState_ι_dict_arrayOrderInfoIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.dict_arrayOrderInfoIndex' " := ( URState (U:= LocalState ) LocalState_ι_dict_arrayOrderInfoIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.optaddressIndex' " := ( ULState (U:= LocalState ) LocalState_ι_optaddressIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.optaddressIndex' " := ( URState (U:= LocalState ) LocalState_ι_optaddressIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TONTokenWalletIndex' " := ( ULState (U:= LocalState ) LocalState_ι_TONTokenWalletIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TONTokenWalletIndex' " := ( URState (U:= LocalState ) LocalState_ι_TONTokenWalletIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tpladdressGramsIndex' " := ( ULState (U:= LocalState ) LocalState_ι_tpladdressGramsIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tpladdressGramsIndex' " := ( URState (U:= LocalState ) LocalState_ι_tpladdressGramsIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TvmSliceIndex' " := ( ULState (U:= LocalState ) LocalState_ι_TvmSliceIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TvmSliceIndex' " := ( URState (U:= LocalState ) LocalState_ι_TvmSliceIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.optOrderRetIndex' " := ( ULState (U:= LocalState ) LocalState_ι_optOrderRetIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.optOrderRetIndex' " := ( URState (U:= LocalState ) LocalState_ι_optOrderRetIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Ledger.Price' " := ( ULState (U:= Ledger ) Ledger_ι_Price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Ledger.Price' " := ( URState (U:= Ledger ) Ledger_ι_Price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Ledger.VMState' " := ( ULState (U:= Ledger ) Ledger_ι_VMState ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Ledger.VMState' " := ( URState (U:= Ledger ) Ledger_ι_VMState ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Ledger.LocalState' " := ( ULState (U:= Ledger ) Ledger_ι_LocalState ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Ledger.LocalState' " := ( URState (U:= Ledger ) Ledger_ι_LocalState ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Ledger.LocalStateCopy' " := ( ULState (U:= Ledger ) Ledger_ι_LocalStateCopy ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Ledger.LocalStateCopy' " := ( URState (U:= Ledger ) Ledger_ι_LocalStateCopy ) (in custom URValue at level 0) : ursus_scope.

 Definition Ф_calc_cost_call { a1 a2 }  ( amount : URValue XInteger128 a1 ) ( price : URValue XInteger128 a2 ) : LedgerT ( ControlResult ( XMaybe XInteger128 )  ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_calc_cost 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} ( amount ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} ( price ) ) 
 . 
 Notation " 'Ф_calc_cost_ref_' '(' amount price ')' " := 
 ( URResult ( Ф_calc_cost_call 
 amount price )) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom ULValue at level 0 ) : ursus_scope . 
 
 Definition dealer_Ф_make_deal_call { a1 a2 }  ( sell : URValue OrderInfo a1 ) ( buy : URValue OrderInfo a2 ) : LedgerT ( ControlResult ( XBool # XBool # XInteger128 )%sol  ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) dealer_Ф_make_deal 
 ( SimpleLedgerableArg URValue {{ Λ "sell" }} ( sell ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "buy" }} ( buy ) ) 
 . 
 Notation " 'dealer_Ф_make_deal_ref_' '(' sell buy ')' " := 
 ( URResult ( dealer_Ф_make_deal_call 
 sell buy )) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , buy custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Ф_is_active_time_call { a1 }  ( order_finish_time : URValue XInteger32 a1 ) : LedgerT ( ControlResult XBool a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Ф_is_active_time 
 ( SimpleLedgerableArg URValue {{ Λ "order_finish_time" }} ( order_finish_time ) ) 
 . 
 Notation " 'Ф_is_active_time_ref_' '(' order_finish_time ')' " := 
 ( URResult ( Ф_is_active_time_call 
 order_finish_time )) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope . 
 
 (* Definition dealer_Ф_extract_active_order_call { a1 a2 a3 a4 } 
 ( cur_order : URValue (XMaybe (XInteger # OrderInfo)%sol) a1 ) ( orders : URValue ( XList OrderInfo ) a2 )
 ( all_amount : URValue XInteger128 a3 ) ( sell : URValue XBool a4 ) 
: LedgerT ( ControlResult (XMaybe (XInteger # OrderInfo) # (XList OrderInfo) # XInteger128) (orb (orb (orb a4 a3) a2) a1) ) := 

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
  *)
 
 Definition Price_Ф_processQueue_call  : LedgerT ( ControlResult PhantomType false) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_processQueue 
 . 
 Notation " 'Price_Ф_processQueue_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_processQueue_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition dealer_Ф_process_queue_call { a1 a2 }  ( sell_idx : URValue XInteger a1 ) ( buy_idx : URValue XInteger a2 ) : LedgerT ( ControlResult PhantomType ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) dealer_Ф_process_queue 
 ( SimpleLedgerableArg URValue {{ Λ "sell_idx" }} ( sell_idx ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "buy_idx" }} ( buy_idx ) ) 
 . 
 Notation " 'dealer_Ф_process_queue_ref_' '(' sell_idx buy_idx ')' " := 
 ( FuncallExpression ( dealer_Ф_process_queue_call 
 sell_idx buy_idx )) 
 (in custom ULValue at level 0 , sell_idx custom ULValue at level 0 
 , buy_idx custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_onTip3LendOwnershipMinValue_call  : LedgerT ( ControlResult XInteger128 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_onTip3LendOwnershipMinValue 
 . 
 Notation " 'Price_Ф_onTip3LendOwnershipMinValue_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_onTip3LendOwnershipMinValue_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_expected_wallet_address_call { a1 a2 }  ( wallet_pubkey : URValue XInteger256 a1 ) ( internal_owner : URValue XInteger256 a2 ) : LedgerT ( ControlResult XInteger256 ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Price_Ф_expected_wallet_address 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_pubkey" }} ( wallet_pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} ( internal_owner ) ) 
 . 
 Notation " 'Price_Ф_expected_wallet_address_ref_' '(' wallet_pubkey internal_owner ')' " := 
 ( URResult ( Price_Ф_expected_wallet_address_call 
 wallet_pubkey internal_owner )) 
 (in custom URValue at level 0 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_verify_tip3_addr_call { a1 a2 a3 }  ( tip3_wallet : URValue XAddress a1 )
 ( wallet_pubkey : URValue XInteger256 a2 ) ( internal_owner : URValue XInteger256 a3 ) 
: LedgerT ( ControlResult XBool ( orb ( orb a3 a2 ) a1 ) ) := 

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
 
 Definition Price_Ф_on_sell_fail_call { a1 a2 }  ( ec : URValue XInteger a1 ) 
( wallet_in : URValue ITONTokenWalletPtr a2 ) : LedgerT ( ControlResult OrderRet ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Price_Ф_on_sell_fail 
 ( SimpleLedgerableArg URValue {{ Λ "ec" }} ( ec ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_in" }} ( wallet_in ) ) 
 . 
 Notation " 'Price_Ф_on_sell_fail_ref_' '(' ec wallet_in ')' " := 
 ( URResult ( Price_Ф_on_sell_fail_call 
 ec wallet_in )) 
 (in custom URValue at level 0 , ec custom URValue at level 0 
 , wallet_in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_onTip3LendOwnership_call { a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue XAddress a1 )
 ( balance : URValue XInteger128 a2 ) ( lend_finish_time : URValue XInteger32 a3 ) 
( pubkey : URValue XInteger256 a4 ) ( internal_owner : URValue XAddress a5 ) 
( payload : URValue TvmCell a6 ) : LedgerT ( ControlResult OrderRet ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4) a3) a2) a1) ) := 

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
 
 Definition Price_Ф_buyTip3MinValue_call { a1 }  ( buy_cost : URValue XInteger128 a1 ) : LedgerT ( ControlResult XInteger128 a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Price_Ф_buyTip3MinValue 
 ( SimpleLedgerableArg URValue {{ Λ "buy_cost" }} ( buy_cost ) ) 
 . 
 Notation " 'Price_Ф_buyTip3MinValue_ref_' '(' buy_cost ')' " := 
 ( URResult ( Price_Ф_buyTip3MinValue_call 
 buy_cost )) 
 (in custom URValue at level 0 , buy_cost custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_buyTip3_call { a1 a2 a3 }  ( amount : URValue XInteger128 a1 ) 
( receive_tip3_wallet : URValue XAddress a2 ) ( order_finish_time : URValue XInteger32 a3 ) 
: LedgerT ( ControlResult OrderRet true ) := 

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
 
 Definition Ф_cancel_order_impl_call { a1 a2 a3 a4 a5 a6 a7 }  ( orders : URValue ( XList OrderInfo ) a1 ) 
( client_addr : URValue addr_std_fixed a2 ) ( all_amount : URValue XInteger128 a3 ) 
( sell : URValue XBool a4 ) ( return_ownership : URValue Grams a5 ) ( process_queue : URValue Grams a6 )
 ( incoming_val : URValue Grams a7 ) : 
LedgerT ( ControlResult ( XList OrderInfo )  ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5) a4) a3) a2) a1) ) := 

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
 
 Definition Price_Ф_cancelSell_call  : LedgerT ( ControlResult PhantomType false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_cancelSell 
 . 
 Notation " 'Price_Ф_cancelSell_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_cancelSell_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_cancelBuy_call  : LedgerT ( ControlResult PhantomType false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_cancelBuy 
 . 
 Notation " 'Price_Ф_cancelBuy_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_cancelBuy_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getPrice_call  : LedgerT ( ControlResult XInteger128 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getPrice 
 . 
 Notation " 'Price_Ф_getPrice_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getPrice_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getMinimumAmount_call  : LedgerT ( ControlResult XInteger128 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getMinimumAmount 
 . 
 Notation " 'Price_Ф_getMinimumAmount_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getMinimumAmount_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getSellAmount_call  : LedgerT ( ControlResult XInteger128 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getSellAmount 
 . 
 Notation " 'Price_Ф_getSellAmount_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getSellAmount_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getBuyAmount_call  : LedgerT ( ControlResult XInteger128 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getBuyAmount 
 . 
 Notation " 'Price_Ф_getBuyAmount_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getBuyAmount_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getDetails_call  : LedgerT ( ControlResult DetailsInfo false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getDetails 
 . 
 Notation " 'Price_Ф_getDetails_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getDetails_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getTonsCfg_call  : LedgerT ( ControlResult TonsConfig false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getTonsCfg 
 . 
 Notation " 'Price_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getTonsCfg_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getSells_call  : LedgerT ( ControlResult ( XHMap XInteger OrderInfo ) false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getSells 
 . 
 Notation " 'Price_Ф_getSells_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getSells_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф_getBuys_call  : LedgerT ( ControlResult ( XHMap XInteger OrderInfo) false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getBuys 
 . 
 Notation " 'Price_Ф_getBuys_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getBuys_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition Price_Ф__fallback_call { a1 } ( xx : URValue TvmCell a1 ) : LedgerT ( ControlResult XInteger a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Price_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "xx" }} ( xx ) ) 
 . 
 Notation " 'Price_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( Price_Ф__fallback_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope . 


End PriceFuncNotations .


