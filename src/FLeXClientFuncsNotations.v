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
Require Import UMLang.SML_NG28.

Require Import FLeXContractTypes.

Require Import FLeXClientClass.
Require Import FLeXClientSpecs.
Require Import FLeXConstSig. 
Require Import UrsusStdLib.stdFunc.

Module FLeXClientFuncNotations (xt: XTypesSig) 
                          (sm: StateMonadSig) 
                          (dc : FLeXConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

Module Export specFlexSpec := specFlexClientSpec xt sm.
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





 Parameter FlexClient_Ф_constructor : XInteger256 -> TvmCell -> TvmCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setFlexCfg : TonsConfig -> addr_std_compact -> addr_std_compact -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setExtWalletCode : TvmCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setFlexWalletCode : TvmCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_setFlexWrapperCode : TvmCell -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_deployTradingPair : addr_std_compact -> XInteger128 -> XInteger128 -> XInteger128 -> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployXchgPair : addr_std_compact -> addr_std_compact -> XInteger128 -> XInteger128 -> XInteger128 -> UExpression XAddress true . 
 Parameter FlexClient_Ф_preparePrice : XInteger128 -> XInteger128 -> XInteger8 -> TvmCell -> Tip3Config -> TvmCell -> UExpression ( StateInit # XAddress # XInteger256 ) false . 
 Parameter FlexClient_Ф_deployPriceWithSell : XInteger128 -> XInteger128 -> XInteger32 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> addr_std_compact -> addr_std_compact -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployPriceWithBuy : XInteger128 -> XInteger128 -> XInteger32 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> addr_std_compact -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_cancelSellOrder : XInteger128 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> Tip3Config -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_cancelBuyOrder : XInteger128 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> Tip3Config -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_preparePriceXchg : XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> Tip3Config -> Tip3Config -> TvmCell -> UExpression ( StateInit # XAddress # XInteger256 ) false . 
 Parameter FlexClient_Ф_cancelXchgOrder : XBool -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> Tip3Config -> Tip3Config -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_transfer : addr_std_compact -> XInteger128 -> XBool -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_deployPriceXchg : XBool -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger32 -> XInteger128 -> XInteger8 -> XInteger128 -> TvmCell -> addr_std_compact -> addr_std_compact -> Tip3Config -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployWrapperWithWallet : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_deployEmptyFlexWallet : XInteger256 -> XInteger128 -> Tip3Config -> UExpression XAddress true . 
 Parameter FlexClient_Ф_burnWallet : XInteger128 -> XInteger256 -> addr_std_compact -> addr_std_compact -> UExpression PhantomType true . 
 Parameter FlexClient_Ф_getOwner : UExpression XInteger256 false . 
 Parameter FlexClient_Ф_getFlex : UExpression XAddress false . 
 Parameter FlexClient_Ф_hasExtWalletCode : UExpression XBool false . 
 Parameter FlexClient_Ф_hasFlexWalletCode : UExpression XBool false . 
 Parameter FlexClient_Ф_hasFlexWrapperCode : UExpression XBool false . 
 Parameter FlexClient_Ф_getPayloadForDeployInternalWallet : XInteger256 -> addr_std_compact -> XInteger128 -> UExpression TvmCell false . 
 Parameter FlexClient_Ф__fallback : TvmCell -> UExpression XInteger false . 
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
 Notation " 'anycast_info.rewrite_pfx' " := ( ULState (U:= anycast_info ) anycast_info_ι_rewrite_pfx ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'anycast_info.rewrite_pfx' " := ( URState (U:= anycast_info ) anycast_info_ι_rewrite_pfx ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.kind' " := ( ULState (U:= addr_std ) addr_std_ι_kind ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.kind' " := ( URState (U:= addr_std ) addr_std_ι_kind ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.Anycast' " := ( ULState (U:= addr_std ) addr_std_ι_Anycast ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.Anycast' " := ( URState (U:= addr_std ) addr_std_ι_Anycast ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.workchain_id' " := ( ULState (U:= addr_std ) addr_std_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.workchain_id' " := ( URState (U:= addr_std ) addr_std_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std.address' " := ( ULState (U:= addr_std ) addr_std_ι_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std.address' " := ( URState (U:= addr_std ) addr_std_ι_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.workchain_id' " := ( ULState (U:= addr_std_fixed ) addr_std_fixed_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.workchain_id' " := ( URState (U:= addr_std_fixed ) addr_std_fixed_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.address' " := ( ULState (U:= addr_std_fixed ) addr_std_fixed_ι_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'addr_std_fixed.address' " := ( URState (U:= addr_std_fixed ) addr_std_fixed_ι_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'SellArgs.amount' " := ( ULState (U:= SellArgs ) SellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'SellArgs.amount' " := ( URState (U:= SellArgs ) SellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'SellArgs.receive_wallet' " := ( ULState (U:= SellArgs ) SellArgs_ι_receive_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'SellArgs.receive_wallet' " := ( URState (U:= SellArgs ) SellArgs_ι_receive_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.tons_value' " := ( ULState (U:= FlexBurnWalletArgs ) FlexBurnWalletArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.tons_value' " := ( URState (U:= FlexBurnWalletArgs ) FlexBurnWalletArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_pubkey' " := ( ULState (U:= FlexBurnWalletArgs ) FlexBurnWalletArgs_ι_out_pubkey ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_pubkey' " := ( URState (U:= FlexBurnWalletArgs ) FlexBurnWalletArgs_ι_out_pubkey ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_internal_owner' " := ( ULState (U:= FlexBurnWalletArgs ) FlexBurnWalletArgs_ι_out_internal_owner ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.out_internal_owner' " := ( URState (U:= FlexBurnWalletArgs ) FlexBurnWalletArgs_ι_out_internal_owner ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.my_tip3_addr' " := ( ULState (U:= FlexBurnWalletArgs ) FlexBurnWalletArgs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBurnWalletArgs.my_tip3_addr' " := ( URState (U:= FlexBurnWalletArgs ) FlexBurnWalletArgs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope.
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
 Notation " 'FlexClient.owner_' " := ( ULState (U:= FlexClient ) FlexClient_ι_owner_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.owner_' " := ( URState (U:= FlexClient ) FlexClient_ι_owner_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.trading_pair_code_' " := ( ULState (U:= FlexClient ) FlexClient_ι_trading_pair_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.trading_pair_code_' " := ( URState (U:= FlexClient ) FlexClient_ι_trading_pair_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.xchg_pair_code_' " := ( ULState (U:= FlexClient ) FlexClient_ι_xchg_pair_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.xchg_pair_code_' " := ( URState (U:= FlexClient ) FlexClient_ι_xchg_pair_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.workchain_id_' " := ( ULState (U:= FlexClient ) FlexClient_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.workchain_id_' " := ( URState (U:= FlexClient ) FlexClient_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.tons_cfg_' " := ( ULState (U:= FlexClient ) FlexClient_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.tons_cfg_' " := ( URState (U:= FlexClient ) FlexClient_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_' " := ( ULState (U:= FlexClient ) FlexClient_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_' " := ( URState (U:= FlexClient ) FlexClient_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.notify_addr_' " := ( ULState (U:= FlexClient ) FlexClient_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.notify_addr_' " := ( URState (U:= FlexClient ) FlexClient_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.ext_wallet_code_' " := ( ULState (U:= FlexClient ) FlexClient_ι_ext_wallet_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.ext_wallet_code_' " := ( URState (U:= FlexClient ) FlexClient_ι_ext_wallet_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wallet_code_' " := ( ULState (U:= FlexClient ) FlexClient_ι_flex_wallet_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wallet_code_' " := ( URState (U:= FlexClient ) FlexClient_ι_flex_wallet_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wrapper_code_' " := ( ULState (U:= FlexClient ) FlexClient_ι_flex_wrapper_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexClient.flex_wrapper_code_' " := ( URState (U:= FlexClient ) FlexClient_ι_flex_wrapper_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgsAddrs.my_tip3_addr' " := ( ULState (U:= FlexSellArgsAddrs ) FlexSellArgsAddrs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgsAddrs.my_tip3_addr' " := ( URState (U:= FlexSellArgsAddrs ) FlexSellArgsAddrs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.amount' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.amount' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.lend_finish_time' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.lend_finish_time' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.min_amount' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.min_amount' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.deals_limit' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.deals_limit' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tons_value' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tons_value' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price_code' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.price_code' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.addrs' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_addrs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.addrs' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_addrs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3_code' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3_code' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3cfg' " := ( ULState (U:= FlexSellArgs ) FlexSellArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexSellArgs.tip3cfg' " := ( URState (U:= FlexSellArgs ) FlexSellArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.amount' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.amount' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.order_finish_time' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.order_finish_time' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.min_amount' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.min_amount' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deals_limit' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deals_limit' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deploy_value' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_deploy_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.deploy_value' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_deploy_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price_code' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.price_code' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.my_tip3_addr' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_my_tip3_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.my_tip3_addr' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_my_tip3_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3_code' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3_code' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3cfg' " := ( ULState (U:= FlexBuyArgs ) FlexBuyArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexBuyArgs.tip3cfg' " := ( URState (U:= FlexBuyArgs ) FlexBuyArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.major_tip3cfg' " := ( ULState (U:= FlexXchgCfgs ) FlexXchgCfgs_ι_major_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.major_tip3cfg' " := ( URState (U:= FlexXchgCfgs ) FlexXchgCfgs_ι_major_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.minor_tip3cfg' " := ( ULState (U:= FlexXchgCfgs ) FlexXchgCfgs_ι_minor_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCfgs.minor_tip3cfg' " := ( URState (U:= FlexXchgCfgs ) FlexXchgCfgs_ι_minor_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.sell' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.sell' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_num' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_price_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_num' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_price_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_denum' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_price_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.price_denum' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_price_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.amount' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.amount' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_amount' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_lend_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_amount' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_lend_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_finish_time' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.lend_finish_time' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.min_amount' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.min_amount' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.deals_limit' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.deals_limit' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tons_value' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_tons_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tons_value' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_tons_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.xchg_price_code' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.xchg_price_code' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_xchg_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.addrs' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_addrs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.addrs' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_addrs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3_code' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3_code' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3cfgs' " := ( ULState (U:= FlexXchgArgs ) FlexXchgArgs_ι_tip3cfgs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgArgs.tip3cfgs' " := ( URState (U:= FlexXchgArgs ) FlexXchgArgs_ι_tip3cfgs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price' " := ( ULState (U:= FlexCancelArgs ) FlexCancelArgs_ι_price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price' " := ( URState (U:= FlexCancelArgs ) FlexCancelArgs_ι_price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.min_amount' " := ( ULState (U:= FlexCancelArgs ) FlexCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.min_amount' " := ( URState (U:= FlexCancelArgs ) FlexCancelArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.deals_limit' " := ( ULState (U:= FlexCancelArgs ) FlexCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.deals_limit' " := ( URState (U:= FlexCancelArgs ) FlexCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.value' " := ( ULState (U:= FlexCancelArgs ) FlexCancelArgs_ι_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.value' " := ( URState (U:= FlexCancelArgs ) FlexCancelArgs_ι_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price_code' " := ( ULState (U:= FlexCancelArgs ) FlexCancelArgs_ι_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.price_code' " := ( URState (U:= FlexCancelArgs ) FlexCancelArgs_ι_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3_code' " := ( ULState (U:= FlexCancelArgs ) FlexCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3_code' " := ( URState (U:= FlexCancelArgs ) FlexCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3cfg' " := ( ULState (U:= FlexCancelArgs ) FlexCancelArgs_ι_tip3cfg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexCancelArgs.tip3cfg' " := ( URState (U:= FlexCancelArgs ) FlexCancelArgs_ι_tip3cfg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.sell' " := ( ULState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.sell' " := ( URState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_num' " := ( ULState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_price_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_num' " := ( URState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_price_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_denum' " := ( ULState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_price_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.price_denum' " := ( URState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_price_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.min_amount' " := ( ULState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.min_amount' " := ( URState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_min_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.deals_limit' " := ( ULState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_deals_limit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.deals_limit' " := ( URState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_deals_limit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.value' " := ( ULState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_value ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.value' " := ( URState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_value ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.xchg_price_code' " := ( ULState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_xchg_price_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.xchg_price_code' " := ( URState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_xchg_price_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3_code' " := ( ULState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_tip3_code ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3_code' " := ( URState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_tip3_code ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3cfgs' " := ( ULState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_tip3cfgs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexXchgCancelArgs.tip3cfgs' " := ( URState (U:= FlexXchgCancelArgs ) FlexXchgCancelArgs_ι_tip3cfgs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.flex_addr_' " := ( ULState (U:= XchgPair ) XchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.flex_addr_' " := ( URState (U:= XchgPair ) XchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_major_root_' " := ( ULState (U:= XchgPair ) XchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_major_root_' " := ( URState (U:= XchgPair ) XchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_minor_root_' " := ( ULState (U:= XchgPair ) XchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.tip3_minor_root_' " := ( URState (U:= XchgPair ) XchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'XchgPair.deploy_value_' " := ( ULState (U:= XchgPair ) XchgPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'XchgPair.deploy_value_' " := ( URState (U:= XchgPair ) XchgPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope.
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
 Notation " 'RationalPrice.num' " := ( ULState (U:= RationalPrice ) RationalPrice_ι_num ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.num' " := ( URState (U:= RationalPrice ) RationalPrice_ι_num ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.denum' " := ( ULState (U:= RationalPrice ) RationalPrice_ι_denum ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'RationalPrice.denum' " := ( URState (U:= RationalPrice ) RationalPrice_ι_denum ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.price_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_price_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.price_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_price_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.sells_amount_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.sells_amount_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.buys_amount_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.buys_amount_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.flex_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_flex_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.flex_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_flex_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.min_amount_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.min_amount_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.deals_limit_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.deals_limit_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.notify_addr_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.notify_addr_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.workchain_id_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.workchain_id_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tons_cfg_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tons_cfg_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tip3_code_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_tip3_code_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.tip3_code_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_tip3_code_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.major_tip3cfg_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_major_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.major_tip3cfg_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_major_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( ULState (U:= PriceXchg ) PriceXchg_ι_minor_tip3cfg_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PriceXchg.minor_tip3cfg_' " := ( URState (U:= PriceXchg ) PriceXchg_ι_minor_tip3cfg_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TradingPair.flex_addr_' " := ( ULState (U:= TradingPair ) TradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TradingPair.flex_addr_' " := ( URState (U:= TradingPair ) TradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TradingPair.tip3_root_' " := ( ULState (U:= TradingPair ) TradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TradingPair.tip3_root_' " := ( URState (U:= TradingPair ) TradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TradingPair.deploy_value_' " := ( ULState (U:= TradingPair ) TradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TradingPair.deploy_value_' " := ( URState (U:= TradingPair ) TradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.sell' " := ( ULState (U:= PayloadArgs ) PayloadArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.sell' " := ( URState (U:= PayloadArgs ) PayloadArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.amount' " := ( ULState (U:= PayloadArgs ) PayloadArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.amount' " := ( URState (U:= PayloadArgs ) PayloadArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( ULState (U:= PayloadArgs ) PayloadArgs_ι_receive_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( URState (U:= PayloadArgs ) PayloadArgs_ι_receive_tip3_wallet ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.client_addr' " := ( ULState (U:= PayloadArgs ) PayloadArgs_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'PayloadArgs.client_addr' " := ( URState (U:= PayloadArgs ) PayloadArgs_ι_client_addr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint256' " := ( ULState (U:= LocalState ) LocalState_ι_uint256 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint256' " := ( URState (U:= LocalState ) LocalState_ι_uint256 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.cell' " := ( ULState (U:= LocalState ) LocalState_ι_cell ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.cell' " := ( URState (U:= LocalState ) LocalState_ι_cell ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TonsConfig' " := ( ULState (U:= LocalState ) LocalState_ι_TonsConfig ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TonsConfig' " := ( URState (U:= LocalState ) LocalState_ι_TonsConfig ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.address' " := ( ULState (U:= LocalState ) LocalState_ι_address ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.address' " := ( URState (U:= LocalState ) LocalState_ι_address ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint128' " := ( ULState (U:= LocalState ) LocalState_ι_uint128 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint128' " := ( URState (U:= LocalState ) LocalState_ι_uint128 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TradingPair' " := ( ULState (U:= LocalState ) LocalState_ι_TradingPair ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TradingPair' " := ( URState (U:= LocalState ) LocalState_ι_TradingPair ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInituint256' " := ( ULState (U:= LocalState ) LocalState_ι_tplStateInituint256 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInituint256' " := ( URState (U:= LocalState ) LocalState_ι_tplStateInituint256 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.StateInit' " := ( ULState (U:= LocalState ) LocalState_ι_StateInit ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.StateInit' " := ( URState (U:= LocalState ) LocalState_ι_StateInit ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.XchgPair' " := ( ULState (U:= LocalState ) LocalState_ι_XchgPair ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.XchgPair' " := ( URState (U:= LocalState ) LocalState_ι_XchgPair ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInitaddress' " := ( ULState (U:= LocalState ) LocalState_ι_tplStateInitaddress ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInitaddress' " := ( URState (U:= LocalState ) LocalState_ι_tplStateInitaddress ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.SellArgs' " := ( ULState (U:= LocalState ) LocalState_ι_SellArgs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.SellArgs' " := ( URState (U:= LocalState ) LocalState_ι_SellArgs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.ITONTokenWalletPtr' " := ( ULState (U:= LocalState ) LocalState_ι_ITONTokenWalletPtr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.ITONTokenWalletPtr' " := ( URState (U:= LocalState ) LocalState_ι_ITONTokenWalletPtr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.IPricePtr' " := ( ULState (U:= LocalState ) LocalState_ι_IPricePtr ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.IPricePtr' " := ( URState (U:= LocalState ) LocalState_ι_IPricePtr ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.int' " := ( ULState (U:= LocalState ) LocalState_ι_int ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.int' " := ( URState (U:= LocalState ) LocalState_ι_int ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.Price' " := ( ULState (U:= LocalState ) LocalState_ι_Price ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.Price' " := ( URState (U:= LocalState ) LocalState_ι_Price ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint8' " := ( ULState (U:= LocalState ) LocalState_ι_uint8 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint8' " := ( URState (U:= LocalState ) LocalState_ι_uint8 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint32' " := ( ULState (U:= LocalState ) LocalState_ι_uint32 ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint32' " := ( URState (U:= LocalState ) LocalState_ι_uint32 ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.Tip3Config' " := ( ULState (U:= LocalState ) LocalState_ι_Tip3Config ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.Tip3Config' " := ( URState (U:= LocalState ) LocalState_ι_Tip3Config ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.PriceXchg' " := ( ULState (U:= LocalState ) LocalState_ι_PriceXchg ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.PriceXchg' " := ( URState (U:= LocalState ) LocalState_ι_PriceXchg ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.PayloadArgs' " := ( ULState (U:= LocalState ) LocalState_ι_PayloadArgs ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.PayloadArgs' " := ( URState (U:= LocalState ) LocalState_ι_PayloadArgs ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint256Index' " := ( ULState (U:= LocalState ) LocalState_ι_uint256Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint256Index' " := ( URState (U:= LocalState ) LocalState_ι_uint256Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.cellIndex' " := ( ULState (U:= LocalState ) LocalState_ι_cellIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.cellIndex' " := ( URState (U:= LocalState ) LocalState_ι_cellIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TonsConfigIndex' " := ( ULState (U:= LocalState ) LocalState_ι_TonsConfigIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TonsConfigIndex' " := ( URState (U:= LocalState ) LocalState_ι_TonsConfigIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.addressIndex' " := ( ULState (U:= LocalState ) LocalState_ι_addressIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.addressIndex' " := ( URState (U:= LocalState ) LocalState_ι_addressIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint128Index' " := ( ULState (U:= LocalState ) LocalState_ι_uint128Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint128Index' " := ( URState (U:= LocalState ) LocalState_ι_uint128Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.TradingPairIndex' " := ( ULState (U:= LocalState ) LocalState_ι_TradingPairIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.TradingPairIndex' " := ( URState (U:= LocalState ) LocalState_ι_TradingPairIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInituint256Index' " := ( ULState (U:= LocalState ) LocalState_ι_tplStateInituint256Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInituint256Index' " := ( URState (U:= LocalState ) LocalState_ι_tplStateInituint256Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.StateInitIndex' " := ( ULState (U:= LocalState ) LocalState_ι_StateInitIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.StateInitIndex' " := ( URState (U:= LocalState ) LocalState_ι_StateInitIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.XchgPairIndex' " := ( ULState (U:= LocalState ) LocalState_ι_XchgPairIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.XchgPairIndex' " := ( URState (U:= LocalState ) LocalState_ι_XchgPairIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInitaddressIndex' " := ( ULState (U:= LocalState ) LocalState_ι_tplStateInitaddressIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.tplStateInitaddressIndex' " := ( URState (U:= LocalState ) LocalState_ι_tplStateInitaddressIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.SellArgsIndex' " := ( ULState (U:= LocalState ) LocalState_ι_SellArgsIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.SellArgsIndex' " := ( URState (U:= LocalState ) LocalState_ι_SellArgsIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.ITONTokenWalletPtrIndex' " := ( ULState (U:= LocalState ) LocalState_ι_ITONTokenWalletPtrIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.ITONTokenWalletPtrIndex' " := ( URState (U:= LocalState ) LocalState_ι_ITONTokenWalletPtrIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.IPricePtrIndex' " := ( ULState (U:= LocalState ) LocalState_ι_IPricePtrIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.IPricePtrIndex' " := ( URState (U:= LocalState ) LocalState_ι_IPricePtrIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.intIndex' " := ( ULState (U:= LocalState ) LocalState_ι_intIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.intIndex' " := ( URState (U:= LocalState ) LocalState_ι_intIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.PriceIndex' " := ( ULState (U:= LocalState ) LocalState_ι_PriceIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.PriceIndex' " := ( URState (U:= LocalState ) LocalState_ι_PriceIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint8Index' " := ( ULState (U:= LocalState ) LocalState_ι_uint8Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint8Index' " := ( URState (U:= LocalState ) LocalState_ι_uint8Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint32Index' " := ( ULState (U:= LocalState ) LocalState_ι_uint32Index ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.uint32Index' " := ( URState (U:= LocalState ) LocalState_ι_uint32Index ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.Tip3ConfigIndex' " := ( ULState (U:= LocalState ) LocalState_ι_Tip3ConfigIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.Tip3ConfigIndex' " := ( URState (U:= LocalState ) LocalState_ι_Tip3ConfigIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.PriceXchgIndex' " := ( ULState (U:= LocalState ) LocalState_ι_PriceXchgIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.PriceXchgIndex' " := ( URState (U:= LocalState ) LocalState_ι_PriceXchgIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'LocalState.PayloadArgsIndex' " := ( ULState (U:= LocalState ) LocalState_ι_PayloadArgsIndex ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'LocalState.PayloadArgsIndex' " := ( URState (U:= LocalState ) LocalState_ι_PayloadArgsIndex ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Ledger.FLeXClient' " := ( ULState (U:= Ledger ) Ledger_ι_FlexClient ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Ledger.FLeXClient' " := ( URState (U:= Ledger ) Ledger_ι_FlexClient ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Ledger.VMState' " := ( ULState (U:= Ledger ) Ledger_ι_VMState ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Ledger.VMState' " := ( URState (U:= Ledger ) Ledger_ι_VMState ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Ledger.LocalState' " := ( ULState (U:= Ledger ) Ledger_ι_LocalState ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Ledger.LocalState' " := ( URState (U:= Ledger ) Ledger_ι_LocalState ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'Ledger.LocalStateCopy' " := ( ULState (U:= Ledger ) Ledger_ι_LocalStateCopy ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'Ledger.LocalStateCopy' " := ( URState (U:= Ledger ) Ledger_ι_LocalStateCopy ) (in custom URValue at level 0) : ursus_scope.

Notation " 'error_code::zero_owner_pubkey' " := (sInject error_code_ι_zero_owner_pubkey) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wallet_code' " := (sInject error_code_ι_missed_flex_wallet_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wrapper_code' " := (sInject error_code_ι_missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 
(*TODO*)
Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 


 Definition FlexClient_Ф_constructor_call { a1 a2 a3 }  ( pubkey : URValue XInteger256 a1 ) ( trading_pair_code : URValue TvmCell a2 ) ( xchg_pair_code : URValue TvmCell a3 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FlexClient_Ф_constructor 
 ( SimpleLedgerableArg URValue {{ Λ "pubkey" }} ( pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "trading_pair_code" }} ( trading_pair_code ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "xchg_pair_code" }} ( xchg_pair_code ) ) 
 . 
 Notation " 'FlexClient_Ф_constructor_ref_' '(' pubkey trading_pair_code xchg_pair_code ')' " := 
 ( FuncallExpression ( FlexClient_Ф_constructor_call 
 pubkey trading_pair_code xchg_pair_code )) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , trading_pair_code custom URValue at level 0 
 , xchg_pair_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_setFlexCfg_call { a1 a2 a3 }  ( tons_cfg : URValue TonsConfig a1 ) ( flex : URValue addr_std_compact a2 ) ( notify_addr : URValue addr_std_compact a3 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FlexClient_Ф_setFlexCfg 
 ( SimpleLedgerableArg URValue {{ Λ "tons_cfg" }} ( tons_cfg ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "flex" }} ( flex ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "notify_addr" }} ( notify_addr ) ) 
 . 
 Notation " 'FlexClient_Ф_setFlexCfg_ref_' '(' tons_cfg flex notify_addr ')' " := 
 ( FuncallExpression ( FlexClient_Ф_setFlexCfg_call 
 tons_cfg flex notify_addr )) 
 (in custom ULValue at level 0 , tons_cfg custom URValue at level 0 
 , flex custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_setExtWalletCode_call { a1 }  ( ext_wallet_code : URValue TvmCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FlexClient_Ф_setExtWalletCode 
 ( SimpleLedgerableArg URValue {{ Λ "ext_wallet_code" }} ( ext_wallet_code ) ) 
 . 
 Notation " 'FlexClient_Ф_setExtWalletCode_ref_' '(' ext_wallet_code ')' " := 
 ( FuncallExpression ( FlexClient_Ф_setExtWalletCode_call 
 ext_wallet_code )) 
 (in custom ULValue at level 0 , ext_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_setFlexWalletCode_call { a1 }  ( flex_wallet_code : URValue TvmCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FlexClient_Ф_setFlexWalletCode 
 ( SimpleLedgerableArg URValue {{ Λ "flex_wallet_code" }} ( flex_wallet_code ) ) 
 . 
 Notation " 'FlexClient_Ф_setFlexWalletCode_ref_' '(' flex_wallet_code ')' " := 
 ( FuncallExpression ( FlexClient_Ф_setFlexWalletCode_call 
 flex_wallet_code )) 
 (in custom ULValue at level 0 , flex_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_setFlexWrapperCode_call { a1 }  ( flex_wrapper_code : URValue TvmCell a1 ) : LedgerT ( ControlResult PhantomType true ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FlexClient_Ф_setFlexWrapperCode 
 ( SimpleLedgerableArg URValue {{ Λ "flex_wrapper_code" }} ( flex_wrapper_code ) ) 
 . 
 Notation " 'FlexClient_Ф_setFlexWrapperCode_ref_' '(' flex_wrapper_code ')' " := 
 ( FuncallExpression ( FlexClient_Ф_setFlexWrapperCode_call 
 flex_wrapper_code )) 
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
 tip3_root deploy_min_value deploy_value min_trade_amount )) 
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
 tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount )) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_preparePrice_call { a1 a2 a3 a4 a5 a6 }  ( price : URValue XInteger128 a1 ) ( min_amount : URValue XInteger128 a2 ) ( deals_limit : URValue XInteger8 a3 ) ( tip3_code : URValue TvmCell a4 ) ( tip3cfg : URValue Tip3Config a5 ) ( price_code : URValue TvmCell a6 ) : LedgerT ( ControlResult ( StateInit # XAddress # XInteger256 ) (orb (orb (orb (orb (orb a6 a5) a4) a3) a2) a1) ) := 
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
 price min_amount deals_limit tip3_code tip3cfg price_code )) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tip3_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , price_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_deployPriceWithSell_call { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  ( price : URValue XInteger128 a1 ) ( amount : URValue XInteger128 a2 ) ( lend_finish_time : URValue XInteger32 a3 ) ( min_amount : URValue XInteger128 a4 ) ( deals_limit : URValue XInteger8 a5 ) ( tons_value : URValue XInteger128 a6 ) ( price_code : URValue TvmCell a7 ) ( my_tip3_addr : URValue addr_std_compact a8 ) ( receive_wallet : URValue addr_std_compact a9 ) ( tip3cfg : URValue Tip3Config a10 ) : LedgerT ( ControlResult XAddress true ) := 
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
 price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg )) 
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
( price_code : URValue TvmCell a7 ) ( my_tip3_addr : URValue addr_std_compact a8 ) 
( tip3cfg : URValue Tip3Config a9 ) : LedgerT ( ControlResult XAddress true ) := 
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
 price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg )) 
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
 ( price_code : URValue TvmCell a5 ) ( tip3cfg : URValue Tip3Config a6 ) 
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
 price min_amount deals_limit value price_code tip3cfg )) 
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_cancelBuyOrder_call { a1 a2 a3 a4 a5 a6 }  ( price : URValue XInteger128 a1 ) 
( min_amount : URValue XInteger128 a2 ) ( deals_limit : URValue XInteger8 a3 ) 
( value : URValue XInteger128 a4 ) ( price_code : URValue TvmCell a5 ) 
( tip3cfg : URValue Tip3Config a6 ) : LedgerT ( ControlResult PhantomType true ) := 
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
 price min_amount deals_limit value price_code tip3cfg )) 
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_preparePriceXchg_call { a1 a2 a3 a4 a5 a6 a7 }  ( price_num : URValue XInteger128 a1 )
 ( price_denum : URValue XInteger128 a2 ) ( min_amount : URValue XInteger128 a3 )
 ( deals_limit : URValue XInteger8 a4 ) ( major_tip3cfg : URValue Tip3Config a5 ) 
( minor_tip3cfg : URValue Tip3Config a6 ) ( price_code : URValue TvmCell a7 ) 
: LedgerT ( ControlResult ( StateInit # XAddress # XInteger256 ) (orb (orb (orb (orb (orb (orb a7 a6) a5) a4) a3) a2) a1)) := 
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
 price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code )) 
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
( value : URValue XInteger128 a6 ) ( xchg_price_code : URValue TvmCell a7 ) 
( major_tip3cfg : URValue Tip3Config a8 ) ( minor_tip3cfg : URValue Tip3Config a9 ) 
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
 sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg )) 
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
 dest value bounce )) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 
 , value custom URValue at level 0 
 , bounce custom URValue at level 0 ) : ursus_scope . 
 
 (* Definition FlexClient_Ф_deployPriceXchg_call { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 } 
 ( sell : URValue XBool a1 ) ( price_num : URValue XInteger128 a2 ) 
( price_denum : URValue XInteger128 a3 ) ( amount : URValue XInteger128 a4 )
 ( lend_amount : URValue XInteger128 a5 ) ( lend_finish_time : URValue XInteger32 a6 )
 ( min_amount : URValue XInteger128 a7 ) ( deals_limit : URValue XInteger8 a8 ) 
( tons_value : URValue XInteger128 a9 ) ( xchg_price_code : URValue TvmCell a10 ) 
( my_tip3_addr : URValue addr_std_compact a11 ) ( receive_wallet : URValue addr_std_compact a12 ) 
( major_tip3cfg : URValue Tip3Config a13 ) ( minor_tip3cfg : URValue Tip3Config a14 ) 
: LedgerT ( ControlResult XAddress  
( orb a14 ( orb a13 ( orb a12 ( orb a11 ( orb a10 ( orb a9 ( orb a8 ( orb a7 ( orb a6 ( orb a5 ( orb a4 ( orb a3 ( orb a2 a1 ) ) ) ) ) ) ) ) ) ) ) ) ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ14 ) FlexClient_Ф_deployPriceXchg 
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
 Notation " 'FlexClient_Ф_deployPriceXchg_ref_' '(' sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg ')' " := 
 ( URResult ( FlexClient_Ф_deployPriceXchg_call 
 sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg )) 
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
( set_internal_wallet_value : URValue XInteger128 a5 ) ( tip3cfg : URValue Tip3Config a6 ) 
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
 wrapper_pubkey wrapper_deploy_value wrapper_keep_balance ext_wallet_balance set_internal_wallet_value tip3cfg )) 
 (in custom URValue at level 0 , wrapper_pubkey custom URValue at level 0 
 , wrapper_deploy_value custom URValue at level 0 
 , wrapper_keep_balance custom URValue at level 0 
 , ext_wallet_balance custom URValue at level 0 
 , set_internal_wallet_value custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_deployEmptyFlexWallet_call { a1 a2 a3 }  ( pubkey : URValue XInteger256 a1 ) 
( tons_to_wallet : URValue XInteger128 a2 ) ( tip3cfg : URValue Tip3Config a3 ) 
: LedgerT ( ControlResult XAddress true  ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FlexClient_Ф_deployEmptyFlexWallet 
 ( SimpleLedgerableArg URValue {{ Λ "pubkey" }} ( pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tons_to_wallet" }} ( tons_to_wallet ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3cfg" }} ( tip3cfg ) ) 
 . 
 Notation " 'FlexClient_Ф_deployEmptyFlexWallet_ref_' '(' pubkey tons_to_wallet tip3cfg ')' " := 
 ( URResult ( FlexClient_Ф_deployEmptyFlexWallet_call 
 pubkey tons_to_wallet tip3cfg )) 
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
 tons_value out_pubkey out_internal_owner my_tip3_addr )) 
 (in custom ULValue at level 0 , tons_value custom URValue at level 0 
 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_getOwner_call  : LedgerT ( ControlResult XInteger256 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_getOwner 
 . 
 Notation " 'FlexClient_Ф_getOwner_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_getOwner_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_getFlex_call  : LedgerT ( ControlResult XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_getFlex 
 . 
 Notation " 'FlexClient_Ф_getFlex_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_getFlex_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_hasExtWalletCode_call  : LedgerT ( ControlResult XBool false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_hasExtWalletCode 
 . 
 Notation " 'FlexClient_Ф_hasExtWalletCode_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_hasExtWalletCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_hasFlexWalletCode_call  : LedgerT ( ControlResult XBool false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_hasFlexWalletCode 
 . 
 Notation " 'FlexClient_Ф_hasFlexWalletCode_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_hasFlexWalletCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_hasFlexWrapperCode_call  : LedgerT ( ControlResult XBool false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FlexClient_Ф_hasFlexWrapperCode 
 . 
 Notation " 'FlexClient_Ф_hasFlexWrapperCode_ref_' '(' ')' " := 
 ( URResult ( FlexClient_Ф_hasFlexWrapperCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition FlexClient_Ф_getPayloadForDeployInternalWallet_call { a1 a2 a3 } 
 ( owner_pubkey : URValue XInteger256 a1 ) ( owner_addr : URValue addr_std_compact a2 )
 ( tons : URValue XInteger128 a3 ) : LedgerT ( ControlResult TvmCell (orb (orb a3 a2) a1) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FlexClient_Ф_getPayloadForDeployInternalWallet 
 ( SimpleLedgerableArg URValue {{ Λ "owner_pubkey" }} ( owner_pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "owner_addr" }} ( owner_addr ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tons" }} ( tons ) ) 
 . 
 Notation " 'FlexClient_Ф_getPayloadForDeployInternalWallet_ref_' '(' owner_pubkey owner_addr tons ')' " := 
 ( URResult ( FlexClient_Ф_getPayloadForDeployInternalWallet_call 
 owner_pubkey owner_addr tons )) 
 (in custom URValue at level 0 , owner_pubkey custom URValue at level 0 
 , owner_addr custom URValue at level 0 
 , tons custom URValue at level 0 ) : ursus_scope . 

 Definition FlexClient_Ф__fallback_call { a1 }  ( x : URValue TvmCell a1 ) : LedgerT ( ControlResult XInteger a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FlexClient_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "x" }} ( x ) ) 
 . 
 Notation " 'FlexClient_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( FlexClient_Ф__fallback_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope . 


End FLeXClientFuncNotations .