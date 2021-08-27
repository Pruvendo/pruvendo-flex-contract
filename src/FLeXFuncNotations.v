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
Require Import FLeXClassSelf.
Require Import FLeXSpecSelf.
Require Import FLeXConstSig. 
Require Import UrsusStdLib.stdFunc.

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

Import ListNotations.


Notation " 'TonsConfig.transfer_tip3' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.order_answer' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.process_queue' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.send_notify' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom ULValue at level 0) : ursus_scope. 


Notation " 'FLeX.deployer_pubkey_' " := ( ULState (U:= FLeX ) FLeX_ι_deployer_pubkey_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.tons_cfg_' " := ( ULState (U:= FLeX ) FLeX_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.pair_code_' " := ( ULState (U:= FLeX ) FLeX_ι_pair_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.xchg_pair_code_' " := ( ULState (U:= FLeX ) FLeX_ι_xchg_pair_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.price_code_' " := ( ULState (U:= FLeX ) FLeX_ι_price_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.xchg_price_code_' " := ( ULState (U:= FLeX ) FLeX_ι_xchg_price_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.min_amount_' " := ( ULState (U:= FLeX ) FLeX_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.deals_limit_' " := ( ULState (U:= FLeX ) FLeX_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.notify_addr_' " := ( ULState (U:= FLeX ) FLeX_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 

 Notation " 'TradingPair.flex_addr_' " := ( ULState (U:= TradingPair ) TradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( ULState (U:= TradingPair ) TradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( ULState (U:= TradingPair ) TradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 

Notation " 'XchgPair.flex_addr_' " := ( ULState (U:= XchgPair ) XchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_major_root_' " := ( ULState (U:= XchgPair ) XchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_minor_root_' " := ( ULState (U:= XchgPair ) XchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.deploy_value_' " := ( ULState (U:= XchgPair ) XchgPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 


Notation " 'TonsConfig.transfer_tip3' " := ( URState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( URState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( URState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.order_answer' " := ( URState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.process_queue' " := ( URState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.send_notify' " := ( URState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'FLeX.deployer_pubkey_' " := ( URState (U:= FLeX ) FLeX_ι_deployer_pubkey_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.tons_cfg_' " := ( URState (U:= FLeX ) FLeX_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.pair_code_' " := ( URState (U:= FLeX ) FLeX_ι_pair_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.xchg_pair_code_' " := ( URState (U:= FLeX ) FLeX_ι_xchg_pair_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.price_code_' " := ( URState (U:= FLeX ) FLeX_ι_price_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.xchg_price_code_' " := ( URState (U:= FLeX ) FLeX_ι_xchg_price_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.min_amount_' " := ( URState (U:= FLeX ) FLeX_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.deals_limit_' " := ( URState (U:= FLeX ) FLeX_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.notify_addr_' " := ( URState (U:= FLeX ) FLeX_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'TradingPair.flex_addr_' " := ( URState (U:= TradingPair ) TradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( URState (U:= TradingPair ) TradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( URState (U:= TradingPair ) TradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'XchgPair.flex_addr_' " := ( URState (U:= XchgPair ) XchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_major_root_' " := ( URState (U:= XchgPair ) XchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_minor_root_' " := ( URState (U:= XchgPair ) XchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.deploy_value_' " := ( URState (U:= XchgPair ) XchgPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 


Notation " 'TIMESTAMP_DELAY' " := (sInject TIMESTAMP_DELAY) (in custom URValue at level 0) : ursus_scope.
Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_message_sender_is_not_my_owner) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::sender_is_not_deployer' " := (sInject error_code_ι_sender_is_not_deployer) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::unexpected_refs_count_in_code' " := (sInject error_code_ι_unexpected_refs_count_in_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::cant_override_code' " := (sInject error_code_ι_cant_override_code) (in custom URValue at level 0) : ursus_scope. 

Notation " 'ok' " := (sInject ok) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::out_of_tons' " := (sInject error_code_ι_out_of_tons) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::deals_limit' " := (sInject error_code_ι_deals_limit) (in custom URValue at level 0) : ursus_scope.
Notation " 'error_code::not_enough_tons_to_process' " := (sInject error_code_ι_not_enough_tons_to_process) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::not_enough_tokens_amount' " := (sInject error_code_ι_not_enough_tokens_amount) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::too_big_tokens_amount' " := (sInject error_code_ι_too_big_tokens_amount) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::different_workchain_id' " := (sInject error_code_ι_different_workchain_id) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::unverified_tip3_wallet' " := (sInject error_code_ι_unverified_tip3_wallet) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::canceled' " := (sInject error_code_ι_canceled) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::expired' " := (sInject error_code_ι_expired) (in custom URValue at level 0) : ursus_scope. 
Notation " 'safe_delay_period' " := (sInject safe_delay_period) (in custom URValue at level 0) : ursus_scope. 

Notation " 'VMState.msg_pubkey' " := ( URState (U:= VMState ) VMState_ι_msg_pubkey ) (in custom URValue at level 0) : ursus_scope.
Notation " 'VMState.now' " := ( URState (U:= VMState ) VMState_ι_now ) (in custom URValue at level 0) : ursus_scope.
Notation " 'VMState.accepted' " := ( URState (U:= VMState ) VMState_ι_accepted ) (in custom URValue at level 0) : ursus_scope.
Notation " 'VMState.msg_value' " := ( URState (U:= VMState ) VMState_ι_msg_value ) (in custom URValue at level 0) : ursus_scope.

Notation " 'VMState.msg_pubkey' " := ( ULState (U:= VMState ) VMState_ι_msg_pubkey ) (in custom ULValue at level 0) : ursus_scope.
Notation " 'VMState.now' " := ( ULState (U:= VMState ) VMState_ι_now ) (in custom ULValue at level 0) : ursus_scope.
Notation " 'VMState.accepted' " := ( ULState (U:= VMState ) VMState_ι_accepted ) (in custom ULValue at level 0) : ursus_scope.
Notation " 'VMState.msg_value' " := ( ULState (U:= VMState ) VMState_ι_msg_value ) (in custom ULValue at level 0) : ursus_scope.

Notation " 'error_code::not_enough_tons' " := (sInject error_code_ι_not_enough_tons) (in custom URValue at level 0) : ursus_scope. 

Parameter FLeX_Ф_constructor : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XAddress -> UExpression PhantomType false . 
Parameter FLeX_Ф_setPairCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_setXchgPairCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_setPriceCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_setXchgPriceCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_isFullyInitialized : UExpression XBool false . 
Parameter FLeX_Ф_getTonsCfg : UExpression TonsConfig false . 
Parameter FLeX_Ф_getTradingPairCode : UExpression TvmCell false .
Parameter FLeX_Ф_getXchgPairCode : UExpression TvmCell false . 
Parameter FLeX_Ф_getSellPriceCode : XAddress -> UExpression TvmCell false . 
Parameter FLeX_Ф_getXchgPriceCode : XAddress -> XAddress -> UExpression TvmCell false . 
Parameter FLeX_Ф_getSellTradingPair : XAddress -> UExpression XAddress false . 
Parameter FLeX_Ф_getXchgTradingPair : XAddress -> XAddress -> UExpression XAddress false . 
Parameter FLeX_Ф_getMinAmount : UExpression XInteger128 false . 
Parameter FLeX_Ф_getDealsLimit : UExpression XInteger8 false . 
Parameter FLeX_Ф_getNotifyAddr : UExpression XAddress false . 
Parameter FLeX_Ф__fallback : TvmCell -> UExpression XInteger false . 
 
 (*begin*) 
 Definition FLeX_Ф_constructor_call  ( deployer_pubkey : URValue XInteger256 false ) ( transfer_tip3 : URValue XInteger128 false ) ( return_ownership : URValue XInteger128 false ) ( trading_pair_deploy : URValue XInteger128 false ) ( order_answer : URValue XInteger128 false ) ( process_queue : URValue XInteger128 false ) ( send_notify : URValue XInteger128 false ) ( min_amount : URValue XInteger128 false ) ( deals_limit : URValue XInteger8 false ) ( notify_addr : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ10 ) FLeX_Ф_constructor 
 ( SimpleLedgerableArg URValue {{ Λ "deployer_pubkey" }} deployer_pubkey ) 
 ( SimpleLedgerableArg URValue {{ Λ "transfer_tip3" }} transfer_tip3 ) 
 ( SimpleLedgerableArg URValue {{ Λ "return_ownership" }} return_ownership ) 
 ( SimpleLedgerableArg URValue {{ Λ "trading_pair_deploy" }} trading_pair_deploy ) 
 ( SimpleLedgerableArg URValue {{ Λ "order_answer" }} order_answer ) 
 ( SimpleLedgerableArg URValue {{ Λ "process_queue" }} process_queue ) 
 ( SimpleLedgerableArg URValue {{ Λ "send_notify" }} send_notify ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} min_amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} deals_limit ) 
 ( SimpleLedgerableArg URValue {{ Λ "notify_addr" }} notify_addr ) 
 . 
 Notation " 'FLeX_Ф_constructor_ref_' '(' deployer_pubkey transfer_tip3 return_ownership trading_pair_deploy order_answer process_queue send_notify min_amount deals_limit notify_addr ')' " := 
 ( URResult ( FLeX_Ф_constructor_call 
 deployer_pubkey transfer_tip3 return_ownership trading_pair_deploy order_answer process_queue send_notify min_amount deals_limit notify_addr )) 
 (in custom URValue at level 0 , deployer_pubkey custom URValue at level 0 
 , transfer_tip3 custom ULValue at level 0 
 , return_ownership custom ULValue at level 0 
 , trading_pair_deploy custom ULValue at level 0 
 , order_answer custom ULValue at level 0 
 , process_queue custom ULValue at level 0 
 , send_notify custom ULValue at level 0 
 , min_amount custom ULValue at level 0 
 , deals_limit custom ULValue at level 0 
 , notify_addr custom ULValue at level 0 ) : ursus_scope . 
 (*end*) 


 (*begin*) 
 Definition FLeX_Ф_isFullyInitialized_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_isFullyInitialized 
 . 
 Notation " 'FLeX_Ф_isFullyInitialized_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_isFullyInitialized_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_setPairCode_call  ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setPairCode_ref_' '(' code ')' " := 
 ( URResult ( FLeX_Ф_setPairCode_call 
 code )) 
 (in custom URValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_setXchgPairCode_call  ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setXchgPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setXchgPairCode_ref_' '(' code ')' " := 
 ( URResult ( FLeX_Ф_setXchgPairCode_call 
 code )) 
 (in custom URValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

(*begin*) 
 Definition FLeX_Ф_setPriceCode_call  ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setPriceCode_ref_' '(' code ')' " := 
 ( URResult ( FLeX_Ф_setPriceCode_call 
 code )) 
 (in custom URValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_setXchgPriceCode_call  ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setXchgPriceCode_ref_' '(' code ')' " := 
 ( URResult ( FLeX_Ф_setXchgPriceCode_call 
 code )) 
 (in custom URValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_getTonsCfg_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getTonsCfg 
 . 
 Notation " 'FLeX_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getTonsCfg_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_getTradingPairCode_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getTradingPairCode 
 . 
 Notation " 'FLeX_Ф_getTradingPairCode_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getTradingPairCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_getXchgPairCode_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getXchgPairCode 
 . 
 Notation " 'FLeX_Ф_getXchgPairCode_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getXchgPairCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_getSellPriceCode_call  ( tip3_addr : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_getSellPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr" }} tip3_addr ) 
 . 
 Notation " 'FLeX_Ф_getSellPriceCode_ref_' '(' tip3_addr ')' " := 
 ( URResult ( FLeX_Ф_getSellPriceCode_call 
 tip3_addr )) 
 (in custom URValue at level 0 , tip3_addr custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_getXchgPriceCode_call  ( tip3_addr1 : URValue XAddress false ) ( tip3_addr2 : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) FLeX_Ф_getXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr1" }} tip3_addr1 ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr2" }} tip3_addr2 ) 
 . 
 Notation " 'FLeX_Ф_getXchgPriceCode_ref_' '(' tip3_addr1 tip3_addr2 ')' " := 
 ( URResult ( FLeX_Ф_getXchgPriceCode_call 
 tip3_addr1 tip3_addr2 )) 
 (in custom URValue at level 0 , tip3_addr1 custom URValue at level 0 
 , tip3_addr2 custom ULValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_getSellTradingPair_call  ( tip3_root : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_getSellTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_root" }} tip3_root ) 
 . 
 Notation " 'FLeX_Ф_getSellTradingPair_ref_' '(' tip3_root ')' " := 
 ( URResult ( FLeX_Ф_getSellTradingPair_call 
 tip3_root )) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 (*begin*) 
 Definition FLeX_Ф_getXchgTradingPair_call  ( tip3_major_root : URValue XAddress false ) ( tip3_minor_root : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) FLeX_Ф_getXchgTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_major_root" }} tip3_major_root ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_minor_root" }} tip3_minor_root ) 
 . 
 Notation " 'FLeX_Ф_getXchgTradingPair_ref_' '(' tip3_major_root tip3_minor_root ')' " := 
 ( URResult ( FLeX_Ф_getXchgTradingPair_call 
 tip3_major_root tip3_minor_root )) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom ULValue at level 0 ) : ursus_scope . 
 (*end*) 
 

 (*begin*) 
 Definition FLeX_Ф_getMinAmount_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getMinAmount 
 . 
 Notation " 'FLeX_Ф_getMinAmount_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getMinAmount_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 (*begin*) 
 Definition FLeX_Ф_getDealsLimit_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getDealsLimit 
 . 
 Notation " 'FLeX_Ф_getDealsLimit_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getDealsLimit_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 (*begin*) 
 Definition FLeX_Ф_getNotifyAddr_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getNotifyAddr 
 . 
 Notation " 'FLeX_Ф_getNotifyAddr_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getNotifyAddr_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 (*begin*) 
 Definition FLeX_Ф__fallback_call  ( x : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "x" }} x ) 
 . 

 Notation " 'FLeX_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( FLeX_Ф__fallback_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope . 
 (*end*) 



End FLeXFuncNotations.
