
Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import Project.CommonConstSig.

Require Import Contracts.Flex.Ledger.
Require Import Contracts.Flex.Functions.FuncSig.

Module FuncNotations (xt: XTypesSig) 
                          (sm: StateMonadSig) 
                          (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

Module Export SpecModuleForFuncNotations :=  Spec xt sm.

Import UrsusNotations.

Local Open Scope ursus_scope.
About ULState.

Check ULState (f:=_Contract) (H:=ContractLEmbeddedType deployer_pubkey_).

Notation " 'Flex.deployer_pubkey_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType  deployer_pubkey_) ) (in custom ULValue at level 0) : ursus_scope. 
 (*дал так же*)
 
(*  Notation " 'Flex.tons_cfg_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract)  tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Flex.pair_code_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract)  pair_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Flex.xchg_pair_code_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract)  xchg_pair_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Flex.price_code_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract)  price_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Flex.xchg_price_code_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract)  xchg_price_code_ ) (in custom ULValue at level 0) : ursus_scope. 
(*  Notation " 'Flex.min_amount_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract)  min_amount_ ) (in custom ULValue at level 0) : ursus_scope.  *)
 Notation " 'Flex.deals_limit_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract)  deals_limit_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Flex.notify_addr_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract)  notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 

 Notation " 'TradingPair.flex_addr_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract) TradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract) TradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract) TradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 

Notation " 'XchgPair.flex_addr_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract) XchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_major_root_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract) XchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_minor_root_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract) XchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.deploy_value_' " := ( ULState (H0:=LedgerLEmbeddedType  _Contract) XchgPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 


Notation " 'TonsConfig.transfer_tip3' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) TonsConfig_ι_transfer_tip3 ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) TonsConfig_ι_return_ownership ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) TonsConfig_ι_trading_pair_deploy ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.order_answer' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) TonsConfig_ι_order_answer ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.process_queue' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) TonsConfig_ι_process_queue ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.send_notify' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) TonsConfig_ι_send_notify ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'Flex.deployer_pubkey_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract)  deployer_pubkey_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Flex.tons_cfg_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract)  tons_cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Flex.pair_code_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract)  pair_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Flex.xchg_pair_code_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract)  xchg_pair_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Flex.price_code_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract)  price_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Flex.xchg_price_code_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract)  xchg_price_code_ ) (in custom URValue at level 0) : ursus_scope. 
(*  Notation " 'Flex.min_amount_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract)  min_amount_ ) (in custom URValue at level 0) : ursus_scope.  *)
 Notation " 'Flex.deals_limit_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract)  deals_limit_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Flex.notify_addr_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract)  notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'TradingPair.flex_addr_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) TradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) TradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) TradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'XchgPair.flex_addr_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) XchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_major_root_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) XchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_minor_root_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) XchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.deploy_value_' " := ( URState (H0:=LedgerLEmbeddedType  _Contract) XchgPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 
 *)

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

Notation " 'error_code::not_enough_tons' " := (sInject error_code_ι_not_enough_tons) (in custom URValue at level 0) : ursus_scope. 

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
