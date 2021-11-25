Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.

Require Import CommonNotations.
Require Import Contracts.Price.Ledger.
Require Import Contracts.Price.Functions.FuncSig.
Require Import Contracts.Price.ClassTypes.

(* здесь инмпортируем все внешние интерфейсы *)
Require Import Contracts.Price.Interface.
Require Import Contracts.TONTokenWallet.Interface.
Require Import Contracts.Flex.Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module PricePublicInterface := PublicInterface xt sm.
Module TONTokenWalletPublicInterface := Contracts.TONTokenWallet.Interface.PublicInterface xt sm.
Module FlexNotifyPublicInterface     := Contracts.Flex.Interface.PublicInterface xt sm.
Module PriceCallbackPublicInterface  := Contracts.Price.Interface.PublicInterface xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Fail Check OutgoingMessage_default.

Import UrsusNotations.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

 Definition price__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_price_ ) : ULValue uint128 ) . 
 Definition price__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_price_ ) : URValue uint128 false ) . 
 Notation " '_price_' " := ( price__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_price_' " := ( price__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition sells_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_sells_amount_ ) : ULValue uint128 ) . 
 Definition sells_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_sells_amount_ ) : URValue uint128 false ) . 
 Notation " '_sells_amount_' " := ( sells_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_sells_amount_' " := ( sells_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition buys_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_buys_amount_ ) : ULValue uint128 ) . 
 Definition buys_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_buys_amount_ ) : URValue uint128 false ) . 
 Notation " '_buys_amount_' " := ( buys_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_buys_amount_' " := ( buys_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_flex_ ) : ULValue addr_std_fixedLRecord ) . 
 Definition flex__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_flex_ ) : URValue addr_std_fixedLRecord false ) . 
 Notation " '_flex_' " := ( flex__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_' " := ( flex__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition min_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_min_amount_ ) : ULValue uint128 ) . 
 Definition min_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_min_amount_ ) : URValue uint128 false ) . 
 Notation " '_min_amount_' " := ( min_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_min_amount_' " := ( min_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition deals_limit__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_deals_limit_ ) : ULValue uint8 ) . 
 Definition deals_limit__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_deals_limit_ ) : URValue uint8 false ) . 
 Notation " '_deals_limit_' " := ( deals_limit__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_deals_limit_' " := ( deals_limit__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition notify_addr__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_notify_addr_ ) : ULValue XAddress (* IFlexNotifyPtrLRecord *) ) . 
 Definition notify_addr__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_notify_addr_ ) : URValue XAddress (* IFlexNotifyPtrLRecord *) false ) . 
 Notation " '_notify_addr_' " := ( notify_addr__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_notify_addr_' " := ( notify_addr__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_workchain_id_ ) : ULValue uint8 ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_workchain_id_ ) : URValue uint8 false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tons_cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_tons_cfg_ ) : ULValue TonsConfigLRecord ) . 
 Definition tons_cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_tons_cfg_ ) : URValue TonsConfigLRecord false ) . 
 Notation " '_tons_cfg_' " := ( tons_cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tons_cfg_' " := ( tons_cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tip3_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_tip3_code_ ) : ULValue XCell ) . 
 Definition tip3_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_tip3_code_ ) : URValue XCell false ) . 
 Notation " '_tip3_code_' " := ( tip3_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tip3_code_' " := ( tip3_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tip3cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_tip3cfg_ ) : ULValue Tip3ConfigLRecord ) . 
 Definition tip3cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_tip3cfg_ ) : URValue Tip3ConfigLRecord false ) . 
 Notation " '_tip3cfg_' " := ( tip3cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tip3cfg_' " := ( tip3cfg__right ) (in custom URValue at level 0) : ursus_scope. 

 Definition sells__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_sells_ ) : ULValue ( XQueue OrderInfoLRecord ) ) . 
 Definition sells__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_sells_ ) : URValue ( XQueue OrderInfoLRecord ) false ) . 
 Notation " '_sells_' " := ( sells__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_sells_' " := ( sells__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition buys__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_buys_ ) : ULValue ( XQueue OrderInfoLRecord ) ) . 
 Definition buys__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DPrice_ι_buys_ ) : URValue ( XQueue OrderInfoLRecord ) false ) . 
 Notation " '_buys_' " := ( buys__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_buys_' " := ( buys__right ) (in custom URValue at level 0) : ursus_scope. 


Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

(**************************************************************************************************)
 Definition make_deal_right { a1 a2 }  ( sell : URValue ( OrderInfoLRecord ) a1 ) ( buy : URValue ( OrderInfoLRecord ) a2 ) : URValue ( XBool # (XBool # uint128) ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) make_deal 
 sell buy ) . 
 
 Notation " 'make_deal_' '(' sell buy ')' " := 
 ( make_deal_right 
 sell buy ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , buy custom URValue at level 0 ) : ursus_scope .

 Definition extract_active_order_right { a1 a2 a3 a4 }  
( cur_order : URValue ( XMaybe (uint # OrderInfoLRecord) ) a1 ) 
( orders : URValue ( XQueue OrderInfoLRecord ) a2 ) 
( all_amount : URValue ( uint128 ) a3 ) 
( sell : URValue ( XBool ) a4 ) 
: URValue ( ( XMaybe (uint # OrderInfoLRecord) ) # (( XQueue OrderInfoLRecord ) # uint128) ) 
( orb ( orb ( orb a4 a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) extract_active_order 
 cur_order orders all_amount sell ) . 
 
 Notation " 'extract_active_order_' '(' cur_order orders all_amount sell ')' " := 
 ( extract_active_order_right 
 cur_order orders all_amount sell ) 
 (in custom URValue at level 0 , cur_order custom URValue at level 0 
 , orders custom URValue at level 0 
 , all_amount custom URValue at level 0 
 , sell custom URValue at level 0 ) : ursus_scope . 
 
 Definition process_queue_left { R a1 a2 }  ( sell_idx : URValue ( uint ) a1 ) ( buy_idx : URValue ( uint ) a2 ) : UExpression R ( orb a2 a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) process_queue 
 sell_idx buy_idx ) . 
 
 Notation " 'process_queue_' '(' sell_idx buy_idx ')' " := 
 ( process_queue_left 
 sell_idx buy_idx ) 
 (in custom ULValue at level 0 , sell_idx custom URValue at level 0 
 , buy_idx custom URValue at level 0 ) : ursus_scope . 

 Definition onTip3LendOwnership_right { a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( XAddress ) a1 ) ( balance : URValue ( uint128 ) a2 ) ( lend_finish_time : URValue ( uint32 ) a3 ) ( pubkey : URValue ( uint256 ) a4 ) ( internal_owner : URValue ( XAddress ) a5 ) ( payload : URValue ( XCell ) a6 ) : URValue OrderRetLRecord ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) onTip3LendOwnership 
 answer_addr balance lend_finish_time pubkey internal_owner payload ) . 
 
 Notation " 'onTip3LendOwnership_' '(' answer_addr balance lend_finish_time pubkey internal_owner payload ')' " := 
 ( onTip3LendOwnership_right 
 answer_addr balance lend_finish_time pubkey internal_owner payload ) 
 (in custom URValue at level 0 , answer_addr custom URValue at level 0 
 , balance custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 Definition buyTip3_right { a1 a2 a3 }  ( amount : URValue ( uint128 ) a1 ) ( receive_tip3_wallet : URValue ( XAddress ) a2 ) ( order_finish_time : URValue ( uint32 ) a3 ) : URValue OrderRetLRecord true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) buyTip3 
 amount receive_tip3_wallet order_finish_time ) . 
 
 Notation " 'buyTip3_' '(' amount receive_tip3_wallet order_finish_time ')' " := 
 ( buyTip3_right 
 amount receive_tip3_wallet order_finish_time ) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , receive_tip3_wallet custom URValue at level 0 
 , order_finish_time custom URValue at level 0 ) : ursus_scope . 
 
 Definition processQueue_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) processQueue 
 ) . 
 
 Notation " 'processQueue_' '(' ')' " := 
 ( processQueue_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition cancelSell_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) cancelSell 
 ) . 
 
 Notation " 'cancelSell_' '(' ')' " := 
 ( cancelSell_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition cancelBuy_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) cancelBuy 
 ) . 
 
 Notation " 'cancelBuy_' '(' ')' " := 
 ( cancelBuy_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 Definition getDetails_right  : URValue DetailsInfoLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDetails 
 ) . 
 
 Notation " 'getDetails_' '(' ')' " := 
 ( getDetails_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getPrice_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPrice 
 ) . 
 
 Notation " 'getPrice_' '(' ')' " := 
 ( getPrice_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getMinimumAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getMinimumAmount 
 ) . 
 
 Notation " 'getMinimumAmount_' '(' ')' " := 
 ( getMinimumAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getTonsCfg_right  : URValue TonsConfigLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTonsCfg 
 ) . 
 
 Notation " 'getTonsCfg_' '(' ')' " := 
 ( getTonsCfg_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getSells_right  : URValue ( XHMap uint OrderInfoLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSells 
 ) . 
 
 Notation " 'getSells_' '(' ')' " := 
 ( getSells_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getBuys_right  : URValue ( XHMap uint OrderInfoLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuys 
 ) . 
 
 Notation " 'getBuys_' '(' ')' " := 
 ( getBuys_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getSellAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSellAmount 
 ) . 
 
 Notation " 'getSellAmount_' '(' ')' " := 
 ( getSellAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getBuyAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuyAmount 
 ) . 
 
 Notation " 'getBuyAmount_' '(' ')' " := 
 ( getBuyAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition _fallback_right { a1 a2 }  ( x : URValue XCell a1 ) ( y : URValue XSlice a2 ) : URValue uint (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 x y ) . 
 
 Notation " '_fallback_' '(' x ',' y ')' " := 
 ( _fallback_right 
 x y ) 
 (in custom URValue at level 0 , x custom URValue at level 0 , y custom URValue at level 0) : ursus_scope . 

 Definition onTip3LendOwnershipMinValue_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) onTip3LendOwnershipMinValue 
 ) . 
 
 Notation " 'onTip3LendOwnershipMinValue_' '(' ')' " := 
 ( onTip3LendOwnershipMinValue_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition buyTip3MinValue_right { a1 }  ( buy_cost : URValue ( uint128 ) a1 ) : URValue uint128 a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) buyTip3MinValue 
 buy_cost ) . 
 
 Notation " 'buyTip3MinValue_' '(' buy_cost ')' " := 
 ( buyTip3MinValue_right 
 buy_cost ) 
 (in custom URValue at level 0 , buy_cost custom URValue at level 0 ) : ursus_scope . 

 Definition verify_tip3_addr_right { a1 a2 a3 }  ( tip3_wallet : URValue ( XAddress ) a1 ) ( wallet_pubkey : URValue ( uint256 ) a2 ) ( internal_owner : URValue ( uint256 ) a3 ) : URValue XBool ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) verify_tip3_addr 
 tip3_wallet wallet_pubkey internal_owner ) . 
 
 Notation " 'verify_tip3_addr_' '(' tip3_wallet wallet_pubkey internal_owner ')' " := 
 ( verify_tip3_addr_right 
 tip3_wallet wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , tip3_wallet custom URValue at level 0 
 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope . 

 Definition expected_wallet_address_right { a1 a2 }  ( wallet_pubkey : URValue ( uint256 ) a1 ) ( internal_owner : URValue ( uint256 ) a2 ) : URValue uint256 ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) expected_wallet_address 
 wallet_pubkey internal_owner ) . 
 
 Notation " 'expected_wallet_address_' '(' wallet_pubkey internal_owner ')' " := 
 ( expected_wallet_address_right 
 wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope .

 Definition on_sell_fail_right { a1 a2 a3 }  ( ec : URValue ( uint ) a1 ) ( wallet_in : URValue ( XAddress (* ITONTokenWalletPtrLRecord *) ) a2 ) ( amount : URValue ( uint128 ) a3 ) : URValue OrderRetLRecord ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) on_sell_fail 
 ec wallet_in amount ) . 
 
 Notation " 'on_sell_fail_' '(' ec wallet_in amount ')' " := 
 ( on_sell_fail_right 
 ec wallet_in amount ) 
 (in custom URValue at level 0 , ec custom URValue at level 0 
 , wallet_in custom URValue at level 0 
 , amount custom URValue at level 0 ) : ursus_scope .

 Definition prepare_price_state_init_and_addr_right { a1 a2 }  ( price_data : URValue ( DPriceLRecord ) a1 ) ( price_code : URValue ( XCell ) a2 ) : URValue ( StateInitLRecord # uint256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_price_state_init_and_addr 
 price_data price_code ) . 
 
 Notation " 'prepare_price_state_init_and_addr_' '(' price_data price_code ')' " := 
 ( prepare_price_state_init_and_addr_right 
 price_data price_code ) 
 (in custom URValue at level 0 , price_data custom URValue at level 0 
 , price_code custom URValue at level 0 ) : ursus_scope . 

 Definition is_active_time_right { a1 }  ( order_finish_time : URValue ( uint32 ) a1 ) : URValue XBool a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) is_active_time 
 order_finish_time ) . 
 
 Notation " 'is_active_time_' '(' order_finish_time ')' " := 
 ( is_active_time_right 
 order_finish_time ) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope .

 Definition calc_cost_right { a1 a2 }  ( amount : URValue ( uint128 ) a1 ) ( price : URValue ( uint128 ) a2 ) : URValue (XMaybe uint128) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_cost 
 amount price ) . 
 
 Notation " 'calc_cost_' '(' amount price ')' " := 
 ( calc_cost_right 
 amount price ) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom URValue at level 0 ) : ursus_scope . 

 Definition process_queue_impl_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 }  ( tip3root : URValue ( XAddress ) a1 ) ( notify_addr : URValue ( XAddress (* IFlexNotifyPtrLRecord *) ) a2 ) ( price : URValue ( uint128 ) a3 ) ( deals_limit : URValue ( uint8 ) a4 ) ( tons_cfg : URValue ( TonsConfigLRecord ) a5 ) ( sell_idx : URValue ( uint ) a6 ) ( buy_idx : URValue ( uint ) a7 ) ( sells_amount : URValue ( uint128 ) a8 ) ( sells : URValue ( XQueue OrderInfoLRecord ) a9 ) ( buys_amount : URValue ( uint128 ) a10 ) ( buys : URValue ( XQueue OrderInfoLRecord ) a11 ) : URValue process_retLRecord ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a11 a10 ) a9 ) a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ11 ) process_queue_impl 
 tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) . 
 
 Notation " 'process_queue_impl_' '(' tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ')' " := 
 ( process_queue_impl_right 
 tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) 
 (in custom URValue at level 0 , tip3root custom URValue at level 0 
 , notify_addr custom URValue at level 0 
 , price custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_cfg custom URValue at level 0 
 , sell_idx custom URValue at level 0 
 , buy_idx custom URValue at level 0 
 , sells_amount custom URValue at level 0 
 , sells custom URValue at level 0 
 , buys_amount custom URValue at level 0 
 , buys custom URValue at level 0 ) : ursus_scope . 

 Definition cancel_order_impl_right { a1 a2 a3 a4 a5 a6 a7 }  
( orders : URValue ( XQueue OrderInfoLRecord ) a1 ) 
( client_addr : URValue ( addr_std_fixedLRecord ) a2 ) 
( all_amount : URValue ( uint128 ) a3 ) 
( sell : URValue ( XBool ) a4 ) 
( return_ownership : URValue ( uint (* Grams *) ) a5 ) 
( process_queue : URValue ( uint (* Grams *) ) a6 ) 
( incoming_val : URValue ( uint (* Grams *) ) a7 ) 
: URValue ((XQueue OrderInfoLRecord) # uint128)
 ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancel_order_impl 
 orders client_addr all_amount sell return_ownership process_queue incoming_val ) . 
 
 Notation " 'cancel_order_impl_' '(' orders client_addr all_amount sell return_ownership process_queue incoming_val ')' " := 
 ( cancel_order_impl_right 
 orders client_addr all_amount sell return_ownership process_queue incoming_val ) 
 (in custom URValue at level 0 , orders custom URValue at level 0 
 , client_addr custom URValue at level 0 
 , all_amount custom URValue at level 0 
 , sell custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , process_queue custom URValue at level 0 
 , incoming_val custom URValue at level 0 ) : ursus_scope . 


End Calls. 

End FuncNotations.
