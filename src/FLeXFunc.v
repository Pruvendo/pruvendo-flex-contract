Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import List.
Import ListNotations.


Local Open Scope program_scope. 

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.StateMonad21. 
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.ProofEnvironment2.

Require Import FLeXContractTypes.
Require Import classFlex.
Require Import FLeXConstSig.  
Require Import ZArith.
Require Import FLeXFuncNotations.
Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG25.

(* Module stdFuncProofs (* (xt: XTypesSig) 
               (sm: StateMonadSig)  *)
               (dc : FLeXConstsTypesSig XTypesModule StateMonadModule )  (cs : ClassSig XTypesModule).
Import cs. 
Module Export FLeXFuncNotationsModule := FLeXFuncNotations XTypesModule StateMonadModule dc.
Import UrsusNotations.
 *)

Module FLeXFuncs (* (xt: XTypesSig) 
               (sm: StateMonadSig)  *)
               (dc : FLeXConstsTypesSig XTypesModule StateMonadModule ).
 
Module Export FLeXFuncNotationsModule := FLeXFuncNotations XTypesModule StateMonadModule dc.
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.


Definition plusassign (a b: XInteger) : UExpression  XInteger false :=
    {{
        a : XInteger @ "a" ; b : XInteger @ "b"  ; FLeXClient.owner_ := 0 ;
       { a } := !{a} + !{b}
    }}.



Definition test_ref (a b: XBool): UExpression XInteger false :=
    {{
       a : XBool @ "a" ;
       b : XBool @ "b" ;
       {b} := !{a}
    }}.

Definition test_ref_call {b} (x: URValue XBool b) (y: ULValue XBool) := 
   🏓 ursus_call_with_args (LedgerableWithArgs := λ2) test_ref 
   (SimpleLedgerableArg URValue {{ Λ "a" }} (local_right_copy x)) (RefLedgerableArg URValue {{ Λ "b" }} (local_left_copy y)) .

Notation " 'test_ref_' '(' x , y ')' " := ( URResult (test_ref_call x y))  
   (in custom URValue at level 0 , x custom URValue at level 0, y custom ULValue at level 0) : ursus_scope.

Notation " 'test_ref_' '(' x , y ')' " := ( FuncallExpression (test_ref_call x y))  
   (in custom ULValue at level 0 , x custom URValue at level 0, y custom ULValue at level 0) : ursus_scope.

Definition bar33 (b0 b1: XBool): UExpression XBool false :=
{{
   b0 : XBool @ "b0";
   b1 : XBool @ "b1";

   test_ref_ ( !{b0} , {b1} ) 

   new 'b : XBool @ "b" := !{b1} ; 
   return_ !{b}
}}.

Definition bar33_call (x y: URValue XBool false)  := 
   🏓 ursus_call_with_args (LedgerableWithArgs := λ2) bar33 
(SimpleLedgerableArg URValue {{ Λ "b0" }} x) (SimpleLedgerableArg URValue {{ Λ "b1" }} y) .


Notation " 'bar33_' '(' x , y ')' " := ( URResult (bar33_call x y))  
   (in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Notation " 'bar33_' '(' x , y ')' " := ( FuncallExpression (bar33_call x y))  
   (in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Definition FLeXClient_Ф_constructor ( pubkey : XInteger256 ) ( trading_pair_code : TvmCell ) ( xchg_pair_code : TvmCell ) 
: UExpression True false.

  refine {{ pubkey : XInteger256 @ "pubkey" ; { _ } }} .
  refine {{ trading_pair_code : TvmCell @ "trading_pair_code" ; { _ } }} .
  refine {{ xchg_pair_code : TvmCell @ "xchg_pair_code" ; { _ } }} .

 refine {{ FLeXClient.owner_ := !{ pubkey } ; { _ } }} . 



 trading_pair_code_ := trading_pair_code ; 
 xchg_pair_code_ := xchg_pair_code ; 
 workchain_id_ = std : : get < addr_std > ( address { tvm_myaddr ( ) } . val ( ) FLeXClient.) ^^ workchain_id ; 
 flex_ = address : : make_std ( int8 ( 0 ) , uint256 ( 0 ) ) ; 
 notify_addr_ = address : : make_std ( int8 ( 0 ) , uint256 ( 0 ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_constructor_call ( pubkey : SMLRValue XInteger256 false ) ( trading_pair_code : SMLRValue TvmCell false ) ( xchg_pair_code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ3 ) FLeXClient_Ф_constructor 
 ( SimpleLedgerableArg SMLRValue {{ Λ "pubkey" }} pubkey ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "trading_pair_code" }} trading_pair_code ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "xchg_pair_code" }} xchg_pair_code ) 
 . 
 Notation " 'FLeXClient_Ф_constructor_ref_' '(' pubkey trading_pair_code xchg_pair_code ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_constructor_ref_call 
 pubkey trading_pair_code xchg_pair_code )) 
 (in custom SMLLValue at level 0 , pubkey custom SMLLValue at level 0 
 , trading_pair_code custom SMLLValue at level 0 
 , xchg_pair_code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeXClient_Ф_setFLeXCfg ( tons_cfg : TonsConfigP ) ( flex : XAddress ) ( notify_addr : XAddress ) : SMLExpression True false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 tons_cfg_ = tons_cfg ; 
 flex_ = flex ; 
 notify_addr_ = notify_addr ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_setFLeXCfg_call ( tons_cfg : SMLRValue TonsConfigP false ) ( flex : SMLRValue XAddress false ) ( notify_addr : SMLRValue XAddress false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ3 ) FLeXClient_Ф_setFLeXCfg 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tons_cfg" }} tons_cfg ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "flex" }} flex ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "notify_addr" }} notify_addr ) 
 . 
 Notation " 'FLeXClient_Ф_setFLeXCfg_ref_' '(' tons_cfg flex notify_addr ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_setFLeXCfg_ref_call 
 tons_cfg flex notify_addr )) 
 (in custom SMLLValue at level 0 , tons_cfg custom SMLLValue at level 0 
 , flex custom SMLLValue at level 0 
 , notify_addr custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition Ф_prepare_trading_pair_state_init_and_addr ( pair_data : DTradingPairP ) ( pair_code : TvmCell ) : SMLExpression ( StateInitP # XInteger256 ) false := 
 {{ 
 Л_pair_data_cl_ := ^ prepare_persistent_data < ITradingPair , void , DTradingPair > ( { } , pair_data ) ; 
 Л_pair_init_ { { } , { } , pair_code , pair_data_cl , { } } ; 
 Л_pair_init_cl_ := ^ build ( pair_init .) ^^ make_cell ( ) ; 
 return { pair_init , uint256 ( tvm_hash ( pair_init_cl ) ) } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_prepare_trading_pair_state_init_and_addr_call ( pair_data : SMLRValue DTradingPairP false ) ( pair_code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_trading_pair_state_init_and_addr 
 ( SimpleLedgerableArg SMLRValue {{ Λ "pair_data" }} pair_data ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "pair_code" }} pair_code ) 
 . 
 Notation " 'Ф_prepare_trading_pair_state_init_and_addr_ref_' '(' pair_data pair_code ')' " := 
 ( SMLRResult ( Ф_prepare_trading_pair_state_init_and_addr_ref_call 
 pair_data pair_code )) 
 (in custom SMLRValue at level 0 , pair_data custom SMLRValue at level 0 
 , pair_code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition TradingPair_Ф_onDeploy : SMLExpression XBool false := 
 {{ 
 require ( int_value ( TradingPair.) ^^ get ( ) > deploy_value_ , error_code : : not_enough_tons ) ; 
 tvm_rawreserve ( TradingPair.deploy_value_ ^^ get ( ) , rawreserve_flag : : up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 return bool_t { true } ; 
 
 }} . 
 
 (*begin*) 
 Definition TradingPair_Ф_onDeploy_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) TradingPair_Ф_onDeploy 
 . 
 Notation " 'TradingPair_Ф_onDeploy_ref_' '(' ')' " := 
 ( SMLRResult ( TradingPair_Ф_onDeploy_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_deployTradingPair ( tip3_root : XAddress ) ( deploy_min_value : XInteger128 ) ( deploy_value : XInteger128 ) : SMLExpression XAddress false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_pair_data_ { . flex_addr_ = flex_ FLeXClient., ^^ tip3_root_ = tip3_root FLeXClient., ^^ deploy_value_ = deploy_min_value } ; 
 (*$$ ( state_init std_addr ) *) [ Л_state_init_ Л_std_addr_ ] = prepare_trading_pair_state_init_and_addr ( pair_data , trading_pair_code_ ) ; 
 Л_trade_pair_ := ^ ITradingPairPtr ( address : : make_std ( workchain_id_ , std_addr ) ) ; 
 FLeXClient.trade_pair ^^ deploy ( state_init , Grams ( FLeXClient.deploy_value ^^ get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ onDeploy ( ) ; 
 return FLeXClient.trade_pair ^^ get ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_deployTradingPair_call ( tip3_root : SMLRValue XAddress false ) ( deploy_min_value : SMLRValue XInteger128 false ) ( deploy_value : SMLRValue XInteger128 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ3 ) FLeXClient_Ф_deployTradingPair 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_root" }} tip3_root ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "deploy_min_value" }} deploy_min_value ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "deploy_value" }} deploy_value ) 
 . 
 Notation " 'FLeXClient_Ф_deployTradingPair_ref_' '(' tip3_root deploy_min_value deploy_value ')' " := 
 ( SMLRResult ( FLeXClient_Ф_deployTradingPair_ref_call 
 tip3_root deploy_min_value deploy_value )) 
 (in custom SMLRValue at level 0 , tip3_root custom SMLRValue at level 0 
 , deploy_min_value custom SMLLValue at level 0 
 , deploy_value custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Ф_prepare_xchg_pair_state_init_and_addr ( pair_data : DXchgPairP ) ( pair_code : TvmCell ) : SMLExpression ( StateInitP # XInteger256 ) false := 
 {{ 
 Л_pair_data_cl_ := ^ prepare_persistent_data < IXchgPair , void , DXchgPair > ( { } , pair_data ) ; 
 Л_pair_init_ { { } , { } , pair_code , pair_data_cl , { } } ; 
 Л_pair_init_cl_ := ^ build ( pair_init .) ^^ make_cell ( ) ; 
 return { pair_init , uint256 ( tvm_hash ( pair_init_cl ) ) } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_prepare_xchg_pair_state_init_and_addr_call ( pair_data : SMLRValue DXchgPairP false ) ( pair_code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_xchg_pair_state_init_and_addr 
 ( SimpleLedgerableArg SMLRValue {{ Λ "pair_data" }} pair_data ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "pair_code" }} pair_code ) 
 . 
 Notation " 'Ф_prepare_xchg_pair_state_init_and_addr_ref_' '(' pair_data pair_code ')' " := 
 ( SMLRResult ( Ф_prepare_xchg_pair_state_init_and_addr_ref_call 
 pair_data pair_code )) 
 (in custom SMLRValue at level 0 , pair_data custom SMLRValue at level 0 
 , pair_code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_deployXchgPair ( tip3_major_root : XAddress ) ( tip3_minor_root : XAddress ) ( deploy_min_value : XInteger128 ) ( deploy_value : XInteger128 ) : SMLExpression XAddress false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_pair_data_ { . flex_addr_ = flex_ FLeXClient., ^^ tip3_major_root_ = tip3_major_root FLeXClient., ^^ tip3_minor_root_ = tip3_minor_root FLeXClient., ^^ deploy_value_ = deploy_min_value } ; 
 (*$$ ( state_init std_addr ) *) [ Л_state_init_ Л_std_addr_ ] = prepare_xchg_pair_state_init_and_addr ( pair_data , xchg_pair_code_ ) ; 
 Л_trade_pair_ := ^ IXchgPairPtr ( address : : make_std ( workchain_id_ , std_addr ) ) ; 
 FLeXClient.trade_pair ^^ deploy ( state_init , Grams ( FLeXClient.deploy_value ^^ get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ onDeploy ( ) ; 
 return FLeXClient.trade_pair ^^ get ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_deployXchgPair_call ( tip3_major_root : SMLRValue XAddress false ) ( tip3_minor_root : SMLRValue XAddress false ) ( deploy_min_value : SMLRValue XInteger128 false ) ( deploy_value : SMLRValue XInteger128 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ4 ) FLeXClient_Ф_deployXchgPair 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_major_root" }} tip3_major_root ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_minor_root" }} tip3_minor_root ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "deploy_min_value" }} deploy_min_value ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "deploy_value" }} deploy_value ) 
 . 
 Notation " 'FLeXClient_Ф_deployXchgPair_ref_' '(' tip3_major_root tip3_minor_root deploy_min_value deploy_value ')' " := 
 ( SMLRResult ( FLeXClient_Ф_deployXchgPair_ref_call 
 tip3_major_root tip3_minor_root deploy_min_value deploy_value )) 
 (in custom SMLRValue at level 0 , tip3_major_root custom SMLRValue at level 0 
 , tip3_minor_root custom SMLLValue at level 0 
 , deploy_min_value custom SMLLValue at level 0 
 , deploy_value custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Ф_prepare_price_state_init_and_addr ( price_data : DPriceP ) ( price_code : TvmCell ) : SMLExpression ( StateInitP # XInteger256 ) false := 
 {{ 
 Л_price_data_cl_ := ^ prepare_persistent_data < IPrice , void , DPrice > ( { } , price_data ) ; 
 Л_price_init_ { { } , { } , price_code , price_data_cl , { } } ; 
 Л_price_init_cl_ := ^ build ( price_init .) ^^ make_cell ( ) ; 
 return { price_init , uint256 ( tvm_hash ( price_init_cl ) ) } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_prepare_price_state_init_and_addr_call ( price_data : SMLRValue DPriceP false ) ( price_code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_price_state_init_and_addr 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price_data" }} price_data ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price_code" }} price_code ) 
 . 
 Notation " 'Ф_prepare_price_state_init_and_addr_ref_' '(' price_data price_code ')' " := 
 ( SMLRResult ( Ф_prepare_price_state_init_and_addr_ref_call 
 price_data price_code )) 
 (in custom SMLRValue at level 0 , price_data custom SMLRValue at level 0 
 , price_code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_preparePrice ( price : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tip3_code : TvmCell ) ( tip3cfg : Tip3ConfigP ) ( price_code : TvmCell ) : SMLExpression ( StateInitP # XAddress # XInteger256 ) false := 
 {{ 
 Л_price_data_ { . price_ = price FLeXClient., ^^ sells_amount_ = uint128 ( 0 ) FLeXClient., ^^ buys_amount_ = uint128 ( 0 ) FLeXClient., ^^ flex_ = flex_ FLeXClient., ^^ min_amount_ = min_amount FLeXClient., ^^ deals_limit_ = deals_limit FLeXClient., ^^ notify_addr_ = notify_addr_ FLeXClient., ^^ workchain_id_ = workchain_id_ FLeXClient., ^^ tons_cfg_ = tons_cfg_ FLeXClient., ^^ tip3_code_ = tip3_code FLeXClient., ^^ tip3cfg_ = tip3cfg FLeXClient., ^^ sells_ = { } FLeXClient., ^^ buys_ = { } } ; 
 (*$$ ( state_init std_addr ) *) [ Л_state_init_ Л_std_addr_ ] = prepare_price_state_init_and_addr ( price_data , price_code ) ; 
 Л_addr_ := ^ address : : make_std ( workchain_id_ , std_addr ) ; 
 return { state_init , addr , std_addr } ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_preparePrice_call ( price : SMLRValue XInteger128 false ) ( min_amount : SMLRValue XInteger128 false ) ( deals_limit : SMLRValue XInteger8 false ) ( tip3_code : SMLRValue TvmCell false ) ( tip3cfg : SMLRValue Tip3ConfigP false ) ( price_code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ6 ) FLeXClient_Ф_preparePrice 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price" }} price ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "min_amount" }} min_amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "deals_limit" }} deals_limit ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_code" }} tip3_code ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3cfg" }} tip3cfg ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price_code" }} price_code ) 
 . 
 Notation " 'FLeXClient_Ф_preparePrice_ref_' '(' price min_amount deals_limit tip3_code tip3cfg price_code ')' " := 
 ( SMLRResult ( FLeXClient_Ф_preparePrice_ref_call 
 price min_amount deals_limit tip3_code tip3cfg price_code )) 
 (in custom SMLRValue at level 0 , price custom SMLRValue at level 0 
 , min_amount custom SMLLValue at level 0 
 , deals_limit custom SMLLValue at level 0 
 , tip3_code custom SMLLValue at level 0 
 , tip3cfg custom SMLLValue at level 0 
 , price_code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_deployPriceWithSell ( args_cl : TvmCell ) : SMLExpression XAddress false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_args_ := ^ parse < FLeXSellArgs > ( FLeXClient.args_cl ^^ ctos ( ) ) ; 
 (*$$ ( state_init addr std_addr ) *) [ Л_state_init_ Л_addr_ Л_std_addr_ ] = preparePrice ( FLeXClient.args ^^ price , FLeXClient.args ^^ min_amount , FLeXClient.args ^^ deals_limit , FLeXClient.args ^^ tip3_code , FLeXClient.args ^^ tip3cfg ( ) , FLeXClient.args ^^ price_code ) ; 
 Л_price_addr_ := ^ IPricePtr ( addr ) ; 
 Л_deploy_init_cl_ := ^ build ( state_init FLeXClient.) ^^ endc ( ) ; 
 Л_sell_args_ := ^ { . amount = FLeXClient.args ^^ amount FLeXClient., ^^ receive_wallet = FLeXClient.args ^^ addrs ( FLeXClient.) ^^ receive_wallet } ; 
 Л_payload_ := ^ build ( sell_args FLeXClient.) ^^ endc ( ) ; 
 ITONTokenWalletPtr my_tip3 ( FLeXClient.args ^^ addrs ( FLeXClient.) ^^ my_tip3_addr ) ; 
 my_tip3 ( Grams ( FLeXClient.args ^^ tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ lendOwnership ( std_addr , FLeXClient.args ^^ amount , FLeXClient.args ^^ lend_finish_time , deploy_init_cl , payload ) ; 
 return FLeXClient.price_addr ^^ get ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_deployPriceWithSell_call ( args_cl : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_deployPriceWithSell 
 ( SimpleLedgerableArg SMLRValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_deployPriceWithSell_ref_' '(' args_cl ')' " := 
 ( SMLRResult ( FLeXClient_Ф_deployPriceWithSell_ref_call 
 args_cl )) 
 (in custom SMLRValue at level 0 , args_cl custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Ф_calc_cost ( amount : XInteger128 ) ( price : XInteger128 ) : SMLExpression ( XMaybe XInteger128 ) false := 
 {{ 
 Л_tons_cost_ := ^ .amount ^^ get ( ) * .price ^^ get ( ) ; 
 if ( tons_cost > > 128 ) return { } ; 
 return uint128 ( tons_cost ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_calc_cost_call ( amount : SMLRValue XInteger128 false ) ( price : SMLRValue XInteger128 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) Ф_calc_cost 
 ( SimpleLedgerableArg SMLRValue {{ Λ "amount" }} amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price" }} price ) 
 . 
 Notation " 'Ф_calc_cost_ref_' '(' amount price ')' " := 
 ( SMLRResult ( Ф_calc_cost_ref_call 
 amount price )) 
 (in custom SMLRValue at level 0 , amount custom SMLRValue at level 0 
 , price custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Ф_is_active_time ( order_finish_time : XInteger32 ) : SMLExpression XBool false := 
 {{ 
 return tvm_now ( ) + safe_delay_period < .order_finish_time ^^ get ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_is_active_time_call ( order_finish_time : SMLRValue XInteger32 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) Ф_is_active_time 
 ( SimpleLedgerableArg SMLRValue {{ Λ "order_finish_time" }} order_finish_time ) 
 . 
 Notation " 'Ф_is_active_time_ref_' '(' order_finish_time ')' " := 
 ( SMLRResult ( Ф_is_active_time_ref_call 
 order_finish_time )) 
 (in custom SMLRValue at level 0 , order_finish_time custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition dealer_Ф_extract_active_order ( cur_order : ( XMaybe OrderInfoWithIdxP ) ) ( orders : ( XQueue OrderInfoP ) ) ( all_amount : XInteger128 ) ( sell : XBool ) : SMLExpression ( XQueue OrderInfoP ) false := 
 {{ 
 if ( cur_order ) return { cur_order , orders , all_amount } ; 
 while ( ! dealer.orders ^^ empty ( ) ) { cur_order = dealer.orders ^^ front_with_idx_opt ( ) ; 
 Л_ord_ := ^ cur_order - > second ; 
 if ( ! is_active_time ( dealer.ord ^^ order_finish_time ) ) { all_amount - = dealer.ord ^^ amount ; 
 Л_ret_ { uint32 ( ec : : expired ) , dealer.ord ^^ original_amount - dealer.ord ^^ amount , uint128 { 0 } } ; 
 IPriceCallbackPtr ( dealer.ord ^^ client_addr ) ( Grams ( dealer.ord ^^ account . get ( ) ) , IGNORE_ACTION_ERRORS dealer.) ^^ onOrderFinished ( ret , sell ) ; 
 dealer.orders ^^ pop ( ) ; 
 dealer.cur_order ^^ reset ( ) ; 
 continue ; 
 } break ; 
 } return { cur_order , orders , all_amount } ; 
 
 }} . 
 
 (*begin*) 
 Definition dealer_Ф_extract_active_order_call ( cur_order : SMLRValue ( XMaybe OrderInfoWithIdxP ) false ) ( orders : SMLRValue ( XQueue OrderInfoP ) false ) ( all_amount : SMLRValue XInteger128 false ) ( sell : SMLRValue XBool false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ4 ) dealer_Ф_extract_active_order 
 ( SimpleLedgerableArg SMLRValue {{ Λ "cur_order" }} cur_order ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "orders" }} orders ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "all_amount" }} all_amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "sell" }} sell ) 
 . 
 Notation " 'dealer_Ф_extract_active_order_ref_' '(' cur_order orders all_amount sell ')' " := 
 ( SMLRResult ( dealer_Ф_extract_active_order_ref_call 
 cur_order orders all_amount sell )) 
 (in custom SMLRValue at level 0 , cur_order custom SMLRValue at level 0 
 , orders custom SMLLValue at level 0 
 , all_amount custom SMLLValue at level 0 
 , sell custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition dealer_Ф_process_queue ( sell_idx : XInteger ) ( buy_idx : XInteger ) : SMLExpression True false := 
 {{ 
 std : : optional < OrderInfoWithIdx > sell_opt ; 
 std : : optional < OrderInfoWithIdx > buy_opt ; 
 Л_deals_count_ := ^ 0 ; 
 while ( true ) { std : : tie ( sell_opt , sells_ , sells_amount_ ) = extract_active_order ( sell_opt , sells_ , sells_amount_ , bool_t { true } ) ; 
 std : : tie ( buy_opt , buys_ , buys_amount_ ) = extract_active_order ( buy_opt , buys_ , buys_amount_ , bool_t { false } ) ; 
 if ( ! sell_opt || ! buy_opt ) break ; 
 (*$$ ( sell_idx_cur sell ) *) [ Л_sell_idx_cur_ Л_sell_ ] = *sell_opt ; 
 (*$$ ( buy_idx_cur buy ) *) [ Л_buy_idx_cur_ Л_buy_ ] = *buy_opt ; 
 Л_sell_out_of_tons_ := ^ false ; 
 Л_buy_out_of_tons_ := ^ false ; 
 Л_deal_amount_ { 0 } ; 
 if ( + + deals_count > deals_limit_ ) { Л_half_process_queue_ := ^ dealer.tons_cfg_ ^^ snd:process_queue / 2 ; 
 Л_safe_extra_ := ^ dealer.tons_cfg_ ^^ snd:return_ownership + dealer.tons_cfg_ ^^ snd:order_answer ; 
 if ( dealer.sell ^^ account < half_process_queue + safe_extra ) { sell_out_of_tons = true ; 
 } if ( dealer.buy ^^ account < half_process_queue + safe_extra ) { buy_out_of_tons = true ; 
 } if ( ! sell_out_of_tons && ! buy_out_of_tons ) { dealer.sell ^^ account - = half_process_queue ; 
 dealer.buy ^^ account - = half_process_queue ; 
 IPricePtr ( address { tvm_myaddr ( ) } ) ( Grams ( dealer.tons_cfg_ ^^ snd:process_queue . get ( ) ) , IGNORE_ACTION_ERRORS dealer.) ^^ processQueue ( ) ; 
 if ( sell_idx == sell_idx_cur ) ret_ = { uint32 ( ec : : deals_limit ) , dealer.sell ^^ original_amount - dealer.sell ^^ amount , dealer.sell ^^ amount } ; 
 if ( buy_idx == buy_idx_cur ) ret_ = { uint32 ( ec : : deals_limit ) , dealer.buy ^^ original_amount - dealer.buy ^^ amount , dealer.buy ^^ amount } ; 
 break ; 
 } } if ( ! sell_out_of_tons && ! buy_out_of_tons ) { std : : tie ( sell_out_of_tons , buy_out_of_tons , deal_amount ) = make_deal ( sell , buy ) ; 
 } if ( sell_out_of_tons ) { dealer.sells_ ^^ pop ( ) ; 
 Л_ret_ { uint32 ( ec : : out_of_tons ) , dealer.sell ^^ original_amount - dealer.sell ^^ amount , uint128 { 0 } } ; 
 if ( sell_idx == sell_idx_cur ) ret_ = ret ; 
 if ( dealer.sell ^^ account > dealer.tons_cfg_ ^^ snd:return_ownership ) { dealer.sell ^^ account - = dealer.tons_cfg_ ^^ snd:return_ownership ; 
 ITONTokenWalletPtr ( dealer.sell ^^ tip3_wallet ) ( Grams ( dealer.tons_cfg_ ^^ snd:return_ownership . get ( ) ) , IGNORE_ACTION_ERRORS dealer.) ^^ returnOwnership ( ) ; 
 IPriceCallbackPtr ( dealer.sell ^^ client_addr ) ( Grams ( dealer.sell ^^ account . get ( ) ) , IGNORE_ACTION_ERRORS dealer.) ^^ onOrderFinished ( ret , bool_t { true } ) ; 
 } dealer.sell_opt ^^ reset ( ) ; 
 } if ( buy_out_of_tons ) { dealer.buys_ ^^ pop ( ) ; 
 Л_ret_ { uint32 ( ec : : out_of_tons ) , dealer.buy ^^ original_amount - dealer.buy ^^ amount , uint128 { 0 } } ; 
 if ( buy_idx == buy_idx_cur ) ret_ = ret ; 
 IPriceCallbackPtr ( dealer.buy ^^ client_addr ) ( Grams ( dealer.buy ^^ account . get ( ) ) , IGNORE_ACTION_ERRORS dealer.) ^^ onOrderFinished ( ret , bool_t { false } ) ; 
 dealer.buy_opt ^^ reset ( ) ; 
 } if ( sell_out_of_tons || buy_out_of_tons ) continue ; 
 sell_opt - > second = sell ; 
 buy_opt - > second = buy ; 
 sells_amount_ - = deal_amount ; 
 buys_amount_ - = deal_amount ; 
 if ( ! dealer.sell ^^ amount ) { dealer.sells_ ^^ pop ( ) ; 
 Л_ret_ { uint32 ( ok ) , dealer.sell ^^ original_amount , uint128 { 0 } } ; 
 if ( sell_idx == sell_idx_cur ) ret_ = ret ; 
 IPriceCallbackPtr ( dealer.sell ^^ client_addr ) ( Grams ( dealer.sell ^^ account . get ( ) ) , IGNORE_ACTION_ERRORS dealer.) ^^ onOrderFinished ( ret , bool_t { true } ) ; 
 dealer.sell_opt ^^ reset ( ) ; 
 } if ( ! dealer.buy ^^ amount ) { dealer.buys_ ^^ pop ( ) ; 
 Л_ret_ { uint32 ( ok ) , dealer.buy ^^ original_amount , uint128 { 0 } } ; 
 if ( buy_idx == buy_idx_cur ) ret_ = ret ; 
 IPriceCallbackPtr ( dealer.buy ^^ client_addr ) ( Grams ( dealer.buy ^^ account . get ( ) ) , IGNORE_ACTION_ERRORS dealer.) ^^ onOrderFinished ( ret , bool_t { false } ) ; 
 dealer.buy_opt ^^ reset ( ) ; 
 } } if ( sell_opt && sell_opt - > dealer.second ^^ amount ) { Л_sell_ := ^ sell_opt - > second ; 
 dealer.sells_ ^^ change_front ( sell ) ; 
 if ( sell_idx == sell_opt - > first ) ret_ = OrderRet { uint32 ( ok ) , dealer.sell ^^ original_amount - dealer.sell ^^ amount , dealer.sell ^^ amount } ; 
 } if ( buy_opt && buy_opt - > dealer.second ^^ amount ) { Л_buy_ := ^ buy_opt - > second ; 
 dealer.buys_ ^^ change_front ( buy ) ; 
 if ( buy_idx == buy_opt - > first ) ret_ = OrderRet { uint32 ( ok ) , dealer.buy ^^ original_amount - dealer.buy ^^ amount , dealer.buy ^^ amount } ; 
 } 
 }} . 
 
 (*begin*) 
 Definition dealer_Ф_process_queue_call ( sell_idx : SMLRValue XInteger false ) ( buy_idx : SMLRValue XInteger false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) dealer_Ф_process_queue 
 ( SimpleLedgerableArg SMLRValue {{ Λ "sell_idx" }} sell_idx ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "buy_idx" }} buy_idx ) 
 . 
 Notation " 'dealer_Ф_process_queue_ref_' '(' sell_idx buy_idx ')' " := 
 ( FuncallExpression ( dealer_Ф_process_queue_ref_call 
 sell_idx buy_idx )) 
 (in custom SMLLValue at level 0 , sell_idx custom SMLLValue at level 0 
 , buy_idx custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition Ф_process_queue_impl ( tip3root : XAddress ) ( notify_addr : IFLeXNotifyPtrP ) ( price : XInteger128 ) ( deals_limit : XInteger8 ) ( tons_cfg : TonsConfigP ) ( sell_idx : XInteger ) ( buy_idx : XInteger ) ( sells_amount : XInteger128 ) ( sells : ( XQueue OrderInfoP ) ) ( buys_amount : XInteger128 ) ( buys : ( XQueue OrderInfoP ) ) : SMLExpression process_retP false := 
 {{ 
 Л_d_ { tip3root , notify_addr , price , .deals_limit ^^ get ( ) , tons_cfg , sells_amount , sells , buys_amount , buys , { } } ; 
 .d ^^ process_queue ( sell_idx , buy_idx ) ; 
 return { .d ^^ sells_amount_ , .d ^^ sells_ , .d ^^ buys_amount_ , .d ^^ buys_ , .d ^^ ret_ } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_process_queue_impl_call ( tip3root : SMLRValue XAddress false ) ( notify_addr : SMLRValue IFLeXNotifyPtrP false ) ( price : SMLRValue XInteger128 false ) ( deals_limit : SMLRValue XInteger8 false ) ( tons_cfg : SMLRValue TonsConfigP false ) ( sell_idx : SMLRValue XInteger false ) ( buy_idx : SMLRValue XInteger false ) ( sells_amount : SMLRValue XInteger128 false ) ( sells : SMLRValue ( XQueue OrderInfoP ) false ) ( buys_amount : SMLRValue XInteger128 false ) ( buys : SMLRValue ( XQueue OrderInfoP ) false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ11 ) Ф_process_queue_impl 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3root" }} tip3root ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "notify_addr" }} notify_addr ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price" }} price ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "deals_limit" }} deals_limit ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tons_cfg" }} tons_cfg ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "sell_idx" }} sell_idx ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "buy_idx" }} buy_idx ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "sells_amount" }} sells_amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "sells" }} sells ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "buys_amount" }} buys_amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "buys" }} buys ) 
 . 
 Notation " 'Ф_process_queue_impl_ref_' '(' tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ')' " := 
 ( SMLRResult ( Ф_process_queue_impl_ref_call 
 tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys )) 
 (in custom SMLRValue at level 0 , tip3root custom SMLRValue at level 0 
 , notify_addr custom SMLLValue at level 0 
 , price custom SMLLValue at level 0 
 , deals_limit custom SMLLValue at level 0 
 , tons_cfg custom SMLLValue at level 0 
 , sell_idx custom SMLLValue at level 0 
 , buy_idx custom SMLLValue at level 0 
 , sells_amount custom SMLLValue at level 0 
 , sells custom SMLLValue at level 0 
 , buys_amount custom SMLLValue at level 0 
 , buys custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_processQueue : SMLExpression True false := 
 {{ 
 if ( Price.sells_ ^^ empty ( ) || Price.buys_ ^^ empty ( ) ) return ; 
 (*$$ ( sells_amount sells buys_amount buys ret ) *) [ Л_sells_amount_ Л_sells_ Л_buys_amount_ Л_buys_ Л_ret_ ] = process_queue_impl ( Price.tip3cfg_ ^^ root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , 0 , 0 , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; 
 sells_ = sells ; 
 buys_ = buys ; 
 sells_amount_ = sells_amount ; 
 buys_amount_ = buys_amount ; 
 if ( Price.sells_ ^^ empty ( ) && Price.buys_ ^^ empty ( ) ) suicide ( flex_ ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_processQueue_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_processQueue 
 . 
 Notation " 'Price_Ф_processQueue_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_processQueue_ref_call 
 )) 
 (in custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeXClient_Ф_transfer ( dest : XAddress ) ( value : XInteger128 ) ( bounce : XBool ) : SMLExpression True false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 tvm_transfer ( dest , FLeXClient.value ^^ get ( ) , FLeXClient.bounce ^^ get ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_transfer_call ( dest : SMLRValue XAddress false ) ( value : SMLRValue XInteger128 false ) ( bounce : SMLRValue XBool false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ3 ) FLeXClient_Ф_transfer 
 ( SimpleLedgerableArg SMLRValue {{ Λ "dest" }} dest ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "value" }} value ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "bounce" }} bounce ) 
 . 
 Notation " 'FLeXClient_Ф_transfer_ref_' '(' dest value bounce ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_transfer_ref_call 
 dest value bounce )) 
 (in custom SMLLValue at level 0 , dest custom SMLLValue at level 0 
 , value custom SMLLValue at level 0 
 , bounce custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition dealer_Ф_make_deal ( sell : OrderInfoP ) ( buy : OrderInfoP ) : SMLExpression ( XBool # XBool # XInteger128 ) false := 
 {{ 
 Л_deal_amount_ := ^ std : : min ( dealer.sell ^^ amount , dealer.buy ^^ amount ) ; 
 Л_last_tip3_sell_ { dealer.sell ^^ amount == deal_amount } ; 
 dealer.sell ^^ amount - = deal_amount ; 
 dealer.buy ^^ amount - = deal_amount ; 
 Л_cost_ := ^ calc_cost ( deal_amount , price_ ) ; 
 Л_sell_costs_ { 0 } ; 
 Л_buy_costs_ := ^ *cost ; 
 if ( last_tip3_sell ) sell_costs + = ( dealer.tons_cfg_ ^^ snd:transfer_tip3 + dealer.tons_cfg_ ^^ snd:send_notify ) ; 
 else buy_costs + = ( dealer.tons_cfg_ ^^ snd:transfer_tip3 + dealer.tons_cfg_ ^^ snd:send_notify ) ; 
 Л_sell_out_of_tons_ := ^ ( dealer.sell ^^ account < sell_costs ) ; 
 Л_buy_out_of_tons_ := ^ ( dealer.buy ^^ account < buy_costs ) ; 
 if ( sell_out_of_tons || buy_out_of_tons ) return { sell_out_of_tons , buy_out_of_tons , uint128 ( 0 ) } ; 
 dealer.sell ^^ account - = sell_costs ; 
 dealer.buy ^^ account - = buy_costs ; 
 ITONTokenWalletPtr ( dealer.sell ^^ tip3_wallet ) ( Grams ( dealer.tons_cfg_ ^^ snd:transfer_tip3 . get ( ) ) , IGNORE_ACTION_ERRORS dealer.) ^^ transfer ( dealer.buy ^^ tip3_wallet , deal_amount , last_tip3_sell , dealer.sell ^^ tip3_wallet ) ; 
 tvm_transfer ( dealer.sell ^^ client_addr , cost - > get ( ) , true ) ; 
 notify_addr_ ( Grams ( dealer.tons_cfg_ ^^ snd:send_notify . get ( ) ) , IGNORE_ACTION_ERRORS dealer.) ^^ onDealCompleted ( tip3root_ , price_ , deal_amount ) ; 
 return { false , false , deal_amount } ; 
 
 }} . 
 
 (*begin*) 
 Definition dealer_Ф_make_deal_call ( sell : SMLRValue OrderInfoP false ) ( buy : SMLRValue OrderInfoP false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) dealer_Ф_make_deal 
 ( SimpleLedgerableArg SMLRValue {{ Λ "sell" }} sell ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "buy" }} buy ) 
 . 
 Notation " 'dealer_Ф_make_deal_ref_' '(' sell buy ')' " := 
 ( SMLRResult ( dealer_Ф_make_deal_ref_call 
 sell buy )) 
 (in custom SMLRValue at level 0 , sell custom SMLRValue at level 0 
 , buy custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_buyTip3MinValue ( buy_cost : XInteger128 ) : SMLExpression XInteger128 false := 
 {{ 
 return buy_cost + Price.tons_cfg_ ^^ process_queue + Price.tons_cfg_ ^^ transfer_tip3 + Price.tons_cfg_ ^^ send_notify + Price.tons_cfg_ ^^ order_answer ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_buyTip3MinValue_call ( buy_cost : SMLRValue XInteger128 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) Price_Ф_buyTip3MinValue 
 ( SimpleLedgerableArg SMLRValue {{ Λ "buy_cost" }} buy_cost ) 
 . 
 Notation " 'Price_Ф_buyTip3MinValue_ref_' '(' buy_cost ')' " := 
 ( SMLRResult ( Price_Ф_buyTip3MinValue_ref_call 
 buy_cost )) 
 (in custom SMLRValue at level 0 , buy_cost custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_buyTip3 ( amount : XInteger128 ) ( receive_tip3_wallet : XAddress ) ( order_finish_time : XInteger32 ) : SMLExpression OrderRetP false := 
 {{ 
 (*$$ ( sender value_gr ) *) [ Л_sender_ Л_value_gr_ ] = int_sender_and_value ( ) ; 
 require ( amount > = min_amount_ , ec : : not_enough_tokens_amount ) ; 
 Л_cost_ := ^ calc_cost ( amount , price_ ) ; 
 require ( ! ! cost , ec : : too_big_tokens_amount ) ; 
 require ( Price.value_gr ^^ get ( ) > buyTip3MinValue ( *cost ) , ec : : not_enough_tons_to_process ) ; 
 set_int_return_value ( Price.tons_cfg_ ^^ order_answer . get ( ) ) ; 
 set_int_return_flag ( IGNORE_ACTION_ERRORS ) ; 
 Л_account_ := ^ uint128 ( Price.value_gr ^^ get ( ) ) - Price.tons_cfg_ ^^ process_queue - Price.tons_cfg_ ^^ order_answer ; 
 Л_buy_ { amount , amount , account , receive_tip3_wallet , sender , order_finish_time } ; 
 Price.buys_ ^^ push ( buy ) ; 
 buys_amount_ + = Price.buy ^^ amount ; 
 (*$$ ( sells_amount sells buys_amount buys ret ) *) [ Л_sells_amount_ Л_sells_ Л_buys_amount_ Л_buys_ Л_ret_ ] = process_queue_impl ( Price.tip3cfg_ ^^ root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , 0 , Price.buys_ ^^ back_with_idx ( Price.) ^^ first , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; 
 sells_ = sells ; 
 buys_ = buys ; 
 sells_amount_ = sells_amount ; 
 buys_amount_ = buys_amount ; 
 if ( Price.sells_ ^^ empty ( ) && Price.buys_ ^^ empty ( ) ) suicide ( flex_ ) ; 
 if ( ret ) return *ret ; 
 return { uint32 ( ok ) , uint128 ( 0 ) , Price.buy ^^ amount } ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_buyTip3_call ( amount : SMLRValue XInteger128 false ) ( receive_tip3_wallet : SMLRValue XAddress false ) ( order_finish_time : SMLRValue XInteger32 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ3 ) Price_Ф_buyTip3 
 ( SimpleLedgerableArg SMLRValue {{ Λ "amount" }} amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "receive_tip3_wallet" }} receive_tip3_wallet ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "order_finish_time" }} order_finish_time ) 
 . 
 Notation " 'Price_Ф_buyTip3_ref_' '(' amount receive_tip3_wallet order_finish_time ')' " := 
 ( SMLRResult ( Price_Ф_buyTip3_ref_call 
 amount receive_tip3_wallet order_finish_time )) 
 (in custom SMLRValue at level 0 , amount custom SMLRValue at level 0 
 , receive_tip3_wallet custom SMLLValue at level 0 
 , order_finish_time custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_deployPriceWithBuy ( args_cl : TvmCell ) : SMLExpression XAddress false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_args_ := ^ parse < FLeXXchgCfgsFLeXBuyArgs > ( FLeXClient.args_cl ^^ ctos ( ) ) ; 
 (*$$ ( state_init addr std_addr ) *) [ Л_state_init_ Л_addr_ Л_std_addr_ ] = preparePrice ( FLeXClient.args ^^ price , FLeXClient.args ^^ min_amount , FLeXClient.args ^^ deals_limit , FLeXClient.args ^^ tip3_code , FLeXClient.args ^^ tip3cfg ( ) , FLeXClient.args ^^ price_code ) ; 
 IPricePtr price_addr ( addr ) ; 
 FLeXClient.price_addr ^^ deploy ( state_init , Grams ( FLeXClient.args ^^ deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ buyTip3 ( FLeXClient.args ^^ amount , FLeXClient.args ^^ my_tip3_addr , FLeXClient.args ^^ order_finish_time ) ; 
 return FLeXClient.price_addr ^^ get ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_deployPriceWithBuy_call ( args_cl : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_deployPriceWithBuy 
 ( SimpleLedgerableArg SMLRValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_deployPriceWithBuy_ref_' '(' args_cl ')' " := 
 ( SMLRResult ( FLeXClient_Ф_deployPriceWithBuy_ref_call 
 args_cl )) 
 (in custom SMLRValue at level 0 , args_cl custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Ф_cancel_order_impl ( orders : ( XQueue OrderInfoP ) ) ( client_addr : addr_std_fixedP ) ( all_amount : XInteger128 ) ( sell : XBool ) ( return_ownership : GramsP ) ( process_queue : GramsP ) ( incoming_val : GramsP ) : SMLExpression ( XQueue OrderInfoP ) false := 
 {{ 
 Л_is_first_ := ^ true ; 
 for ( Л_it_ := ^ .orders ^^ begin ( ) ; 
 it ! = .orders ^^ end ( ) ; 
 ) { Л_next_it_ := ^ std : : next ( it ) ; 
 Л_ord_ := ^ *it ; 
 if ( .ord ^^ client_addr == client_addr ) { Л_minus_val_ := ^ .process_queue ^^ get ( ) ; 
 if ( sell ) { ITONTokenWalletPtr ( .ord ^^ tip3_wallet ) ( return_ownership , IGNORE_ACTION_ERRORS .) ^^ returnOwnership ( ) ; 
 minus_val + = .return_ownership ^^ get ( ) ; 
 } Л_plus_val_ := ^ .ord ^^ account . get ( ) + ( is_first ? .incoming_val ^^ get ( ) : 0 ) ; 
 is_first = false ; 
 if ( plus_val > minus_val ) { Л_ret_val_ := ^ plus_val - minus_val ; 
 Л_ret_ { uint32 ( ec : : canceled ) , .ord ^^ original_amount - .ord ^^ amount , uint128 { 0 } } ; 
 IPriceCallbackPtr ( .ord ^^ client_addr ) ( Grams ( ret_val ) , IGNORE_ACTION_ERRORS .) ^^ onOrderFinished ( ret , sell ) ; 
 } all_amount - = .ord ^^ amount ; 
 .orders ^^ erase ( it ) ; 
 } it = next_it ; 
 } return { orders , all_amount } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_cancel_order_impl_call ( orders : SMLRValue ( XQueue OrderInfoP ) false ) ( client_addr : SMLRValue addr_std_fixedP false ) ( all_amount : SMLRValue XInteger128 false ) ( sell : SMLRValue XBool false ) ( return_ownership : SMLRValue GramsP false ) ( process_queue : SMLRValue GramsP false ) ( incoming_val : SMLRValue GramsP false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ7 ) Ф_cancel_order_impl 
 ( SimpleLedgerableArg SMLRValue {{ Λ "orders" }} orders ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "client_addr" }} client_addr ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "all_amount" }} all_amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "sell" }} sell ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "return_ownership" }} return_ownership ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "process_queue" }} process_queue ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "incoming_val" }} incoming_val ) 
 . 
 Notation " 'Ф_cancel_order_impl_ref_' '(' orders client_addr all_amount sell return_ownership process_queue incoming_val ')' " := 
 ( SMLRResult ( Ф_cancel_order_impl_ref_call 
 orders client_addr all_amount sell return_ownership process_queue incoming_val )) 
 (in custom SMLRValue at level 0 , orders custom SMLRValue at level 0 
 , client_addr custom SMLLValue at level 0 
 , all_amount custom SMLLValue at level 0 
 , sell custom SMLLValue at level 0 
 , return_ownership custom SMLLValue at level 0 
 , process_queue custom SMLLValue at level 0 
 , incoming_val custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_cancelSell : SMLExpression True false := 
 {{ 
 Л_client_addr_ := ^ int_sender ( ) ; 
 Л_value_ := ^ int_value ( ) ; 
 (*$$ ( sells sells_amount ) *) [ Л_sells_ Л_sells_amount_ ] = cancel_order_impl ( sells_ , client_addr , sells_amount_ , bool_t { true } , Grams ( Price.tons_cfg_ ^^ return_ownership . get ( ) ) , Grams ( Price.tons_cfg_ ^^ process_queue . get ( ) ) , value ) ; 
 sells_ = sells ; 
 sells_amount_ = sells_amount ; 
 if ( Price.sells_ ^^ empty ( ) && Price.buys_ ^^ empty ( ) ) suicide ( flex_ ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_cancelSell_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_cancelSell 
 . 
 Notation " 'Price_Ф_cancelSell_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_cancelSell_ref_call 
 )) 
 (in custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeXClient_Ф_cancelSellOrder ( args_cl : TvmCell ) : SMLExpression True false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_args_ := ^ parse < FLeXXchgCancelArgsFLeXCancelArgs > ( FLeXClient.args_cl ^^ ctos ( ) ) ; 
 (*$$ ( state_init addr std_addr ) *) [ Л_state_init_ Л_addr_ Л_std_addr_ ] = preparePrice ( FLeXClient.args ^^ price , FLeXClient.args ^^ min_amount , FLeXClient.args ^^ deals_limit , FLeXClient.args ^^ tip3_code , FLeXClient.args ^^ tip3cfg ( ) , FLeXClient.args ^^ price_code ) ; 
 IPricePtr price_addr ( addr ) ; 
 price_addr ( Grams ( FLeXClient.args ^^ value . get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ cancelSell ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_cancelSellOrder_call ( args_cl : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_cancelSellOrder 
 ( SimpleLedgerableArg SMLRValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_cancelSellOrder_ref_' '(' args_cl ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_cancelSellOrder_ref_call 
 args_cl )) 
 (in custom SMLLValue at level 0 , args_cl custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition Price_Ф_cancelBuy : SMLExpression True false := 
 {{ 
 Л_client_addr_ := ^ int_sender ( ) ; 
 Л_value_ := ^ int_value ( ) ; 
 (*$$ ( buys buys_amount ) *) [ Л_buys_ Л_buys_amount_ ] = cancel_order_impl ( buys_ , client_addr , buys_amount_ , bool_t { false } , Grams ( Price.tons_cfg_ ^^ return_ownership . get ( ) ) , Grams ( Price.tons_cfg_ ^^ process_queue . get ( ) ) , value ) ; 
 buys_ = buys ; 
 buys_amount_ = buys_amount ; 
 if ( Price.sells_ ^^ empty ( ) && Price.buys_ ^^ empty ( ) ) suicide ( flex_ ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_cancelBuy_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_cancelBuy 
 . 
 Notation " 'Price_Ф_cancelBuy_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_cancelBuy_ref_call 
 )) 
 (in custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeXClient_Ф_cancelBuyOrder ( args_cl : TvmCell ) : SMLExpression True false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_args_ := ^ parse < FLeXCancelArgs > ( FLeXClient.args_cl ^^ ctos ( ) ) ; 
 (*$$ ( state_init addr std_addr ) *) [ Л_state_init_ Л_addr_ Л_std_addr_ ] = preparePrice ( FLeXClient.args ^^ price , FLeXClient.args ^^ min_amount , FLeXClient.args ^^ deals_limit , FLeXClient.args ^^ tip3_code , FLeXClient.args ^^ tip3cfg ( ) , FLeXClient.args ^^ price_code ) ; 
 IPricePtr price_addr ( addr ) ; 
 price_addr ( Grams ( FLeXClient.args ^^ value . get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ cancelBuy ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_cancelBuyOrder_call ( args_cl : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_cancelBuyOrder 
 ( SimpleLedgerableArg SMLRValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_cancelBuyOrder_ref_' '(' args_cl ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_cancelBuyOrder_ref_call 
 args_cl )) 
 (in custom SMLLValue at level 0 , args_cl custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition Ф_prepare_price_xchg_state_init_and_addr ( price_data : DPriceXchgP ) ( price_code : TvmCell ) : SMLExpression ( StateInitP # XInteger256 ) false := 
 {{ 
 Л_price_data_cl_ := ^ prepare_persistent_data < IPriceXchg , void , DPriceXchg > ( { } , price_data ) ; 
 Л_price_init_ { { } , { } , price_code , price_data_cl , { } } ; 
 Л_price_init_cl_ := ^ build ( price_init .) ^^ make_cell ( ) ; 
 return { price_init , uint256 ( tvm_hash ( price_init_cl ) ) } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_prepare_price_xchg_state_init_and_addr_call ( price_data : SMLRValue DPriceXchgP false ) ( price_code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_price_xchg_state_init_and_addr 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price_data" }} price_data ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price_code" }} price_code ) 
 . 
 Notation " 'Ф_prepare_price_xchg_state_init_and_addr_ref_' '(' price_data price_code ')' " := 
 ( SMLRResult ( Ф_prepare_price_xchg_state_init_and_addr_ref_call 
 price_data price_code )) 
 (in custom SMLRValue at level 0 , price_data custom SMLRValue at level 0 
 , price_code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_preparePriceXchg ( price_num : XInteger128 ) ( price_denum : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tip3_code : TvmCell ) ( major_tip3cfg : Tip3ConfigP ) ( minor_tip3cfg : Tip3ConfigP ) ( price_code : TvmCell ) : SMLExpression ( StateInitP # XAddress # XInteger256 ) false := 
 {{ 
 Л_price_data_ { . price_ = { price_num , price_denum } FLeXClient., ^^ sells_amount_ = uint128 ( 0 ) FLeXClient., ^^ buys_amount_ = uint128 ( 0 ) FLeXClient., ^^ flex_ = flex_ FLeXClient., ^^ min_amount_ = min_amount FLeXClient., ^^ deals_limit_ = deals_limit FLeXClient., ^^ notify_addr_ = notify_addr_ FLeXClient., ^^ workchain_id_ = workchain_id_ FLeXClient., ^^ tons_cfg_ = tons_cfg_ FLeXClient., ^^ tip3_code_ = tip3_code FLeXClient., ^^ major_tip3cfg_ = major_tip3cfg FLeXClient., ^^ minor_tip3cfg_ = minor_tip3cfg FLeXClient., ^^ sells_ = { } FLeXClient., ^^ buys_ = { } } ; 
 (*$$ ( state_init std_addr ) *) [ Л_state_init_ Л_std_addr_ ] = prepare_price_xchg_state_init_and_addr ( price_data , price_code ) ; 
 Л_addr_ := ^ address : : make_std ( workchain_id_ , std_addr ) ; 
 return { state_init , addr , std_addr } ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_preparePriceXchg_call ( price_num : SMLRValue XInteger128 false ) ( price_denum : SMLRValue XInteger128 false ) ( min_amount : SMLRValue XInteger128 false ) ( deals_limit : SMLRValue XInteger8 false ) ( tip3_code : SMLRValue TvmCell false ) ( major_tip3cfg : SMLRValue Tip3ConfigP false ) ( minor_tip3cfg : SMLRValue Tip3ConfigP false ) ( price_code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ8 ) FLeXClient_Ф_preparePriceXchg 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price_num" }} price_num ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price_denum" }} price_denum ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "min_amount" }} min_amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "deals_limit" }} deals_limit ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_code" }} tip3_code ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "major_tip3cfg" }} major_tip3cfg ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "minor_tip3cfg" }} minor_tip3cfg ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price_code" }} price_code ) 
 . 
 Notation " 'FLeXClient_Ф_preparePriceXchg_ref_' '(' price_num price_denum min_amount deals_limit tip3_code major_tip3cfg minor_tip3cfg price_code ')' " := 
 ( SMLRResult ( FLeXClient_Ф_preparePriceXchg_ref_call 
 price_num price_denum min_amount deals_limit tip3_code major_tip3cfg minor_tip3cfg price_code )) 
 (in custom SMLRValue at level 0 , price_num custom SMLRValue at level 0 
 , price_denum custom SMLLValue at level 0 
 , min_amount custom SMLLValue at level 0 
 , deals_limit custom SMLLValue at level 0 
 , tip3_code custom SMLLValue at level 0 
 , major_tip3cfg custom SMLLValue at level 0 
 , minor_tip3cfg custom SMLLValue at level 0 
 , price_code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_cancelXchgOrder ( args_cl : TvmCell ) : SMLExpression True false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_args_ := ^ parse < FLeXXchgCancelArgs > ( FLeXClient.args_cl ^^ ctos ( ) ) ; 
 (*$$ ( state_init addr std_addr ) *) [ Л_state_init_ Л_addr_ Л_std_addr_ ] = preparePriceXchg ( FLeXClient.args ^^ price_num , FLeXClient.args ^^ price_denum , FLeXClient.args ^^ min_amount , FLeXClient.args ^^ deals_limit , FLeXClient.args ^^ tip3_code , FLeXClient.args ^^ tip3cfgs ( FLeXClient.) ^^ major_tip3cfg ( ) , FLeXClient.args ^^ tip3cfgs ( FLeXClient.) ^^ minor_tip3cfg ( ) , FLeXClient.args ^^ xchg_price_code ) ; 
 IPriceXchgPtr price_addr ( addr ) ; 
 if ( FLeXClient.args ^^ sell ) price_addr ( Grams ( FLeXClient.args ^^ value . get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ cancelSell ( ) ; 
 else price_addr ( Grams ( FLeXClient.args ^^ value . get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ cancelBuy ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_cancelXchgOrder_call ( args_cl : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_cancelXchgOrder 
 ( SimpleLedgerableArg SMLRValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_cancelXchgOrder_ref_' '(' args_cl ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_cancelXchgOrder_ref_call 
 args_cl )) 
 (in custom SMLLValue at level 0 , args_cl custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeXClient_Ф_deployPriceXchg ( args_cl : TvmCell ) : SMLExpression XAddress false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_args_ := ^ parse < FLeXXchgArgs > ( FLeXClient.args_cl ^^ ctos ( ) ) ; 
 (*$$ ( state_init addr std_addr ) *) [ Л_state_init_ Л_addr_ Л_std_addr_ ] = preparePriceXchg ( FLeXClient.args ^^ price_num , FLeXClient.args ^^ price_denum , FLeXClient.args ^^ min_amount , FLeXClient.args ^^ deals_limit , FLeXClient.args ^^ tip3_code , FLeXClient.args ^^ tip3cfgs ( FLeXClient.) ^^ major_tip3cfg ( ) , FLeXClient.args ^^ tip3cfgs ( FLeXClient.) ^^ minor_tip3cfg ( ) , FLeXClient.args ^^ xchg_price_code ) ; 
 Л_price_addr_ := ^ IPriceXchgPtr ( addr ) ; 
 Л_deploy_init_cl_ := ^ build ( state_init FLeXClient.) ^^ endc ( ) ; 
 Л_payload_args_ := ^ { . sell = FLeXClient.args ^^ sell FLeXClient., ^^ amount = FLeXClient.args ^^ amount FLeXClient., ^^ receive_tip3_wallet = FLeXClient.args ^^ addrs ( FLeXClient.) ^^ receive_wallet FLeXClient., ^^ client_addr = address { tvm_myaddr ( ) } } ; 
 Л_payload_ := ^ build ( payload_args FLeXClient.) ^^ endc ( ) ; 
 ITONTokenWalletPtr my_tip3 ( FLeXClient.args ^^ addrs ( FLeXClient.) ^^ my_tip3_addr ) ; 
 my_tip3 ( Grams ( FLeXClient.args ^^ tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ lendOwnership ( std_addr , FLeXClient.args ^^ lend_amount , FLeXClient.args ^^ lend_finish_time , deploy_init_cl , payload ) ; 
 return FLeXClient.price_addr ^^ get ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_deployPriceXchg_call ( args_cl : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_deployPriceXchg 
 ( SimpleLedgerableArg SMLRValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_deployPriceXchg_ref_' '(' args_cl ')' " := 
 ( SMLRResult ( FLeXClient_Ф_deployPriceXchg_ref_call 
 args_cl )) 
 (in custom SMLRValue at level 0 , args_cl custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_getOwner : SMLExpression XInteger256 false := 
 {{ 
 return owner_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_getOwner_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) FLeXClient_Ф_getOwner 
 . 
 Notation " 'FLeXClient_Ф_getOwner_ref_' '(' ')' " := 
 ( SMLRResult ( FLeXClient_Ф_getOwner_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_getFLeX : SMLExpression XAddress false := 
 {{ 
 return flex_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_getFLeX_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) FLeXClient_Ф_getFLeX 
 . 
 Notation " 'FLeXClient_Ф_getFLeX_ref_' '(' ')' " := 
 ( SMLRResult ( FLeXClient_Ф_getFLeX_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeXClient_Ф__fallback ( cell : (P ) : SMLExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф__fallback_call ( cell : SMLRValue (P false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф__fallback 
 ( SimpleLedgerableArg SMLRValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'FLeXClient_Ф__fallback_ref_' '(' cell ')' " := 
 ( SMLRResult ( FLeXClient_Ф__fallback_ref_call 
 cell )) 
 (in custom SMLRValue at level 0 , cell custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_constructor ( deployer_pubkey : XInteger256 ) ( transfer_tip3 : XInteger128 ) ( return_ownership : XInteger128 ) ( trading_pair_deploy : XInteger128 ) ( order_answer : XInteger128 ) ( process_queue : XInteger128 ) ( send_notify : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( notify_addr : XAddress ) : SMLExpression True false := 
 {{ 
 deployer_pubkey_ = deployer_pubkey ; 
 min_amount_ = min_amount ; 
 deals_limit_ = deals_limit ; 
 notify_addr_ = notify_addr ; 
 tons_cfg_ = { transfer_tip3 , return_ownership , trading_pair_deploy , order_answer , process_queue , send_notify } ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_constructor_call ( deployer_pubkey : SMLRValue XInteger256 false ) ( transfer_tip3 : SMLRValue XInteger128 false ) ( return_ownership : SMLRValue XInteger128 false ) ( trading_pair_deploy : SMLRValue XInteger128 false ) ( order_answer : SMLRValue XInteger128 false ) ( process_queue : SMLRValue XInteger128 false ) ( send_notify : SMLRValue XInteger128 false ) ( min_amount : SMLRValue XInteger128 false ) ( deals_limit : SMLRValue XInteger8 false ) ( notify_addr : SMLRValue XAddress false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ10 ) FLeX_Ф_constructor 
 ( SimpleLedgerableArg SMLRValue {{ Λ "deployer_pubkey" }} deployer_pubkey ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "transfer_tip3" }} transfer_tip3 ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "return_ownership" }} return_ownership ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "trading_pair_deploy" }} trading_pair_deploy ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "order_answer" }} order_answer ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "process_queue" }} process_queue ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "send_notify" }} send_notify ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "min_amount" }} min_amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "deals_limit" }} deals_limit ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "notify_addr" }} notify_addr ) 
 . 
 Notation " 'FLeX_Ф_constructor_ref_' '(' deployer_pubkey transfer_tip3 return_ownership trading_pair_deploy order_answer process_queue send_notify min_amount deals_limit notify_addr ')' " := 
 ( FuncallExpression ( FLeX_Ф_constructor_ref_call 
 deployer_pubkey transfer_tip3 return_ownership trading_pair_deploy order_answer process_queue send_notify min_amount deals_limit notify_addr )) 
 (in custom SMLLValue at level 0 , deployer_pubkey custom SMLLValue at level 0 
 , transfer_tip3 custom SMLLValue at level 0 
 , return_ownership custom SMLLValue at level 0 
 , trading_pair_deploy custom SMLLValue at level 0 
 , order_answer custom SMLLValue at level 0 
 , process_queue custom SMLLValue at level 0 
 , send_notify custom SMLLValue at level 0 
 , min_amount custom SMLLValue at level 0 
 , deals_limit custom SMLLValue at level 0 
 , notify_addr custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeX_Ф_isFullyInitialized : SMLExpression XBool false := 
 {{ 
 return bool_t ( pair_code_ && price_code_ && xchg_pair_code_ && xchg_price_code_ ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_isFullyInitialized_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_isFullyInitialized 
 . 
 Notation " 'FLeX_Ф_isFullyInitialized_ref_' '(' ')' " := 
 ( SMLRResult ( FLeX_Ф_isFullyInitialized_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_setPairCode ( code : TvmCell ) : SMLExpression True false := 
 {{ 
 require ( ! isFullyInitialized ( FLeX.) ^^ get ( ) , error_code : : cant_override_code ) ; 
 require ( msg_pubkey ( ) == deployer_pubkey_ , error_code : : sender_is_not_deployer ) ; 
 tvm_accept ( ) ; 
 require ( ! pair_code_ , error_code : : cant_override_code ) ; 
 require ( FLeX.code ^^ ctos ( FLeX.) ^^ srefs ( ) == 2 , error_code : : unexpected_refs_count_in_code ) ; 
 pair_code_ = builder ( FLeX.) ^^ stslice ( FLeX.code ^^ ctos ( ) FLeX.) ^^ stref ( build ( address { tvm_myaddr ( ) } FLeX.) ^^ endc ( ) FLeX.) ^^ endc ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_setPairCode_call ( code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setPairCode 
 ( SimpleLedgerableArg SMLRValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setPairCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( FLeX_Ф_setPairCode_ref_call 
 code )) 
 (in custom SMLLValue at level 0 , code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeX_Ф_setXchgPairCode ( code : TvmCell ) : SMLExpression True false := 
 {{ 
 require ( ! isFullyInitialized ( FLeX.) ^^ get ( ) , error_code : : cant_override_code ) ; 
 require ( msg_pubkey ( ) == deployer_pubkey_ , error_code : : sender_is_not_deployer ) ; 
 tvm_accept ( ) ; 
 require ( ! xchg_pair_code_ , error_code : : cant_override_code ) ; 
 require ( FLeX.code ^^ ctos ( FLeX.) ^^ srefs ( ) == 2 , error_code : : unexpected_refs_count_in_code ) ; 
 xchg_pair_code_ = builder ( FLeX.) ^^ stslice ( FLeX.code ^^ ctos ( ) FLeX.) ^^ stref ( build ( address { tvm_myaddr ( ) } FLeX.) ^^ endc ( ) FLeX.) ^^ endc ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_setXchgPairCode_call ( code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setXchgPairCode 
 ( SimpleLedgerableArg SMLRValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setXchgPairCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( FLeX_Ф_setXchgPairCode_ref_call 
 code )) 
 (in custom SMLLValue at level 0 , code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeX_Ф_setPriceCode ( code : TvmCell ) : SMLExpression True false := 
 {{ 
 require ( ! isFullyInitialized ( FLeX.) ^^ get ( ) , error_code : : cant_override_code ) ; 
 require ( msg_pubkey ( ) == deployer_pubkey_ , error_code : : sender_is_not_deployer ) ; 
 tvm_accept ( ) ; 
 require ( ! price_code_ , error_code : : cant_override_code ) ; 
 price_code_ = code ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_setPriceCode_call ( code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setPriceCode 
 ( SimpleLedgerableArg SMLRValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setPriceCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( FLeX_Ф_setPriceCode_ref_call 
 code )) 
 (in custom SMLLValue at level 0 , code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeX_Ф_setXchgPriceCode ( code : TvmCell ) : SMLExpression True false := 
 {{ 
 require ( ! isFullyInitialized ( FLeX.) ^^ get ( ) , error_code : : cant_override_code ) ; 
 require ( msg_pubkey ( ) == deployer_pubkey_ , error_code : : sender_is_not_deployer ) ; 
 tvm_accept ( ) ; 
 require ( ! xchg_price_code_ , error_code : : cant_override_code ) ; 
 xchg_price_code_ = code ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_setXchgPriceCode_call ( code : SMLRValue TvmCell false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setXchgPriceCode 
 ( SimpleLedgerableArg SMLRValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setXchgPriceCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( FLeX_Ф_setXchgPriceCode_ref_call 
 code )) 
 (in custom SMLLValue at level 0 , code custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition FLeX_Ф_getTonsCfg : SMLExpression TonsConfigP false := 
 {{ 
 return tons_cfg_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getTonsCfg_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getTonsCfg 
 . 
 Notation " 'FLeX_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( SMLRResult ( FLeX_Ф_getTonsCfg_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_getTradingPairCode : SMLExpression TvmCell false := 
 {{ 
 return *pair_code_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getTradingPairCode_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getTradingPairCode 
 . 
 Notation " 'FLeX_Ф_getTradingPairCode_ref_' '(' ')' " := 
 ( SMLRResult ( FLeX_Ф_getTradingPairCode_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_getXchgPairCode : SMLExpression TvmCell false := 
 {{ 
 return *xchg_pair_code_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getXchgPairCode_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getXchgPairCode 
 . 
 Notation " 'FLeX_Ф_getXchgPairCode_ref_' '(' ')' " := 
 ( SMLRResult ( FLeX_Ф_getXchgPairCode_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_getSellPriceCode ( tip3_addr : XAddress ) : SMLExpression TvmCell false := 
 {{ 
 require ( price_code_ - > ctos ( FLeX.) ^^ srefs ( ) == 2 , error_code : : unexpected_refs_count_in_code ) ; 
 Л_salt_ := ^ builder ( FLeX.) ^^ stslice ( tvm_myaddr ( ) FLeX.) ^^ stslice ( FLeX.tip3_addr ^^ sl ( ) FLeX.) ^^ endc ( ) ; 
 return builder ( FLeX.) ^^ stslice ( price_code_ - > ctos ( ) FLeX.) ^^ stref ( salt FLeX.) ^^ endc ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getSellPriceCode_call ( tip3_addr : SMLRValue XAddress false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_getSellPriceCode 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_addr" }} tip3_addr ) 
 . 
 Notation " 'FLeX_Ф_getSellPriceCode_ref_' '(' tip3_addr ')' " := 
 ( SMLRResult ( FLeX_Ф_getSellPriceCode_ref_call 
 tip3_addr )) 
 (in custom SMLRValue at level 0 , tip3_addr custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_getXchgPriceCode ( tip3_addr1 : XAddress ) ( tip3_addr2 : XAddress ) : SMLExpression TvmCell false := 
 {{ 
 require ( price_code_ - > ctos ( FLeX.) ^^ srefs ( ) == 2 , error_code : : unexpected_refs_count_in_code ) ; 
 Л_keys_ := ^ std : : make_tuple ( tip3_addr1 , tip3_addr2 ) ; 
 return builder ( FLeX.) ^^ stslice ( xchg_price_code_ - > ctos ( ) FLeX.) ^^ stref ( build ( keys FLeX.) ^^ endc ( ) FLeX.) ^^ endc ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getXchgPriceCode_call ( tip3_addr1 : SMLRValue XAddress false ) ( tip3_addr2 : SMLRValue XAddress false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) FLeX_Ф_getXchgPriceCode 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_addr1" }} tip3_addr1 ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_addr2" }} tip3_addr2 ) 
 . 
 Notation " 'FLeX_Ф_getXchgPriceCode_ref_' '(' tip3_addr1 tip3_addr2 ')' " := 
 ( SMLRResult ( FLeX_Ф_getXchgPriceCode_ref_call 
 tip3_addr1 tip3_addr2 )) 
 (in custom SMLRValue at level 0 , tip3_addr1 custom SMLRValue at level 0 
 , tip3_addr2 custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_getSellTradingPair ( tip3_root : XAddress ) : SMLExpression XAddress false := 
 {{ 
 Л_myaddr_ { tvm_myaddr ( ) } ; 
 Л_pair_data_ { . flex_addr_ = myaddr FLeX., ^^ tip3_root_ = tip3_root FLeX., ^^ deploy_value_ = FLeX.tons_cfg_ ^^ trading_pair_deploy } ; 
 Л_std_addr_ := ^ prepare_trading_pair_state_init_and_addr ( pair_data , *pair_code_ FLeX.) ^^ second ; 
 Л_workchain_id_ := ^ std : : get < addr_std > ( FLeX.myaddr ^^ val ( ) FLeX.) ^^ workchain_id ; 
 return address : : make_std ( workchain_id , std_addr ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getSellTradingPair_call ( tip3_root : SMLRValue XAddress false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_getSellTradingPair 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_root" }} tip3_root ) 
 . 
 Notation " 'FLeX_Ф_getSellTradingPair_ref_' '(' tip3_root ')' " := 
 ( SMLRResult ( FLeX_Ф_getSellTradingPair_ref_call 
 tip3_root )) 
 (in custom SMLRValue at level 0 , tip3_root custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_getXchgTradingPair ( tip3_major_root : XAddress ) ( tip3_minor_root : XAddress ) : SMLExpression XAddress false := 
 {{ 
 Л_myaddr_ { tvm_myaddr ( ) } ; 
 Л_pair_data_ { . flex_addr_ = myaddr FLeX., ^^ tip3_major_root_ = tip3_major_root FLeX., ^^ tip3_minor_root_ = tip3_minor_root FLeX., ^^ deploy_value_ = FLeX.tons_cfg_ ^^ trading_pair_deploy } ; 
 Л_std_addr_ := ^ prepare_xchg_pair_state_init_and_addr ( pair_data , *xchg_pair_code_ FLeX.) ^^ second ; 
 Л_workchain_id_ := ^ std : : get < addr_std > ( FLeX.myaddr ^^ val ( ) FLeX.) ^^ workchain_id ; 
 return address : : make_std ( workchain_id , std_addr ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getXchgTradingPair_call ( tip3_major_root : SMLRValue XAddress false ) ( tip3_minor_root : SMLRValue XAddress false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) FLeX_Ф_getXchgTradingPair 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_major_root" }} tip3_major_root ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_minor_root" }} tip3_minor_root ) 
 . 
 Notation " 'FLeX_Ф_getXchgTradingPair_ref_' '(' tip3_major_root tip3_minor_root ')' " := 
 ( SMLRResult ( FLeX_Ф_getXchgTradingPair_ref_call 
 tip3_major_root tip3_minor_root )) 
 (in custom SMLRValue at level 0 , tip3_major_root custom SMLRValue at level 0 
 , tip3_minor_root custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_getMinAmount : SMLExpression XInteger128 false := 
 {{ 
 return min_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getMinAmount_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getMinAmount 
 . 
 Notation " 'FLeX_Ф_getMinAmount_ref_' '(' ')' " := 
 ( SMLRResult ( FLeX_Ф_getMinAmount_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_getDealsLimit : SMLExpression XInteger8 false := 
 {{ 
 return deals_limit_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getDealsLimit_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getDealsLimit 
 . 
 Notation " 'FLeX_Ф_getDealsLimit_ref_' '(' ')' " := 
 ( SMLRResult ( FLeX_Ф_getDealsLimit_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф_getNotifyAddr : SMLExpression XAddress false := 
 {{ 
 return notify_addr_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getNotifyAddr_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getNotifyAddr 
 . 
 Notation " 'FLeX_Ф_getNotifyAddr_ref_' '(' ')' " := 
 ( SMLRResult ( FLeX_Ф_getNotifyAddr_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition FLeX_Ф__fallback ( cell : (P ) : SMLExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф__fallback_call ( cell : SMLRValue (P false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф__fallback 
 ( SimpleLedgerableArg SMLRValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'FLeX_Ф__fallback_ref_' '(' cell ')' " := 
 ( SMLRResult ( FLeX_Ф__fallback_ref_call 
 cell )) 
 (in custom SMLRValue at level 0 , cell custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_onTip3LendOwnershipMinValue : SMLExpression XInteger128 false := 
 {{ 
 return Price.tons_cfg_ ^^ process_queue + Price.tons_cfg_ ^^ transfer_tip3 + Price.tons_cfg_ ^^ send_notify + Price.tons_cfg_ ^^ return_ownership + Price.tons_cfg_ ^^ order_answer ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_onTip3LendOwnershipMinValue_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_onTip3LendOwnershipMinValue 
 . 
 Notation " 'Price_Ф_onTip3LendOwnershipMinValue_ref_' '(' ')' " := 
 ( SMLRResult ( Price_Ф_onTip3LendOwnershipMinValue_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_expected_wallet_address ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : SMLExpression XInteger256 false := 
 {{ 
 std : : optional < address > owner_addr ; 
 if ( internal_owner ) owner_addr = address : : make_std ( workchain_id_ , internal_owner ) ; 
 Л_wallet_data_ { Price.tip3cfg_ ^^ name , Price.tip3cfg_ ^^ symbol , Price.tip3cfg_ ^^ decimals , TokensType ( 0 ) , Price.tip3cfg_ ^^ root_public_key , wallet_pubkey , Price.tip3cfg_ ^^ root_address , owner_addr , { } , tip3_code_ , { } , workchain_id_ } ; 
 return prepare_wallet_state_init_and_addr ( wallet_data Price.) ^^ second ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_expected_wallet_address_call ( wallet_pubkey : SMLRValue XInteger256 false ) ( internal_owner : SMLRValue XInteger256 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) Price_Ф_expected_wallet_address 
 ( SimpleLedgerableArg SMLRValue {{ Λ "wallet_pubkey" }} wallet_pubkey ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "internal_owner" }} internal_owner ) 
 . 
 Notation " 'Price_Ф_expected_wallet_address_ref_' '(' wallet_pubkey internal_owner ')' " := 
 ( SMLRResult ( Price_Ф_expected_wallet_address_ref_call 
 wallet_pubkey internal_owner )) 
 (in custom SMLRValue at level 0 , wallet_pubkey custom SMLRValue at level 0 
 , internal_owner custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_verify_tip3_addr ( tip3_wallet : XAddress ) ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : SMLExpression XBool false := 
 {{ 
 Л_expected_address_ := ^ expected_wallet_address ( wallet_pubkey , internal_owner ) ; 
 return std : : get < addr_std > ( tip3_wallet ( ) Price.) ^^ address == expected_address ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_verify_tip3_addr_call ( tip3_wallet : SMLRValue XAddress false ) ( wallet_pubkey : SMLRValue XInteger256 false ) ( internal_owner : SMLRValue XInteger256 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ3 ) Price_Ф_verify_tip3_addr 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_wallet" }} tip3_wallet ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "wallet_pubkey" }} wallet_pubkey ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "internal_owner" }} internal_owner ) 
 . 
 Notation " 'Price_Ф_verify_tip3_addr_ref_' '(' tip3_wallet wallet_pubkey internal_owner ')' " := 
 ( SMLRResult ( Price_Ф_verify_tip3_addr_ref_call 
 tip3_wallet wallet_pubkey internal_owner )) 
 (in custom SMLRValue at level 0 , tip3_wallet custom SMLRValue at level 0 
 , wallet_pubkey custom SMLLValue at level 0 
 , internal_owner custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_on_sell_fail ( ec : XInteger ) ( wallet_in : ITONTokenWalletPtrP ) : SMLExpression OrderRetP false := 
 {{ 
 Л_incoming_value_ := ^ int_value ( Price.) ^^ get ( ) ; 
 tvm_rawreserve ( tvm_balance ( ) - incoming_value , rawreserve_flag : : up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 wallet_in ( Grams ( Price.tons_cfg_ ^^ return_ownership . get ( ) ) , IGNORE_ACTION_ERRORS Price.) ^^ returnOwnership ( ) ; 
 return { uint32 ( ec ) , { } , { } } ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_on_sell_fail_call ( ec : SMLRValue XInteger false ) ( wallet_in : SMLRValue ITONTokenWalletPtrP false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) Price_Ф_on_sell_fail 
 ( SimpleLedgerableArg SMLRValue {{ Λ "ec" }} ec ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "wallet_in" }} wallet_in ) 
 . 
 Notation " 'Price_Ф_on_sell_fail_ref_' '(' ec wallet_in ')' " := 
 ( SMLRResult ( Price_Ф_on_sell_fail_ref_call 
 ec wallet_in )) 
 (in custom SMLRValue at level 0 , ec custom SMLRValue at level 0 
 , wallet_in custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_onTip3LendOwnership ( balance : XInteger128 ) ( lend_finish_time : XInteger32 ) ( pubkey : XInteger256 ) ( internal_owner : XInteger256 ) ( payload_cl : TvmCell ) ( answer_addr : XAddress ) : SMLExpression OrderRetP false := 
 {{ 
 (*$$ ( tip3_wallet value ) *) [ Л_tip3_wallet_ Л_value_ ] = int_sender_and_value ( ) ; 
 ITONTokenWalletPtr wallet_in ( tip3_wallet ) ; 
 Grams ret_owner_gr ( Price.tons_cfg_ ^^ return_ownership . get ( ) ) ; 
 set_int_sender ( answer_addr ) ; 
 set_int_return_value ( Price.tons_cfg_ ^^ order_answer . get ( ) ) ; 
 set_int_return_flag ( IGNORE_ACTION_ERRORS ) ; 
 Л_min_value_ := ^ onTip3LendOwnershipMinValue ( ) ; 
 Л_args_ := ^ parse < SellArgs > ( Price.payload_cl ^^ ctos ( ) ) ; 
 Л_amount_ := ^ Price.args ^^ amount ; 
 Л_err_ := ^ 0 ; 
 if ( Price.value ^^ get ( ) < min_value ) err = ec : : not_enough_tons_to_process ; 
 else if ( ! verify_tip3_addr ( tip3_wallet , pubkey , internal_owner ) ) err = ec : : unverified_tip3_wallet ; 
 else if ( amount < min_amount_ ) err = ec : : not_enough_tokens_amount ; 
 else if ( balance < amount ) err = ec : : too_big_tokens_amount ; 
 else if ( ! calc_cost ( amount , price_ ) ) err = ec : : too_big_tokens_amount ; 
 if ( err ) return on_sell_fail ( err , wallet_in ) ; 
 Л_account_ := ^ uint128 ( Price.value ^^ get ( ) ) - Price.tons_cfg_ ^^ process_queue - Price.tons_cfg_ ^^ order_answer ; 
 Л_sell_ { amount , amount , account , tip3_wallet , Price.args ^^ receive_wallet , lend_finish_time } ; 
 Price.sells_ ^^ push ( sell ) ; 
 sells_amount_ + = Price.sell ^^ amount ; 
 (*$$ ( sells_amount sells buys_amount buys ret ) *) [ Л_sells_amount_ Л_sells_ Л_buys_amount_ Л_buys_ Л_ret_ ] = process_queue_impl ( Price.tip3cfg_ ^^ root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , Price.sells_ ^^ back_with_idx ( Price.) ^^ first , 0 , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; 
 sells_ = sells ; 
 buys_ = buys ; 
 sells_amount_ = sells_amount ; 
 buys_amount_ = buys_amount ; 
 if ( Price.sells_ ^^ empty ( ) && Price.buys_ ^^ empty ( ) ) suicide ( flex_ ) ; 
 if ( ret ) return *ret ; 
 return { uint32 ( ok ) , uint128 ( 0 ) , Price.sell ^^ amount } ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_onTip3LendOwnership_call ( balance : SMLRValue XInteger128 false ) ( lend_finish_time : SMLRValue XInteger32 false ) ( pubkey : SMLRValue XInteger256 false ) ( internal_owner : SMLRValue XInteger256 false ) ( payload_cl : SMLRValue TvmCell false ) ( answer_addr : SMLRValue XAddress false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ6 ) Price_Ф_onTip3LendOwnership 
 ( SimpleLedgerableArg SMLRValue {{ Λ "balance" }} balance ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "lend_finish_time" }} lend_finish_time ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "pubkey" }} pubkey ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "internal_owner" }} internal_owner ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "payload_cl" }} payload_cl ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "answer_addr" }} answer_addr ) 
 . 
 Notation " 'Price_Ф_onTip3LendOwnership_ref_' '(' balance lend_finish_time pubkey internal_owner payload_cl answer_addr ')' " := 
 ( SMLRResult ( Price_Ф_onTip3LendOwnership_ref_call 
 balance lend_finish_time pubkey internal_owner payload_cl answer_addr )) 
 (in custom SMLRValue at level 0 , balance custom SMLRValue at level 0 
 , lend_finish_time custom SMLLValue at level 0 
 , pubkey custom SMLLValue at level 0 
 , internal_owner custom SMLLValue at level 0 
 , payload_cl custom SMLLValue at level 0 
 , answer_addr custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_getPrice : SMLExpression XInteger128 false := 
 {{ 
 return price_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getPrice_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getPrice 
 . 
 Notation " 'Price_Ф_getPrice_ref_' '(' ')' " := 
 ( SMLRResult ( Price_Ф_getPrice_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_getMinimumAmount : SMLExpression XInteger128 false := 
 {{ 
 return min_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getMinimumAmount_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getMinimumAmount 
 . 
 Notation " 'Price_Ф_getMinimumAmount_ref_' '(' ')' " := 
 ( SMLRResult ( Price_Ф_getMinimumAmount_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_getSellAmount : SMLExpression XInteger128 false := 
 {{ 
 return sells_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getSellAmount_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getSellAmount 
 . 
 Notation " 'Price_Ф_getSellAmount_ref_' '(' ')' " := 
 ( SMLRResult ( Price_Ф_getSellAmount_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_getBuyAmount : SMLExpression XInteger128 false := 
 {{ 
 return buys_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getBuyAmount_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getBuyAmount 
 . 
 Notation " 'Price_Ф_getBuyAmount_ref_' '(' ')' " := 
 ( SMLRResult ( Price_Ф_getBuyAmount_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_getDetails : SMLExpression DetailsInfoP false := 
 {{ 
 return { getPrice ( ) , getMinimumAmount ( ) , getSellAmount ( ) , getBuyAmount ( ) } ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getDetails_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getDetails 
 . 
 Notation " 'Price_Ф_getDetails_ref_' '(' ')' " := 
 ( SMLRResult ( Price_Ф_getDetails_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_getTonsCfg : SMLExpression TonsConfigP false := 
 {{ 
 return tons_cfg_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getTonsCfg_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getTonsCfg 
 . 
 Notation " 'Price_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( SMLRResult ( Price_Ф_getTonsCfg_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_getSells : SMLExpression ( XDictArray ) false := 
 {{ 
 return dict_array < OrderInfo > ( Price.sells_ ^^ begin ( ) , Price.sells_ ^^ end ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getSells_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getSells 
 . 
 Notation " 'Price_Ф_getSells_ref_' '(' ')' " := 
 ( SMLRResult ( Price_Ф_getSells_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф_getBuys : SMLExpression ( XDictArray ) false := 
 {{ 
 return dict_array < OrderInfo > ( Price.buys_ ^^ begin ( ) , Price.buys_ ^^ end ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getBuys_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getBuys 
 . 
 Notation " 'Price_Ф_getBuys_ref_' '(' ')' " := 
 ( SMLRResult ( Price_Ф_getBuys_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Price_Ф__fallback ( cell : (P ) : SMLExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф__fallback_call ( cell : SMLRValue (P false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) Price_Ф__fallback 
 ( SimpleLedgerableArg SMLRValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'Price_Ф__fallback_ref_' '(' cell ')' " := 
 ( SMLRResult ( Price_Ф__fallback_ref_call 
 cell )) 
 (in custom SMLRValue at level 0 , cell custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Ф_numerator : SMLExpression XInteger128 false := 
 {{ 
 return num ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_numerator_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Ф_numerator 
 . 
 Notation " 'Ф_numerator_ref_' '(' ')' " := 
 ( SMLRResult ( Ф_numerator_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Ф_denominator : SMLExpression XInteger128 false := 
 {{ 
 return denum ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_denominator_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) Ф_denominator 
 . 
 Notation " 'Ф_denominator_ref_' '(' ')' " := 
 ( SMLRResult ( Ф_denominator_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition Ф_minor_cost ( amount : XInteger128 ) ( price : price_tP ) : SMLExpression ( XMaybe XInteger128 ) false := 
 {{ 
 Л_cost_ := ^ __builtin_tvm_muldivr ( .amount ^^ get ( ) , .price ^^ numerator ( .) ^^ get ( ) , .price ^^ denominator ( .) ^^ get ( ) ) ; 
 if ( cost > > 128 ) return { } ; 
 return uint128 { cost } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_minor_cost_call ( amount : SMLRValue XInteger128 false ) ( price : SMLRValue price_tP false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) Ф_minor_cost 
 ( SimpleLedgerableArg SMLRValue {{ Λ "amount" }} amount ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "price" }} price ) 
 . 
 Notation " 'Ф_minor_cost_ref_' '(' amount price ')' " := 
 ( SMLRResult ( Ф_minor_cost_ref_call 
 amount price )) 
 (in custom SMLRValue at level 0 , amount custom SMLRValue at level 0 
 , price custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_on_ord_fail ( ec : XInteger ) ( wallet_in : ITONTokenWalletPtrP ) : SMLExpression OrderRetP false := 
 {{ 
 Л_incoming_value_ := ^ int_value ( PriceXchg.) ^^ get ( ) ; 
 tvm_rawreserve ( tvm_balance ( ) - incoming_value , rawreserve_flag : : up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 wallet_in ( Grams ( PriceXchg.tons_cfg_ ^^ return_ownership . get ( ) ) , IGNORE_ACTION_ERRORS PriceXchg.) ^^ returnOwnership ( ) ; 
 return { uint32 ( ec ) , { } , { } } ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_on_ord_fail_call ( ec : SMLRValue XInteger false ) ( wallet_in : SMLRValue ITONTokenWalletPtrP false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ2 ) PriceXchg_Ф_on_ord_fail 
 ( SimpleLedgerableArg SMLRValue {{ Λ "ec" }} ec ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "wallet_in" }} wallet_in ) 
 . 
 Notation " 'PriceXchg_Ф_on_ord_fail_ref_' '(' ec wallet_in ')' " := 
 ( SMLRResult ( PriceXchg_Ф_on_ord_fail_ref_call 
 ec wallet_in )) 
 (in custom SMLRValue at level 0 , ec custom SMLRValue at level 0 
 , wallet_in custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_onTip3LendOwnership ( lend_balance : XInteger128 ) ( lend_finish_time : XInteger32 ) ( pubkey : XInteger256 ) ( internal_owner : XInteger256 ) ( payload_cl : TvmCell ) ( answer_addr : XAddress ) : SMLExpression OrderRetP false := 
 {{ 
 (*$$ ( tip3_wallet value ) *) [ Л_tip3_wallet_ Л_value_ ] = int_sender_and_value ( ) ; 
 ITONTokenWalletPtr wallet_in ( tip3_wallet ) ; 
 Grams ret_owner_gr ( PriceXchg.tons_cfg_ ^^ return_ownership . get ( ) ) ; 
 set_int_sender ( answer_addr ) ; 
 set_int_return_value ( PriceXchg.tons_cfg_ ^^ order_answer . get ( ) ) ; 
 set_int_return_flag ( IGNORE_ACTION_ERRORS ) ; 
 Л_min_value_ := ^ onTip3LendOwnershipMinValue ( ) ; 
 Л_args_ := ^ parse < PayloadArgs > ( PriceXchg.payload_cl ^^ ctos ( ) ) ; 
 Л_is_sell_ := ^ PriceXchg.args ^^ sell ; 
 Л_amount_ := ^ PriceXchg.args ^^ amount ; 
 Л_minor_amount_ := ^ minor_cost ( amount , price_ ) ; 
 Л_err_ := ^ 0 ; 
 if ( PriceXchg.value ^^ get ( ) < min_value ) err = ec : : not_enough_tons_to_process ; 
 else if ( is_sell ? ! verify_tip3_addr ( major_tip3cfg_ , tip3_wallet , pubkey , internal_owner ) : ! verify_tip3_addr ( minor_tip3cfg_ , tip3_wallet , pubkey , internal_owner ) ) err = ec : : unverified_tip3_wallet ; 
 else if ( ! minor_amount ) err = ec : : too_big_tokens_amount ; 
 else if ( amount < min_amount_ ) err = ec : : not_enough_tokens_amount ; 
 else if ( lend_balance < ( is_sell ? amount : *minor_amount ) ) err = ec : : too_big_tokens_amount ; 
 if ( err ) return on_ord_fail ( err , wallet_in ) ; 
 Л_account_ := ^ uint128 ( PriceXchg.value ^^ get ( ) ) - PriceXchg.tons_cfg_ ^^ process_queue - PriceXchg.tons_cfg_ ^^ order_answer ; 
 Л_ord_ { amount , amount , account , tip3_wallet , PriceXchg.args ^^ receive_tip3_wallet , PriceXchg.args ^^ client_addr , lend_finish_time } ; 
 Л_sell_idx_ := ^ 0 ; 
 Л_buy_idx_ := ^ 0 ; 
 if ( is_sell ) { PriceXchg.sells_ ^^ push ( ord ) ; 
 sells_amount_ + = PriceXchg.ord ^^ amount ; 
 sell_idx = PriceXchg.sells_ ^^ back_with_idx ( PriceXchg.) ^^ first ; 
 } else { PriceXchg.buys_ ^^ push ( ord ) ; 
 buys_amount_ + = PriceXchg.ord ^^ amount ; 
 buy_idx = PriceXchg.buys_ ^^ back_with_idx ( PriceXchg.) ^^ first ; 
 } (*$$ ( sells_amount sells buys_amount buys ret ) *) [ Л_sells_amount_ Л_sells_ Л_buys_amount_ Л_buys_ Л_ret_ ] = process_queue_impl ( PriceXchg.major_tip3cfg_ ^^ root_address , PriceXchg.minor_tip3cfg_ ^^ root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , sell_idx , buy_idx , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; 
 sells_ = sells ; 
 buys_ = buys ; 
 sells_amount_ = sells_amount ; 
 buys_amount_ = buys_amount ; 
 if ( PriceXchg.sells_ ^^ empty ( ) && PriceXchg.buys_ ^^ empty ( ) ) suicide ( flex_ ) ; 
 if ( ret ) return *ret ; 
 return { uint32 ( ok ) , uint128 ( 0 ) , PriceXchg.ord ^^ amount } ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_onTip3LendOwnership_call ( lend_balance : SMLRValue XInteger128 false ) ( lend_finish_time : SMLRValue XInteger32 false ) ( pubkey : SMLRValue XInteger256 false ) ( internal_owner : SMLRValue XInteger256 false ) ( payload_cl : SMLRValue TvmCell false ) ( answer_addr : SMLRValue XAddress false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ6 ) PriceXchg_Ф_onTip3LendOwnership 
 ( SimpleLedgerableArg SMLRValue {{ Λ "lend_balance" }} lend_balance ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "lend_finish_time" }} lend_finish_time ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "pubkey" }} pubkey ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "internal_owner" }} internal_owner ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "payload_cl" }} payload_cl ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "answer_addr" }} answer_addr ) 
 . 
 Notation " 'PriceXchg_Ф_onTip3LendOwnership_ref_' '(' lend_balance lend_finish_time pubkey internal_owner payload_cl answer_addr ')' " := 
 ( SMLRResult ( PriceXchg_Ф_onTip3LendOwnership_ref_call 
 lend_balance lend_finish_time pubkey internal_owner payload_cl answer_addr )) 
 (in custom SMLRValue at level 0 , lend_balance custom SMLRValue at level 0 
 , lend_finish_time custom SMLLValue at level 0 
 , pubkey custom SMLLValue at level 0 
 , internal_owner custom SMLLValue at level 0 
 , payload_cl custom SMLLValue at level 0 
 , answer_addr custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_processQueue : SMLExpression True false := 
 {{ 
 if ( PriceXchg.sells_ ^^ empty ( ) || PriceXchg.buys_ ^^ empty ( ) ) return ; 
 (*$$ ( sells_amount sells buys_amount buys ret ) *) [ Л_sells_amount_ Л_sells_ Л_buys_amount_ Л_buys_ Л_ret_ ] = process_queue_impl ( PriceXchg.major_tip3cfg_ ^^ root_address , PriceXchg.minor_tip3cfg_ ^^ root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , 0 , 0 , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; 
 sells_ = sells ; 
 buys_ = buys ; 
 sells_amount_ = sells_amount ; 
 buys_amount_ = buys_amount ; 
 if ( PriceXchg.sells_ ^^ empty ( ) && PriceXchg.buys_ ^^ empty ( ) ) suicide ( flex_ ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_processQueue_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_processQueue 
 . 
 Notation " 'PriceXchg_Ф_processQueue_ref_' '(' ')' " := 
 ( FuncallExpression ( PriceXchg_Ф_processQueue_ref_call 
 )) 
 (in custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition PriceXchg_Ф_cancelSell : SMLExpression True false := 
 {{ 
 Л_client_addr_ := ^ int_sender ( ) ; 
 Л_value_ := ^ int_value ( ) ; 
 (*$$ ( sells sells_amount ) *) [ Л_sells_ Л_sells_amount_ ] = cancel_order_impl ( sells_ , client_addr , sells_amount_ , bool_t { true } , Grams ( PriceXchg.tons_cfg_ ^^ return_ownership . get ( ) ) , Grams ( PriceXchg.tons_cfg_ ^^ process_queue . get ( ) ) , value ) ; 
 sells_ = sells ; 
 sells_amount_ = sells_amount ; 
 if ( PriceXchg.sells_ ^^ empty ( ) && PriceXchg.buys_ ^^ empty ( ) ) suicide ( flex_ ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_cancelSell_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_cancelSell 
 . 
 Notation " 'PriceXchg_Ф_cancelSell_ref_' '(' ')' " := 
 ( FuncallExpression ( PriceXchg_Ф_cancelSell_ref_call 
 )) 
 (in custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition PriceXchg_Ф_cancelBuy : SMLExpression True false := 
 {{ 
 Л_client_addr_ := ^ int_sender ( ) ; 
 Л_value_ := ^ int_value ( ) ; 
 (*$$ ( buys buys_amount ) *) [ Л_buys_ Л_buys_amount_ ] = cancel_order_impl ( buys_ , client_addr , buys_amount_ , bool_t { false } , Grams ( PriceXchg.tons_cfg_ ^^ return_ownership . get ( ) ) , Grams ( PriceXchg.tons_cfg_ ^^ process_queue . get ( ) ) , value ) ; 
 buys_ = buys ; 
 buys_amount_ = buys_amount ; 
 if ( PriceXchg.sells_ ^^ empty ( ) && PriceXchg.buys_ ^^ empty ( ) ) suicide ( flex_ ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_cancelBuy_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_cancelBuy 
 . 
 Notation " 'PriceXchg_Ф_cancelBuy_ref_' '(' ')' " := 
 ( FuncallExpression ( PriceXchg_Ф_cancelBuy_ref_call 
 )) 
 (in custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 

Definition PriceXchg_Ф_getPriceNum : SMLExpression XInteger128 false := 
 {{ 
 return PriceXchg.price_ ^^ numerator ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getPriceNum_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getPriceNum 
 . 
 Notation " 'PriceXchg_Ф_getPriceNum_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_getPriceNum_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getPriceDenum : SMLExpression XInteger128 false := 
 {{ 
 return PriceXchg.price_ ^^ denominator ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getPriceDenum_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getPriceDenum 
 . 
 Notation " 'PriceXchg_Ф_getPriceDenum_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_getPriceDenum_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getDetails : SMLExpression DetailsInfoXchgP false := 
 {{ 
 return { getPriceNum ( ) , getPriceDenum ( ) , getMinimumAmount ( ) , getSellAmount ( ) , getBuyAmount ( ) } ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getDetails_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getDetails 
 . 
 Notation " 'PriceXchg_Ф_getDetails_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_getDetails_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getMinimumAmount : SMLExpression XInteger128 false := 
 {{ 
 return min_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getMinimumAmount_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getMinimumAmount 
 . 
 Notation " 'PriceXchg_Ф_getMinimumAmount_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_getMinimumAmount_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getTonsCfg : SMLExpression TonsConfigP false := 
 {{ 
 return tons_cfg_ ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getTonsCfg_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getTonsCfg 
 . 
 Notation " 'PriceXchg_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_getTonsCfg_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getSells : SMLExpression ( XDictArray ) false := 
 {{ 
 return dict_array < OrderInfoXchg > ( PriceXchg.sells_ ^^ begin ( ) , PriceXchg.sells_ ^^ end ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getSells_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getSells 
 . 
 Notation " 'PriceXchg_Ф_getSells_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_getSells_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getBuys : SMLExpression ( XDictArray ) false := 
 {{ 
 return dict_array < OrderInfoXchg > ( PriceXchg.buys_ ^^ begin ( ) , PriceXchg.buys_ ^^ end ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getBuys_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getBuys 
 . 
 Notation " 'PriceXchg_Ф_getBuys_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_getBuys_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getSellAmount : SMLExpression XInteger128 false := 
 {{ 
 return sells_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getSellAmount_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getSellAmount 
 . 
 Notation " 'PriceXchg_Ф_getSellAmount_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_getSellAmount_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getBuyAmount : SMLExpression XInteger128 false := 
 {{ 
 return buys_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getBuyAmount_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getBuyAmount 
 . 
 Notation " 'PriceXchg_Ф_getBuyAmount_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_getBuyAmount_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф__fallback ( cell : (P ) : SMLExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф__fallback_call ( cell : SMLRValue (P false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) PriceXchg_Ф__fallback 
 ( SimpleLedgerableArg SMLRValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'PriceXchg_Ф__fallback_ref_' '(' cell ')' " := 
 ( SMLRResult ( PriceXchg_Ф__fallback_ref_call 
 cell )) 
 (in custom SMLRValue at level 0 , cell custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_onTip3LendOwnershipMinValue : SMLExpression XInteger128 false := 
 {{ 
 return PriceXchg.tons_cfg_ ^^ process_queue + PriceXchg.tons_cfg_ ^^ transfer_tip3 + PriceXchg.tons_cfg_ ^^ send_notify + PriceXchg.tons_cfg_ ^^ return_ownership + PriceXchg.tons_cfg_ ^^ order_answer ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_onTip3LendOwnershipMinValue_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_onTip3LendOwnershipMinValue 
 . 
 Notation " 'PriceXchg_Ф_onTip3LendOwnershipMinValue_ref_' '(' ')' " := 
 ( SMLRResult ( PriceXchg_Ф_onTip3LendOwnershipMinValue_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_verify_tip3_addr ( cfg : Tip3ConfigP ) ( tip3_wallet : XAddress ) ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : SMLExpression XBool false := 
 {{ 
 Л_expected_address_ := ^ expected_wallet_address ( cfg , wallet_pubkey , internal_owner ) ; 
 return std : : get < addr_std > ( tip3_wallet ( ) PriceXchg.) ^^ address == expected_address ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_verify_tip3_addr_call ( cfg : SMLRValue Tip3ConfigP false ) ( tip3_wallet : SMLRValue XAddress false ) ( wallet_pubkey : SMLRValue XInteger256 false ) ( internal_owner : SMLRValue XInteger256 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ4 ) PriceXchg_Ф_verify_tip3_addr 
 ( SimpleLedgerableArg SMLRValue {{ Λ "cfg" }} cfg ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "tip3_wallet" }} tip3_wallet ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "wallet_pubkey" }} wallet_pubkey ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "internal_owner" }} internal_owner ) 
 . 
 Notation " 'PriceXchg_Ф_verify_tip3_addr_ref_' '(' cfg tip3_wallet wallet_pubkey internal_owner ')' " := 
 ( SMLRResult ( PriceXchg_Ф_verify_tip3_addr_ref_call 
 cfg tip3_wallet wallet_pubkey internal_owner )) 
 (in custom SMLRValue at level 0 , cfg custom SMLRValue at level 0 
 , tip3_wallet custom SMLLValue at level 0 
 , wallet_pubkey custom SMLLValue at level 0 
 , internal_owner custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_expected_wallet_address ( cfg : Tip3ConfigP ) ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : SMLExpression XInteger256 false := 
 {{ 
 std : : optional < address > owner_addr ; 
 if ( internal_owner ) owner_addr = address : : make_std ( workchain_id_ , internal_owner ) ; 
 Л_wallet_data_ { PriceXchg.cfg ^^ name , PriceXchg.cfg ^^ symbol , PriceXchg.cfg ^^ decimals , TokensType ( 0 ) , PriceXchg.cfg ^^ root_public_key , wallet_pubkey , PriceXchg.cfg ^^ root_address , owner_addr , { } , tip3_code_ , { } , workchain_id_ } ; 
 return prepare_wallet_state_init_and_addr ( wallet_data PriceXchg.) ^^ second ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_expected_wallet_address_call ( cfg : SMLRValue Tip3ConfigP false ) ( wallet_pubkey : SMLRValue XInteger256 false ) ( internal_owner : SMLRValue XInteger256 false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ3 ) PriceXchg_Ф_expected_wallet_address 
 ( SimpleLedgerableArg SMLRValue {{ Λ "cfg" }} cfg ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "wallet_pubkey" }} wallet_pubkey ) 
 ( SimpleLedgerableArg SMLRValue {{ Λ "internal_owner" }} internal_owner ) 
 . 
 Notation " 'PriceXchg_Ф_expected_wallet_address_ref_' '(' cfg wallet_pubkey internal_owner ')' " := 
 ( SMLRResult ( PriceXchg_Ф_expected_wallet_address_ref_call 
 cfg wallet_pubkey internal_owner )) 
 (in custom SMLRValue at level 0 , cfg custom SMLRValue at level 0 
 , wallet_pubkey custom SMLLValue at level 0 
 , internal_owner custom SMLLValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition TradingPair_Ф_getFLeXAddr : SMLExpression XAddress false := 
 {{ 
 return flex_addr_ ; 
 
 }} . 
 
 (*begin*) 
 Definition TradingPair_Ф_getFLeXAddr_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) TradingPair_Ф_getFLeXAddr 
 . 
 Notation " 'TradingPair_Ф_getFLeXAddr_ref_' '(' ')' " := 
 ( SMLRResult ( TradingPair_Ф_getFLeXAddr_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition TradingPair_Ф_getTip3Root : SMLExpression XAddress false := 
 {{ 
 return tip3_root_ ; 
 
 }} . 
 
 (*begin*) 
 Definition TradingPair_Ф_getTip3Root_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) TradingPair_Ф_getTip3Root 
 . 
 Notation " 'TradingPair_Ф_getTip3Root_ref_' '(' ')' " := 
 ( SMLRResult ( TradingPair_Ф_getTip3Root_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition TradingPair_Ф__fallback ( cell : (P ) : SMLExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition TradingPair_Ф__fallback_call ( cell : SMLRValue (P false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) TradingPair_Ф__fallback 
 ( SimpleLedgerableArg SMLRValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'TradingPair_Ф__fallback_ref_' '(' cell ')' " := 
 ( SMLRResult ( TradingPair_Ф__fallback_ref_call 
 cell )) 
 (in custom SMLRValue at level 0 , cell custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition XchgPair_Ф_onDeploy : SMLExpression XBool false := 
 {{ 
 require ( int_value ( XchgPair.) ^^ get ( ) > deploy_value_ , error_code : : not_enough_tons ) ; 
 tvm_rawreserve ( XchgPair.deploy_value_ ^^ get ( ) , rawreserve_flag : : up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 return bool_t { true } ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф_onDeploy_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) XchgPair_Ф_onDeploy 
 . 
 Notation " 'XchgPair_Ф_onDeploy_ref_' '(' ')' " := 
 ( SMLRResult ( XchgPair_Ф_onDeploy_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition XchgPair_Ф_getFLeXAddr : SMLExpression XAddress false := 
 {{ 
 return flex_addr_ ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф_getFLeXAddr_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) XchgPair_Ф_getFLeXAddr 
 . 
 Notation " 'XchgPair_Ф_getFLeXAddr_ref_' '(' ')' " := 
 ( SMLRResult ( XchgPair_Ф_getFLeXAddr_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition XchgPair_Ф_getTip3MajorRoot : SMLExpression XAddress false := 
 {{ 
 return tip3_major_root_ ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф_getTip3MajorRoot_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) XchgPair_Ф_getTip3MajorRoot 
 . 
 Notation " 'XchgPair_Ф_getTip3MajorRoot_ref_' '(' ')' " := 
 ( SMLRResult ( XchgPair_Ф_getTip3MajorRoot_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition XchgPair_Ф_getTip3MinorRoot : SMLExpression XAddress false := 
 {{ 
 return tip3_minor_root_ ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф_getTip3MinorRoot_call := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ0 ) XchgPair_Ф_getTip3MinorRoot 
 . 
 Notation " 'XchgPair_Ф_getTip3MinorRoot_ref_' '(' ')' " := 
 ( SMLRResult ( XchgPair_Ф_getTip3MinorRoot_ref_call 
 )) 
 (in custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

Definition XchgPair_Ф__fallback ( cell : (P ) : SMLExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф__fallback_call ( cell : SMLRValue (P false ) := 
 🏓 sml_call_with_args ( LedgerableWithArgs := λ1 ) XchgPair_Ф__fallback 
 ( SimpleLedgerableArg SMLRValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'XchgPair_Ф__fallback_ref_' '(' cell ')' " := 
 ( SMLRResult ( XchgPair_Ф__fallback_ref_call 
 cell )) 
 (in custom SMLRValue at level 0 , cell custom SMLRValue at level 0 ) : sml_scope. 
 (*end*) 
 

End FLeXFuncs.