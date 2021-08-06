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

Module FLeXFuncs (dc : FLeXConstsTypesSig XTypesModule StateMonadModule ).
 
Module Export FLeXFuncNotationsModule := FLeXFuncNotations XTypesModule StateMonadModule dc.
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.

Check {{ pubkey : XInteger256 @ "pubkey" ; 

         (* trading_pair_code : TvmCell @ "trading_pair_code" ;
         xchg_pair_code : TvmCell @ "xchg_pair_code" ;  *)

         FLeXClient.owner_ := !{pubkey} 
          }} .
(* Existing Instance xint_default. *)
(* Existing Instance xbool_default. *)
(* Existing Instance true_default. *)
Instance TvmCell_default : XDefault (TvmCell) := {
default := xStrNull}.
Existing Instance TvmCell_default.
Existing Instance phantom_default .

Definition FLeXClient_Ф_constructor ( pubkey : XInteger256 ) 
                                    ( trading_pair_code : TvmCell ) 
                                    ( xchg_pair_code : TvmCell ) 
: UExpression PhantomType false.

    refine {{ pubkey            : XInteger256 @ "pubkey" ; { _ } }} . 
    refine {{ trading_pair_code : TvmCell @ "trading_pair_code" ; { _ } }} .
    refine {{ xchg_pair_code    : TvmCell @ "xchg_pair_code" ; { _ } }} .
    refine {{ FLeXClient.owner_             := !{pubkey}  ; { _ }  }} . 

    refine {{ FLeXClient.trading_pair_code_ := !{trading_pair_code} ; { _ } }} . 
    refine {{ FLeXClient.xchg_pair_code_    := !{xchg_pair_code} ; { _ } }} . 
    refine {{ FLeXClient.workchain_id_      := 0 ; { _ } }} . (* get < addr_std > ( address { tvm_myaddr ( ) } . val ( ) FLeXClient.) ^^ workchain_id ;  *)
    refine {{ FLeXClient.flex_              := 0 ; { _ } }} . (* address : : make_std ( int8 ( 0 ) , uint256 ( 0 ) ) ; *)
    refine {{ FLeXClient.notify_addr_       := 0 }} . (* address : : make_std ( int8 ( 0 ) , uint256 ( 0 ) ) ;  *)
Defined.  

  (* refine {{  := !{} ; { _ } }} .  *)

Definition FLeXClient_Ф_constructor1 ( pubkey : XInteger256 ) ( trading_pair_code : TvmCell ) ( xchg_pair_code : TvmCell ) 
: UExpression PhantomType false :=
{{
  pubkey : XInteger256 @ "pubkey" ; 
  trading_pair_code : TvmCell @ "trading_pair_code" ; 
  xchg_pair_code : TvmCell @ "xchg_pair_code" ; 

  FLeXClient.owner_ := !{pubkey} ; 
  FLeXClient.trading_pair_code_ := !{trading_pair_code} ; 
  FLeXClient.xchg_pair_code_ := !{xchg_pair_code} ; 
  FLeXClient.workchain_id_ := 0 ;  (* get < addr_std > ( address { tvm_myaddr ( ) } . val ( ) FLeXClient.) ^^ workchain_id ;  *)
  FLeXClient.flex_ := 0 ;  (* address : : make_std ( int8 ( 0 ) , uint256 ( 0 ) ) ; *)
  FLeXClient.notify_addr_ := 0   (* address : : make_std ( int8 ( 0 ) , uint256 ( 0 ) ) ;  *)
}} .

 (*begin*) 
 Definition FLeXClient_Ф_constructor_call ( pubkey : URValue XInteger256 false ) 
                                          ( trading_pair_code : URValue TvmCell false ) 
                                          ( xchg_pair_code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FLeXClient_Ф_constructor 
 ( SimpleLedgerableArg URValue {{ Λ "pubkey" }} pubkey ) 
 ( SimpleLedgerableArg URValue {{ Λ "trading_pair_code" }} trading_pair_code ) 
 ( SimpleLedgerableArg URValue {{ Λ "xchg_pair_code" }} xchg_pair_code ) 
 . 
 Notation " 'FLeXClient_Ф_constructor_ref_' '(' pubkey trading_pair_code xchg_pair_code ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_constructor_call 
 pubkey trading_pair_code xchg_pair_code )) 
 (in custom ULValue at level 0 , pubkey custom ULValue at level 0 
 , trading_pair_code custom ULValue at level 0 
 , xchg_pair_code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Notation " 'I' " := (sInject I) (in custom URValue at level 0) : ursus_scope. 

Definition tvm_accept : UExpression True false := {{ return_ I }} . 
 Notation " 'tvm_accept' '(' ')' " := 
 ( FuncallExpression ( tvm_accept ) )
 (in custom ULValue at level 0 ) : ursus_scope. 

Definition FLeXClient_Ф_setFLeXCfg ( tons_cfg : TonsConfig ) 
                                   ( flex : XAddress ) 
                                   ( notify_addr : XAddress ) 
                                   : UExpression PhantomType false .
    refine {{ tons_cfg       : TonsConfig @ "tons_cfg" ; { _ } }} . 
    refine {{ flex           : XAddress @ "flex" ; { _ } }} .
    refine {{ notify_addr    : XAddress @ "notify_addr" ; { _ } }} .

(*    refine {{ require_ ( (* msg_pubkey ( ) *) 0 == FLeXClient.owner_ , 
                       error_code::message_sender_is_not_my_owner ) ; { _ } }} .
 *)
(*  refine {{ tvm_accept ( ) ; { _ } }} .  *)
  refine {{ FLeXClient.tons_cfg_ := !{tons_cfg} ; { _ } }} .
  refine {{ FLeXClient.flex_ := !{flex} ; { _ } }} .
  refine {{ FLeXClient.notify_addr_ := !{notify_addr} }} .
Defined. 
 
 (*begin*) 
 Definition FLeXClient_Ф_setFLeXCfg_call ( tons_cfg : URValue TonsConfig false ) 
                                         ( flex : URValue XAddress false ) 
                                         ( notify_addr : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FLeXClient_Ф_setFLeXCfg 
 ( SimpleLedgerableArg URValue {{ Λ "tons_cfg" }} tons_cfg ) 
 ( SimpleLedgerableArg URValue {{ Λ "flex" }} flex ) 
 ( SimpleLedgerableArg URValue {{ Λ "notify_addr" }} notify_addr ) 
 .
 Notation " 'FLeXClient_Ф_setFLeXCfg_ref_' '(' tons_cfg flex notify_addr ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_setFLeXCfg_call 
 tons_cfg flex notify_addr )) 
 (in custom ULValue at level 0 , tons_cfg custom ULValue at level 0 
 , flex custom ULValue at level 0 
 , notify_addr custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition Ф_prepare_trading_pair_state_init_and_addr ( pair_data : DTradingPair ) 
                                                      ( pair_code : TvmCell ) 
                                       : UExpression ( StateInit # XInteger256 )%sol false . 
    refine {{ pair_data       : DTradingPair @ "pair_data" ; { _ } }} . 
    refine {{ pair_code       : TvmCell @ "pair_code" ; { _ } }} .
    refine {{ pair_data_cl_       : TvmCell @ "pair_data_cl_" ; { _ } }} .
    refine {{ pair_init_cl_       : TvmCell @ "pair_init_cl_" ; { _ } }} .
    refine {{ price_init          : StateInit @ "price_init" ; { _ } }} .

    refine {{ {pair_data_cl_} := !{pair_data_cl_} ; { _ } }} . (* prepare_persistent_data < ITradingPair , void , DTradingPair > ( { } , pair_data ) ; *) 
(*  refine {{ pair_init_ { { } , { } , pair_code , pair_data_cl , { } } ; { _ } }} . *)
    refine {{ {pair_init_cl_} := !{pair_init_cl_} ; { _ } }} . (* prepare_persistent_data < ITradingPair , void , DTradingPair > ( { } , pair_data ) ; *) 
    refine {{ return_ [ !{price_init} , 0 ] }} . (* uint256 ( tvm_hash ( pair_init_cl ) ) *) 
Defined. 

 (*begin*) 
 Definition Ф_prepare_trading_pair_state_init_and_addr_call ( pair_data : URValue DTradingPair false ) ( pair_code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_trading_pair_state_init_and_addr 
 ( SimpleLedgerableArg URValue {{ Λ "pair_data" }} pair_data ) 
 ( SimpleLedgerableArg URValue {{ Λ "pair_code" }} pair_code ) 
 . 
 Notation " 'Ф_prepare_trading_pair_state_init_and_addr_ref_' '(' pair_data pair_code ')' " := 
 ( URResult ( Ф_prepare_trading_pair_state_init_and_addr_call 
 pair_data pair_code )) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 
 , pair_code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition TradingPair_Ф_onDeploy : UExpression XBool true . 

 refine {{ require_ ( (* int_value().get() > DTradingPair.deploy_value_ *) 0 > 0  , error_code::not_enough_tons ) ; { _ } }} .
(*  refine {{ tvm_rawreserve ( deploy_value_.get() , rawreserve_flag::up_to ) ; { _ } }} . *)
(*   refine {{ set_int_return_flag ( SEND_ALL_GAS ) ; { _ } }} . *)
 refine {{ return_ TRUE }} . 
Defined.

 (*begin*) 
 Definition TradingPair_Ф_onDeploy_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) TradingPair_Ф_onDeploy . 

 Notation " 'TradingPair_Ф_onDeploy_ref_' '(' ')' " := 
 ( URResult ( TradingPair_Ф_onDeploy_call )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_deployTradingPair ( tip3_root : XAddress ) 
                                          ( deploy_min_value : XInteger128 ) 
                                          ( deploy_value : XInteger128 ) 
                                         : UExpression XAddress false . 

    refine {{ tip3_root        : XAddress @ "tip3_root" ; { _ } }} . 
    refine {{ deploy_min_value : XInteger128 @ "deploy_min_value" ; { _ } }} .
    refine {{ deploy_value     : XInteger128 @ "deploy_value" ; { _ } }} .
    refine {{ state_init_      : StateInit @ "state_init_" ; { _ } }} .
    refine {{ std_addr_       : XAddress @ "std_addr_" ; { _ } }} .
    refine {{ trade_pair     : XAddress @ "trade_pair" ; { _ } }} .
(*  refine {{ require_ ( (* msg_pubkey ( ) *) 0 == FLeXClient.owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . *)
(*  tvm_accept ( ) ;  *)
(*    DTradingPair pair_data {
      .flex_addr_ = flex_,
      .tip3_root_ = tip3_root,
      .deploy_value_ = deploy_min_value
    }; *)
 refine {{ [ {state_init_} , {std_addr_} ] := [ !{state_init_} , !{std_addr_} ] ; { _ } }} . (* prepare_trading_pair_state_init_and_addr ( pair_data , trading_pair_code_ ) ;  *)
 refine {{ {trade_pair} := 0 ; { _ } }} . (* ITradingPairPtr(address::make_std(workchain_id_, std_addr));  *)
(*  trade_pair.deploy(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS, false).onDeploy();  *)
 refine {{ return_ !{trade_pair} }} . 
Defined.
 
 (*begin*) 
 Definition FLeXClient_Ф_deployTradingPair_call ( tip3_root : URValue XAddress false ) ( deploy_min_value : URValue XInteger128 false ) ( deploy_value : URValue XInteger128 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FLeXClient_Ф_deployTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_root" }} tip3_root ) 
 ( SimpleLedgerableArg URValue {{ Λ "deploy_min_value" }} deploy_min_value ) 
 ( SimpleLedgerableArg URValue {{ Λ "deploy_value" }} deploy_value ) 
 . 
 Notation " 'FLeXClient_Ф_deployTradingPair_ref_' '(' tip3_root deploy_min_value deploy_value ')' " := 
 ( URResult ( FLeXClient_Ф_deployTradingPair_call 
 tip3_root deploy_min_value deploy_value )) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 
 , deploy_min_value custom ULValue at level 0 
 , deploy_value custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Ф_prepare_xchg_pair_state_init_and_addr ( pair_data : DXchgPair ) 
                                                   ( pair_code : TvmCell ) 
                              : UExpression ( StateInit # XInteger256 )%sol false.
    refine {{ pair_data        : DXchgPair @ "pair_data" ; { _ } }} . 
    refine {{ pair_code        : TvmCell @ "pair_code" ; { _ } }} .
    refine {{ pair_data_cl_    : TvmCell @ "pair_data_cl_" ; { _ } }} .
    refine {{ pair_init_cl_    : TvmCell @ "pair_init_cl_" ; { _ } }} .
    refine {{ pair_init        : StateInit @ "pair_init" ; { _ } }} .

    refine {{ {pair_data_cl_} := !{pair_data_cl_} ; { _ } }} . (* prepare_persistent_data<IXchgPair, void, DXchgPair>({}, pair_data); *)
(*     refine {{   StateInit pair_init {
    {}, {}, pair_code, pair_data_cl, /*library*/{} }; { }  ; { _ } }} .
 *)    
    refine {{ {pair_init_cl_} := !{pair_init_cl_} ; { _ } }} . (* build(pair_init).make_cell();  *)
    refine {{ return_ [ !{pair_init} , 0 ] }} . (* uint256 ( tvm_hash ( pair_init_cl ) ) } ; *) 
Defined.
 (*begin*) 
 Definition Ф_prepare_xchg_pair_state_init_and_addr_call ( pair_data : URValue DXchgPair false ) ( pair_code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_xchg_pair_state_init_and_addr 
 ( SimpleLedgerableArg URValue {{ Λ "pair_data" }} pair_data ) 
 ( SimpleLedgerableArg URValue {{ Λ "pair_code" }} pair_code ) 
 . 
 Notation " 'Ф_prepare_xchg_pair_state_init_and_addr_ref_' '(' pair_data pair_code ')' " := 
 ( URResult ( Ф_prepare_xchg_pair_state_init_and_addr_call 
 pair_data pair_code )) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 
 , pair_code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 
Definition FLeXClient_Ф_deployXchgPair ( tip3_major_root : XAddress ) 
                                       ( tip3_minor_root : XAddress ) 
                                       ( deploy_min_value : XInteger128 ) 
                                       ( deploy_value : XInteger128 ) 
                                       : UExpression XAddress false . 
    refine {{ tip3_major_root        : XAddress @ "tip3_major_root" ; { _ } }} . 
    refine {{ tip3_minor_root        : XAddress @ "tip3_minor_root" ; { _ } }} .
    refine {{ deploy_min_value    : XInteger128 @ "deploy_min_value" ; { _ } }} .
    refine {{ deploy_value        : XInteger128 @ "deploy_value" ; { _ } }} .
    refine {{ pair_data           : DXchgPair @ "pair_data" ; { _ } }} .
    refine {{ state_init        : StateInit @ "state_init" ; { _ } }} .
    refine {{ std_addr           : XInteger256 @ "pair_data" ; { _ } }} .
    refine {{ trade_pair           : XAddress @ "trade_pair" ; { _ } }} .
 
(*     refine {{ require_ ( (* msg_pubkey ( ) *) 0 == FLeXClient.owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . *)
(*  tvm_accept ( ) ;  *)
    (* DXchgPair pair_data {
      .flex_addr_ = flex_,
      .tip3_major_root_ = tip3_major_root,
      .tip3_minor_root_ = tip3_minor_root,
      .deploy_value_ = deploy_min_value
    }; *)
    refine {{ [ {state_init} , {std_addr} ] := [ !{state_init} , !{std_addr} ] ; { _ } }} . (* prepare_xchg_pair_state_init_and_addr ( pair_data , xchg_pair_code_ ) ; *) 
    refine {{ {trade_pair} := 0 ; { _ } }} . (* IXchgPairPtr(address::make_std(workchain_id_, std_addr));  *)
(*     trade_pair.deploy(state_init, Grams(deploy_value.get()), DEFAULT_MSG_FLAGS, false).onDeploy(); return FLeXClient.trade_pair ^^ get ( ) ;  *)
    refine {{ return_ !{trade_pair} }} . 
Defined.
 
 (*begin*) 
 Definition FLeXClient_Ф_deployXchgPair_call ( tip3_major_root : URValue XAddress false ) ( tip3_minor_root : URValue XAddress false ) ( deploy_min_value : URValue XInteger128 false ) ( deploy_value : URValue XInteger128 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ4 ) FLeXClient_Ф_deployXchgPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_major_root" }} tip3_major_root ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_minor_root" }} tip3_minor_root ) 
 ( SimpleLedgerableArg URValue {{ Λ "deploy_min_value" }} deploy_min_value ) 
 ( SimpleLedgerableArg URValue {{ Λ "deploy_value" }} deploy_value ) 
 . 
 Notation " 'FLeXClient_Ф_deployXchgPair_ref_' '(' tip3_major_root tip3_minor_root deploy_min_value deploy_value ')' " := 
 ( URResult ( FLeXClient_Ф_deployXchgPair_call 
 tip3_major_root tip3_minor_root deploy_min_value deploy_value )) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom ULValue at level 0 
 , deploy_min_value custom ULValue at level 0 
 , deploy_value custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Ф_prepare_price_state_init_and_addr ( price_data : Price ) 
                                               ( price_code : TvmCell ) 
                     : UExpression ( StateInit # XInteger256 )%sol false . 
    refine {{ price_data        : Price @ "price_data" ; { _ } }} . 
    refine {{ price_code        : TvmCell @ "price_code" ; { _ } }} .
    refine {{ price_data_cl     : TvmCell @ "price_data_cl" ; { _ } }} .
    refine {{ price_init        : StateInit @ "price_init" ; { _ } }} .
    refine {{ price_init_cl     : TvmCell @ "price_init_cl" ; { _ } }} .

    refine {{ {price_data_cl} := !{price_data_cl} ; { _ } }} . (* prepare_persistent_data < IPrice , void , DPrice > ( { } , price_data ) ; *) 
  (* StateInit price_init {
    /*split_depth*/{}, /*special*/{},
    price_code, price_data_cl, /*library*/{}
  }; *)
    refine {{ {price_init_cl} := !{price_init_cl} ; { _ } }} . (* build(price_init).make_cell();  *)
    refine {{ return_ [ !{price_init} , 0 ] (* uint256 ( tvm_hash ( price_init_cl ) ) *) }} . 
Defined . 
 
 (*begin*) 
 Definition Ф_prepare_price_state_init_and_addr_call ( price_data : URValue Price false ) ( price_code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_price_state_init_and_addr 
 ( SimpleLedgerableArg URValue {{ Λ "price_data" }} price_data ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} price_code ) 
 . 
 Notation " 'Ф_prepare_price_state_init_and_addr_ref_' '(' price_data price_code ')' " := 
 ( URResult ( Ф_prepare_price_state_init_and_addr_call 
 price_data price_code )) 
 (in custom URValue at level 0 , price_data custom URValue at level 0 
 , price_code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_preparePrice ( price : XInteger128 ) 
                                     ( min_amount : XInteger128 ) 
                                     ( deals_limit : XInteger8 ) 
                                     ( tip3_code : TvmCell ) 
                                     ( tip3cfg : Tip3Config ) 
                                     ( price_code : TvmCell ) 
      : UExpression ( StateInit # XAddress (* # XInteger256 *) )%sol false . 
    refine {{ price        : XInteger128 @ "price" ; { _ } }} . 
    refine {{ min_amount   : XInteger128 @ "min_amount" ; { _ } }} .
    refine {{ deals_limit  : XInteger128 @ "deals_limit" ; { _ } }} .
    refine {{ tip3_code     : TvmCell @ "tip3_code" ; { _ } }} .
    refine {{ tip3cfg        : Tip3Config @ "tip3cfg" ; { _ } }} .
    refine {{ price_code     : TvmCell @ "price_code" ; { _ } }} .
    refine {{ price_data     : Price @ "price_data" ; { _ } }} .
    refine {{ state_init     : StateInit @ "state_init" ; { _ } }} .
    refine {{ std_addr       : XInteger256 @ "std_addr" ; { _ } }} .
    refine {{ addr           : XAddress @ "addr" ; { _ } }} .

    (* DPrice price_data {
      .price_ = price,
      .sells_amount_ = uint128(0),
      .buys_amount_ = uint128(0),
      .flex_ = flex_,
      .min_amount_ = min_amount,
      .deals_limit_ = deals_limit,
      .notify_addr_ = notify_addr_,
      .workchain_id_ = workchain_id_,
      .tons_cfg_ = tons_cfg_,
      .tip3_code_ = tip3_code,
      .tip3cfg_ = tip3cfg,
      .sells_ = {},
      .buys_ = {}
    }; *)
    refine {{ [ {state_init} , {std_addr} ] := [ !{state_init} , !{std_addr} ] ; { _ } }} . (* prepare_price_state_init_and_addr ( price_data , price_code ) ;  *)
    refine {{ {addr} := 0 ; { _ } }} . (* address : : make_std ( workchain_id_ , std_addr ) ;  *)
    refine {{ return_  [ !{state_init} , !{addr} (* , !{std_addr} *) ] }} .
Defined. 
 
 
 (*begin*) 
 Definition FLeXClient_Ф_preparePrice_call ( price : URValue XInteger128 false ) ( min_amount : URValue XInteger128 false ) ( deals_limit : URValue XInteger8 false ) ( tip3_code : URValue TvmCell false ) ( tip3cfg : URValue Tip3Config false ) ( price_code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ6 ) FLeXClient_Ф_preparePrice 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} price ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} min_amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} deals_limit ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_code" }} tip3_code ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3cfg" }} tip3cfg ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} price_code ) 
 . 
 Notation " 'FLeXClient_Ф_preparePrice_ref_' '(' price min_amount deals_limit tip3_code tip3cfg price_code ')' " := 
 ( URResult ( FLeXClient_Ф_preparePrice_call 
 price min_amount deals_limit tip3_code tip3cfg price_code )) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , min_amount custom ULValue at level 0 
 , deals_limit custom ULValue at level 0 
 , tip3_code custom ULValue at level 0 
 , tip3cfg custom ULValue at level 0 
 , price_code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_deployPriceWithSell ( args_cl : TvmCell ) : UExpression XAddress false . 
    refine {{ args_cl         : TvmCell @ "args_cl" ; { _ } }} . 
    refine {{ args             : FLeXSellArgs @ "args" ; { _ } }} .
    refine {{ state_init      : StateInit @ "state_init" ; { _ } }} .
    refine {{ addr            : XAddress @ "addr" ; { _ } }} .
    refine {{ std_addr        : XInteger256 @ "std_addr" ; { _ } }} .
    refine {{ price_addr      : XAddress @ "price_addr" ; { _ } }} .
    refine {{ deploy_init_cl     : TvmCell @ "deploy_init_cl" ; { _ } }} .
    refine {{ sell_args       : SellArgs @ "sell_args" ; { _ } }} .
    refine {{ payload        : TvmCell @ "payload" ; { _ } }} .
 
(* refine {{ require_ ( (* msg_pubkey ( ) *) 0 == FLeXClient.owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . *)
(*  tvm_accept ( ) ;  *)
    refine {{ {args} := !{args} ; { _ } }} . (* parse<FLeXSellArgs>(args_cl.ctos()); *) 
    refine {{ [ {state_init} , {addr} (* , {std_addr} *) ] := [ !{state_init} , !{addr} (* , !{std_addr} *) ] ; { _ } }} . (* preparePrice(args.price, args.min_amount, args.deals_limit, args.tip3_code, args.tip3cfg(), args.price_code); *)
    refine {{ {price_addr} := 0 ; { _ } }} . (* IPricePtr ( addr ) ; *) 
    refine {{ {deploy_init_cl} := !{deploy_init_cl} ; { _ } }} . (* build(state_init).endc(); *)
    (* SellArgs sell_args = {
      .amount = args.amount,
      .receive_wallet = args.addrs().receive_wallet
    }; *)
    refine {{ {payload} := !{payload} ; { _ } }} . (* build(sell_args).endc(); *)
(*     ITONTokenWalletPtr my_tip3(args.addrs().my_tip3_addr);  *)
   (*  my_tip3(Grams(args.tons_value.get()), DEFAULT_MSG_FLAGS, false).
      lendOwnership(std_addr, args.amount, args.lend_finish_time, deploy_init_cl, payload); *)
    refine {{ return_ !{price_addr} }} .

 
 (*begin*) 
 Definition FLeXClient_Ф_deployPriceWithSell_call ( args_cl : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_deployPriceWithSell 
 ( SimpleLedgerableArg URValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_deployPriceWithSell_ref_' '(' args_cl ')' " := 
 ( URResult ( FLeXClient_Ф_deployPriceWithSell_ref_call 
 args_cl )) 
 (in custom URValue at level 0 , args_cl custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Ф_calc_cost ( amount : XInteger128 ) ( price : XInteger128 ) : UExpression ( XMaybe XInteger128 ) false := 
 {{ 
 Л_tons_cost_ := ^ .amount ^^ get ( ) * .price ^^ get ( ) ; 
 if ( tons_cost > > 128 ) return { } ; 
 return uint128 ( tons_cost ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_calc_cost_call ( amount : URValue XInteger128 false ) ( price : URValue XInteger128 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_calc_cost 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} price ) 
 . 
 Notation " 'Ф_calc_cost_ref_' '(' amount price ')' " := 
 ( URResult ( Ф_calc_cost_ref_call 
 amount price )) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Ф_is_active_time ( order_finish_time : XInteger32 ) : UExpression XBool false := 
 {{ 
 return tvm_now ( ) + safe_delay_period < .order_finish_time ^^ get ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_is_active_time_call ( order_finish_time : URValue XInteger32 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Ф_is_active_time 
 ( SimpleLedgerableArg URValue {{ Λ "order_finish_time" }} order_finish_time ) 
 . 
 Notation " 'Ф_is_active_time_ref_' '(' order_finish_time ')' " := 
 ( URResult ( Ф_is_active_time_ref_call 
 order_finish_time )) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition dealer_Ф_extract_active_order ( cur_order : ( XMaybe OrderInfoWithIdxP ) ) ( orders : ( XQueue OrderInfoP ) ) ( all_amount : XInteger128 ) ( sell : XBool ) : UExpression ( XQueue OrderInfoP ) false := 
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
 Definition dealer_Ф_extract_active_order_call ( cur_order : URValue ( XMaybe OrderInfoWithIdxP ) false ) ( orders : URValue ( XQueue OrderInfoP ) false ) ( all_amount : URValue XInteger128 false ) ( sell : URValue XBool false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ4 ) dealer_Ф_extract_active_order 
 ( SimpleLedgerableArg URValue {{ Λ "cur_order" }} cur_order ) 
 ( SimpleLedgerableArg URValue {{ Λ "orders" }} orders ) 
 ( SimpleLedgerableArg URValue {{ Λ "all_amount" }} all_amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "sell" }} sell ) 
 . 
 Notation " 'dealer_Ф_extract_active_order_ref_' '(' cur_order orders all_amount sell ')' " := 
 ( URResult ( dealer_Ф_extract_active_order_ref_call 
 cur_order orders all_amount sell )) 
 (in custom URValue at level 0 , cur_order custom URValue at level 0 
 , orders custom ULValue at level 0 
 , all_amount custom ULValue at level 0 
 , sell custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition dealer_Ф_process_queue ( sell_idx : XInteger ) ( buy_idx : XInteger ) : UExpression True false := 
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
 Definition dealer_Ф_process_queue_call ( sell_idx : URValue XInteger false ) ( buy_idx : URValue XInteger false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) dealer_Ф_process_queue 
 ( SimpleLedgerableArg URValue {{ Λ "sell_idx" }} sell_idx ) 
 ( SimpleLedgerableArg URValue {{ Λ "buy_idx" }} buy_idx ) 
 . 
 Notation " 'dealer_Ф_process_queue_ref_' '(' sell_idx buy_idx ')' " := 
 ( FuncallExpression ( dealer_Ф_process_queue_ref_call 
 sell_idx buy_idx )) 
 (in custom ULValue at level 0 , sell_idx custom ULValue at level 0 
 , buy_idx custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition Ф_process_queue_impl ( tip3root : XAddress ) ( notify_addr : IFLeXNotifyPtrP ) ( price : XInteger128 ) ( deals_limit : XInteger8 ) ( tons_cfg : TonsConfigP ) ( sell_idx : XInteger ) ( buy_idx : XInteger ) ( sells_amount : XInteger128 ) ( sells : ( XQueue OrderInfoP ) ) ( buys_amount : XInteger128 ) ( buys : ( XQueue OrderInfoP ) ) : UExpression process_retP false := 
 {{ 
 Л_d_ { tip3root , notify_addr , price , .deals_limit ^^ get ( ) , tons_cfg , sells_amount , sells , buys_amount , buys , { } } ; 
 .d ^^ process_queue ( sell_idx , buy_idx ) ; 
 return { .d ^^ sells_amount_ , .d ^^ sells_ , .d ^^ buys_amount_ , .d ^^ buys_ , .d ^^ ret_ } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_process_queue_impl_call ( tip3root : URValue XAddress false ) ( notify_addr : URValue IFLeXNotifyPtrP false ) ( price : URValue XInteger128 false ) ( deals_limit : URValue XInteger8 false ) ( tons_cfg : URValue TonsConfigP false ) ( sell_idx : URValue XInteger false ) ( buy_idx : URValue XInteger false ) ( sells_amount : URValue XInteger128 false ) ( sells : URValue ( XQueue OrderInfoP ) false ) ( buys_amount : URValue XInteger128 false ) ( buys : URValue ( XQueue OrderInfoP ) false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ11 ) Ф_process_queue_impl 
 ( SimpleLedgerableArg URValue {{ Λ "tip3root" }} tip3root ) 
 ( SimpleLedgerableArg URValue {{ Λ "notify_addr" }} notify_addr ) 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} price ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} deals_limit ) 
 ( SimpleLedgerableArg URValue {{ Λ "tons_cfg" }} tons_cfg ) 
 ( SimpleLedgerableArg URValue {{ Λ "sell_idx" }} sell_idx ) 
 ( SimpleLedgerableArg URValue {{ Λ "buy_idx" }} buy_idx ) 
 ( SimpleLedgerableArg URValue {{ Λ "sells_amount" }} sells_amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "sells" }} sells ) 
 ( SimpleLedgerableArg URValue {{ Λ "buys_amount" }} buys_amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "buys" }} buys ) 
 . 
 Notation " 'Ф_process_queue_impl_ref_' '(' tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ')' " := 
 ( URResult ( Ф_process_queue_impl_ref_call 
 tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys )) 
 (in custom URValue at level 0 , tip3root custom URValue at level 0 
 , notify_addr custom ULValue at level 0 
 , price custom ULValue at level 0 
 , deals_limit custom ULValue at level 0 
 , tons_cfg custom ULValue at level 0 
 , sell_idx custom ULValue at level 0 
 , buy_idx custom ULValue at level 0 
 , sells_amount custom ULValue at level 0 
 , sells custom ULValue at level 0 
 , buys_amount custom ULValue at level 0 
 , buys custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_processQueue : UExpression True false := 
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
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_processQueue 
 . 
 Notation " 'Price_Ф_processQueue_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_processQueue_ref_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition FLeXClient_Ф_transfer ( dest : XAddress ) ( value : XInteger128 ) ( bounce : XBool ) : UExpression True false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 tvm_transfer ( dest , FLeXClient.value ^^ get ( ) , FLeXClient.bounce ^^ get ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_transfer_call ( dest : URValue XAddress false ) ( value : URValue XInteger128 false ) ( bounce : URValue XBool false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) FLeXClient_Ф_transfer 
 ( SimpleLedgerableArg URValue {{ Λ "dest" }} dest ) 
 ( SimpleLedgerableArg URValue {{ Λ "value" }} value ) 
 ( SimpleLedgerableArg URValue {{ Λ "bounce" }} bounce ) 
 . 
 Notation " 'FLeXClient_Ф_transfer_ref_' '(' dest value bounce ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_transfer_ref_call 
 dest value bounce )) 
 (in custom ULValue at level 0 , dest custom ULValue at level 0 
 , value custom ULValue at level 0 
 , bounce custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition dealer_Ф_make_deal ( sell : OrderInfoP ) ( buy : OrderInfoP ) : UExpression ( XBool # XBool # XInteger128 ) false := 
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
 Definition dealer_Ф_make_deal_call ( sell : URValue OrderInfoP false ) ( buy : URValue OrderInfoP false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) dealer_Ф_make_deal 
 ( SimpleLedgerableArg URValue {{ Λ "sell" }} sell ) 
 ( SimpleLedgerableArg URValue {{ Λ "buy" }} buy ) 
 . 
 Notation " 'dealer_Ф_make_deal_ref_' '(' sell buy ')' " := 
 ( URResult ( dealer_Ф_make_deal_ref_call 
 sell buy )) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , buy custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_buyTip3MinValue ( buy_cost : XInteger128 ) : UExpression XInteger128 false := 
 {{ 
 return buy_cost + Price.tons_cfg_ ^^ process_queue + Price.tons_cfg_ ^^ transfer_tip3 + Price.tons_cfg_ ^^ send_notify + Price.tons_cfg_ ^^ order_answer ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_buyTip3MinValue_call ( buy_cost : URValue XInteger128 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Price_Ф_buyTip3MinValue 
 ( SimpleLedgerableArg URValue {{ Λ "buy_cost" }} buy_cost ) 
 . 
 Notation " 'Price_Ф_buyTip3MinValue_ref_' '(' buy_cost ')' " := 
 ( URResult ( Price_Ф_buyTip3MinValue_ref_call 
 buy_cost )) 
 (in custom URValue at level 0 , buy_cost custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_buyTip3 ( amount : XInteger128 ) ( receive_tip3_wallet : XAddress ) ( order_finish_time : XInteger32 ) : UExpression OrderRetP false := 
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
 Definition Price_Ф_buyTip3_call ( amount : URValue XInteger128 false ) ( receive_tip3_wallet : URValue XAddress false ) ( order_finish_time : URValue XInteger32 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) Price_Ф_buyTip3 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "receive_tip3_wallet" }} receive_tip3_wallet ) 
 ( SimpleLedgerableArg URValue {{ Λ "order_finish_time" }} order_finish_time ) 
 . 
 Notation " 'Price_Ф_buyTip3_ref_' '(' amount receive_tip3_wallet order_finish_time ')' " := 
 ( URResult ( Price_Ф_buyTip3_ref_call 
 amount receive_tip3_wallet order_finish_time )) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , receive_tip3_wallet custom ULValue at level 0 
 , order_finish_time custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_deployPriceWithBuy ( args_cl : TvmCell ) : UExpression XAddress false := 
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
 Definition FLeXClient_Ф_deployPriceWithBuy_call ( args_cl : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_deployPriceWithBuy 
 ( SimpleLedgerableArg URValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_deployPriceWithBuy_ref_' '(' args_cl ')' " := 
 ( URResult ( FLeXClient_Ф_deployPriceWithBuy_ref_call 
 args_cl )) 
 (in custom URValue at level 0 , args_cl custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Ф_cancel_order_impl ( orders : ( XQueue OrderInfoP ) ) ( client_addr : addr_std_fixedP ) ( all_amount : XInteger128 ) ( sell : XBool ) ( return_ownership : GramsP ) ( process_queue : GramsP ) ( incoming_val : GramsP ) : UExpression ( XQueue OrderInfoP ) false := 
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
 Definition Ф_cancel_order_impl_call ( orders : URValue ( XQueue OrderInfoP ) false ) ( client_addr : URValue addr_std_fixedP false ) ( all_amount : URValue XInteger128 false ) ( sell : URValue XBool false ) ( return_ownership : URValue GramsP false ) ( process_queue : URValue GramsP false ) ( incoming_val : URValue GramsP false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ7 ) Ф_cancel_order_impl 
 ( SimpleLedgerableArg URValue {{ Λ "orders" }} orders ) 
 ( SimpleLedgerableArg URValue {{ Λ "client_addr" }} client_addr ) 
 ( SimpleLedgerableArg URValue {{ Λ "all_amount" }} all_amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "sell" }} sell ) 
 ( SimpleLedgerableArg URValue {{ Λ "return_ownership" }} return_ownership ) 
 ( SimpleLedgerableArg URValue {{ Λ "process_queue" }} process_queue ) 
 ( SimpleLedgerableArg URValue {{ Λ "incoming_val" }} incoming_val ) 
 . 
 Notation " 'Ф_cancel_order_impl_ref_' '(' orders client_addr all_amount sell return_ownership process_queue incoming_val ')' " := 
 ( URResult ( Ф_cancel_order_impl_ref_call 
 orders client_addr all_amount sell return_ownership process_queue incoming_val )) 
 (in custom URValue at level 0 , orders custom URValue at level 0 
 , client_addr custom ULValue at level 0 
 , all_amount custom ULValue at level 0 
 , sell custom ULValue at level 0 
 , return_ownership custom ULValue at level 0 
 , process_queue custom ULValue at level 0 
 , incoming_val custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_cancelSell : UExpression True false := 
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
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_cancelSell 
 . 
 Notation " 'Price_Ф_cancelSell_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_cancelSell_ref_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition FLeXClient_Ф_cancelSellOrder ( args_cl : TvmCell ) : UExpression True false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_args_ := ^ parse < FLeXXchgCancelArgsFLeXCancelArgs > ( FLeXClient.args_cl ^^ ctos ( ) ) ; 
 (*$$ ( state_init addr std_addr ) *) [ Л_state_init_ Л_addr_ Л_std_addr_ ] = preparePrice ( FLeXClient.args ^^ price , FLeXClient.args ^^ min_amount , FLeXClient.args ^^ deals_limit , FLeXClient.args ^^ tip3_code , FLeXClient.args ^^ tip3cfg ( ) , FLeXClient.args ^^ price_code ) ; 
 IPricePtr price_addr ( addr ) ; 
 price_addr ( Grams ( FLeXClient.args ^^ value . get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ cancelSell ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_cancelSellOrder_call ( args_cl : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_cancelSellOrder 
 ( SimpleLedgerableArg URValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_cancelSellOrder_ref_' '(' args_cl ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_cancelSellOrder_ref_call 
 args_cl )) 
 (in custom ULValue at level 0 , args_cl custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition Price_Ф_cancelBuy : UExpression True false := 
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
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_cancelBuy 
 . 
 Notation " 'Price_Ф_cancelBuy_ref_' '(' ')' " := 
 ( FuncallExpression ( Price_Ф_cancelBuy_ref_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition FLeXClient_Ф_cancelBuyOrder ( args_cl : TvmCell ) : UExpression True false := 
 {{ 
 require ( msg_pubkey ( ) == owner_ , error_code : : message_sender_is_not_my_owner ) ; 
 tvm_accept ( ) ; 
 Л_args_ := ^ parse < FLeXCancelArgs > ( FLeXClient.args_cl ^^ ctos ( ) ) ; 
 (*$$ ( state_init addr std_addr ) *) [ Л_state_init_ Л_addr_ Л_std_addr_ ] = preparePrice ( FLeXClient.args ^^ price , FLeXClient.args ^^ min_amount , FLeXClient.args ^^ deals_limit , FLeXClient.args ^^ tip3_code , FLeXClient.args ^^ tip3cfg ( ) , FLeXClient.args ^^ price_code ) ; 
 IPricePtr price_addr ( addr ) ; 
 price_addr ( Grams ( FLeXClient.args ^^ value . get ( ) ) , DEFAULT_MSG_FLAGS , false FLeXClient.) ^^ cancelBuy ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_cancelBuyOrder_call ( args_cl : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_cancelBuyOrder 
 ( SimpleLedgerableArg URValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_cancelBuyOrder_ref_' '(' args_cl ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_cancelBuyOrder_ref_call 
 args_cl )) 
 (in custom ULValue at level 0 , args_cl custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition Ф_prepare_price_xchg_state_init_and_addr ( price_data : DPriceXchgP ) ( price_code : TvmCell ) : UExpression ( StateInitP # XInteger256 ) false := 
 {{ 
 Л_price_data_cl_ := ^ prepare_persistent_data < IPriceXchg , void , DPriceXchg > ( { } , price_data ) ; 
 Л_price_init_ { { } , { } , price_code , price_data_cl , { } } ; 
 Л_price_init_cl_ := ^ build ( price_init .) ^^ make_cell ( ) ; 
 return { price_init , uint256 ( tvm_hash ( price_init_cl ) ) } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_prepare_price_xchg_state_init_and_addr_call ( price_data : URValue DPriceXchgP false ) ( price_code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_price_xchg_state_init_and_addr 
 ( SimpleLedgerableArg URValue {{ Λ "price_data" }} price_data ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} price_code ) 
 . 
 Notation " 'Ф_prepare_price_xchg_state_init_and_addr_ref_' '(' price_data price_code ')' " := 
 ( URResult ( Ф_prepare_price_xchg_state_init_and_addr_ref_call 
 price_data price_code )) 
 (in custom URValue at level 0 , price_data custom URValue at level 0 
 , price_code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_preparePriceXchg ( price_num : XInteger128 ) ( price_denum : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tip3_code : TvmCell ) ( major_tip3cfg : Tip3ConfigP ) ( minor_tip3cfg : Tip3ConfigP ) ( price_code : TvmCell ) : UExpression ( StateInitP # XAddress # XInteger256 ) false := 
 {{ 
 Л_price_data_ { . price_ = { price_num , price_denum } FLeXClient., ^^ sells_amount_ = uint128 ( 0 ) FLeXClient., ^^ buys_amount_ = uint128 ( 0 ) FLeXClient., ^^ flex_ = flex_ FLeXClient., ^^ min_amount_ = min_amount FLeXClient., ^^ deals_limit_ = deals_limit FLeXClient., ^^ notify_addr_ = notify_addr_ FLeXClient., ^^ workchain_id_ = workchain_id_ FLeXClient., ^^ tons_cfg_ = tons_cfg_ FLeXClient., ^^ tip3_code_ = tip3_code FLeXClient., ^^ major_tip3cfg_ = major_tip3cfg FLeXClient., ^^ minor_tip3cfg_ = minor_tip3cfg FLeXClient., ^^ sells_ = { } FLeXClient., ^^ buys_ = { } } ; 
 (*$$ ( state_init std_addr ) *) [ Л_state_init_ Л_std_addr_ ] = prepare_price_xchg_state_init_and_addr ( price_data , price_code ) ; 
 Л_addr_ := ^ address : : make_std ( workchain_id_ , std_addr ) ; 
 return { state_init , addr , std_addr } ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_preparePriceXchg_call ( price_num : URValue XInteger128 false ) ( price_denum : URValue XInteger128 false ) ( min_amount : URValue XInteger128 false ) ( deals_limit : URValue XInteger8 false ) ( tip3_code : URValue TvmCell false ) ( major_tip3cfg : URValue Tip3ConfigP false ) ( minor_tip3cfg : URValue Tip3ConfigP false ) ( price_code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ8 ) FLeXClient_Ф_preparePriceXchg 
 ( SimpleLedgerableArg URValue {{ Λ "price_num" }} price_num ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_denum" }} price_denum ) 
 ( SimpleLedgerableArg URValue {{ Λ "min_amount" }} min_amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} deals_limit ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_code" }} tip3_code ) 
 ( SimpleLedgerableArg URValue {{ Λ "major_tip3cfg" }} major_tip3cfg ) 
 ( SimpleLedgerableArg URValue {{ Λ "minor_tip3cfg" }} minor_tip3cfg ) 
 ( SimpleLedgerableArg URValue {{ Λ "price_code" }} price_code ) 
 . 
 Notation " 'FLeXClient_Ф_preparePriceXchg_ref_' '(' price_num price_denum min_amount deals_limit tip3_code major_tip3cfg minor_tip3cfg price_code ')' " := 
 ( URResult ( FLeXClient_Ф_preparePriceXchg_ref_call 
 price_num price_denum min_amount deals_limit tip3_code major_tip3cfg minor_tip3cfg price_code )) 
 (in custom URValue at level 0 , price_num custom URValue at level 0 
 , price_denum custom ULValue at level 0 
 , min_amount custom ULValue at level 0 
 , deals_limit custom ULValue at level 0 
 , tip3_code custom ULValue at level 0 
 , major_tip3cfg custom ULValue at level 0 
 , minor_tip3cfg custom ULValue at level 0 
 , price_code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_cancelXchgOrder ( args_cl : TvmCell ) : UExpression True false := 
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
 Definition FLeXClient_Ф_cancelXchgOrder_call ( args_cl : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_cancelXchgOrder 
 ( SimpleLedgerableArg URValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_cancelXchgOrder_ref_' '(' args_cl ')' " := 
 ( FuncallExpression ( FLeXClient_Ф_cancelXchgOrder_ref_call 
 args_cl )) 
 (in custom ULValue at level 0 , args_cl custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition FLeXClient_Ф_deployPriceXchg ( args_cl : TvmCell ) : UExpression XAddress false := 
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
 Definition FLeXClient_Ф_deployPriceXchg_call ( args_cl : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф_deployPriceXchg 
 ( SimpleLedgerableArg URValue {{ Λ "args_cl" }} args_cl ) 
 . 
 Notation " 'FLeXClient_Ф_deployPriceXchg_ref_' '(' args_cl ')' " := 
 ( URResult ( FLeXClient_Ф_deployPriceXchg_ref_call 
 args_cl )) 
 (in custom URValue at level 0 , args_cl custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_getOwner : UExpression XInteger256 false := 
 {{ 
 return owner_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_getOwner_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeXClient_Ф_getOwner 
 . 
 Notation " 'FLeXClient_Ф_getOwner_ref_' '(' ')' " := 
 ( URResult ( FLeXClient_Ф_getOwner_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeXClient_Ф_getFLeX : UExpression XAddress false := 
 {{ 
 return flex_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф_getFLeX_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeXClient_Ф_getFLeX 
 . 
 Notation " 'FLeXClient_Ф_getFLeX_ref_' '(' ')' " := 
 ( URResult ( FLeXClient_Ф_getFLeX_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeXClient_Ф__fallback ( cell : (P ) : UExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeXClient_Ф__fallback_call ( cell : URValue (P false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeXClient_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'FLeXClient_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( FLeXClient_Ф__fallback_ref_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_constructor ( deployer_pubkey : XInteger256 ) ( transfer_tip3 : XInteger128 ) ( return_ownership : XInteger128 ) ( trading_pair_deploy : XInteger128 ) ( order_answer : XInteger128 ) ( process_queue : XInteger128 ) ( send_notify : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( notify_addr : XAddress ) : UExpression True false := 
 {{ 
 deployer_pubkey_ = deployer_pubkey ; 
 min_amount_ = min_amount ; 
 deals_limit_ = deals_limit ; 
 notify_addr_ = notify_addr ; 
 tons_cfg_ = { transfer_tip3 , return_ownership , trading_pair_deploy , order_answer , process_queue , send_notify } ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_constructor_call ( deployer_pubkey : URValue XInteger256 false ) ( transfer_tip3 : URValue XInteger128 false ) ( return_ownership : URValue XInteger128 false ) ( trading_pair_deploy : URValue XInteger128 false ) ( order_answer : URValue XInteger128 false ) ( process_queue : URValue XInteger128 false ) ( send_notify : URValue XInteger128 false ) ( min_amount : URValue XInteger128 false ) ( deals_limit : URValue XInteger8 false ) ( notify_addr : URValue XAddress false ) := 
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
 ( FuncallExpression ( FLeX_Ф_constructor_ref_call 
 deployer_pubkey transfer_tip3 return_ownership trading_pair_deploy order_answer process_queue send_notify min_amount deals_limit notify_addr )) 
 (in custom ULValue at level 0 , deployer_pubkey custom ULValue at level 0 
 , transfer_tip3 custom ULValue at level 0 
 , return_ownership custom ULValue at level 0 
 , trading_pair_deploy custom ULValue at level 0 
 , order_answer custom ULValue at level 0 
 , process_queue custom ULValue at level 0 
 , send_notify custom ULValue at level 0 
 , min_amount custom ULValue at level 0 
 , deals_limit custom ULValue at level 0 
 , notify_addr custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition FLeX_Ф_isFullyInitialized : UExpression XBool false := 
 {{ 
 return bool_t ( pair_code_ && price_code_ && xchg_pair_code_ && xchg_price_code_ ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_isFullyInitialized_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_isFullyInitialized 
 . 
 Notation " 'FLeX_Ф_isFullyInitialized_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_isFullyInitialized_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_setPairCode ( code : TvmCell ) : UExpression True false := 
 {{ 
 require ( ! isFullyInitialized ( FLeX.) ^^ get ( ) , error_code : : cant_override_code ) ; 
 require ( msg_pubkey ( ) == deployer_pubkey_ , error_code : : sender_is_not_deployer ) ; 
 tvm_accept ( ) ; 
 require ( ! pair_code_ , error_code : : cant_override_code ) ; 
 require ( FLeX.code ^^ ctos ( FLeX.) ^^ srefs ( ) == 2 , error_code : : unexpected_refs_count_in_code ) ; 
 pair_code_ = builder ( FLeX.) ^^ stslice ( FLeX.code ^^ ctos ( ) FLeX.) ^^ stref ( build ( address { tvm_myaddr ( ) } FLeX.) ^^ endc ( ) FLeX.) ^^ endc ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_setPairCode_call ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setPairCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( FLeX_Ф_setPairCode_ref_call 
 code )) 
 (in custom ULValue at level 0 , code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition FLeX_Ф_setXchgPairCode ( code : TvmCell ) : UExpression True false := 
 {{ 
 require ( ! isFullyInitialized ( FLeX.) ^^ get ( ) , error_code : : cant_override_code ) ; 
 require ( msg_pubkey ( ) == deployer_pubkey_ , error_code : : sender_is_not_deployer ) ; 
 tvm_accept ( ) ; 
 require ( ! xchg_pair_code_ , error_code : : cant_override_code ) ; 
 require ( FLeX.code ^^ ctos ( FLeX.) ^^ srefs ( ) == 2 , error_code : : unexpected_refs_count_in_code ) ; 
 xchg_pair_code_ = builder ( FLeX.) ^^ stslice ( FLeX.code ^^ ctos ( ) FLeX.) ^^ stref ( build ( address { tvm_myaddr ( ) } FLeX.) ^^ endc ( ) FLeX.) ^^ endc ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_setXchgPairCode_call ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setXchgPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setXchgPairCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( FLeX_Ф_setXchgPairCode_ref_call 
 code )) 
 (in custom ULValue at level 0 , code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition FLeX_Ф_setPriceCode ( code : TvmCell ) : UExpression True false := 
 {{ 
 require ( ! isFullyInitialized ( FLeX.) ^^ get ( ) , error_code : : cant_override_code ) ; 
 require ( msg_pubkey ( ) == deployer_pubkey_ , error_code : : sender_is_not_deployer ) ; 
 tvm_accept ( ) ; 
 require ( ! price_code_ , error_code : : cant_override_code ) ; 
 price_code_ = code ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_setPriceCode_call ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setPriceCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( FLeX_Ф_setPriceCode_ref_call 
 code )) 
 (in custom ULValue at level 0 , code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition FLeX_Ф_setXchgPriceCode ( code : TvmCell ) : UExpression True false := 
 {{ 
 require ( ! isFullyInitialized ( FLeX.) ^^ get ( ) , error_code : : cant_override_code ) ; 
 require ( msg_pubkey ( ) == deployer_pubkey_ , error_code : : sender_is_not_deployer ) ; 
 tvm_accept ( ) ; 
 require ( ! xchg_price_code_ , error_code : : cant_override_code ) ; 
 xchg_price_code_ = code ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_setXchgPriceCode_call ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setXchgPriceCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( FLeX_Ф_setXchgPriceCode_ref_call 
 code )) 
 (in custom ULValue at level 0 , code custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition FLeX_Ф_getTonsCfg : UExpression TonsConfigP false := 
 {{ 
 return tons_cfg_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getTonsCfg_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getTonsCfg 
 . 
 Notation " 'FLeX_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getTonsCfg_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_getTradingPairCode : UExpression TvmCell false := 
 {{ 
 return *pair_code_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getTradingPairCode_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getTradingPairCode 
 . 
 Notation " 'FLeX_Ф_getTradingPairCode_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getTradingPairCode_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_getXchgPairCode : UExpression TvmCell false := 
 {{ 
 return *xchg_pair_code_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getXchgPairCode_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getXchgPairCode 
 . 
 Notation " 'FLeX_Ф_getXchgPairCode_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getXchgPairCode_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_getSellPriceCode ( tip3_addr : XAddress ) : UExpression TvmCell false := 
 {{ 
 require ( price_code_ - > ctos ( FLeX.) ^^ srefs ( ) == 2 , error_code : : unexpected_refs_count_in_code ) ; 
 Л_salt_ := ^ builder ( FLeX.) ^^ stslice ( tvm_myaddr ( ) FLeX.) ^^ stslice ( FLeX.tip3_addr ^^ sl ( ) FLeX.) ^^ endc ( ) ; 
 return builder ( FLeX.) ^^ stslice ( price_code_ - > ctos ( ) FLeX.) ^^ stref ( salt FLeX.) ^^ endc ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getSellPriceCode_call ( tip3_addr : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_getSellPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr" }} tip3_addr ) 
 . 
 Notation " 'FLeX_Ф_getSellPriceCode_ref_' '(' tip3_addr ')' " := 
 ( URResult ( FLeX_Ф_getSellPriceCode_ref_call 
 tip3_addr )) 
 (in custom URValue at level 0 , tip3_addr custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_getXchgPriceCode ( tip3_addr1 : XAddress ) ( tip3_addr2 : XAddress ) : UExpression TvmCell false := 
 {{ 
 require ( price_code_ - > ctos ( FLeX.) ^^ srefs ( ) == 2 , error_code : : unexpected_refs_count_in_code ) ; 
 Л_keys_ := ^ std : : make_tuple ( tip3_addr1 , tip3_addr2 ) ; 
 return builder ( FLeX.) ^^ stslice ( xchg_price_code_ - > ctos ( ) FLeX.) ^^ stref ( build ( keys FLeX.) ^^ endc ( ) FLeX.) ^^ endc ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getXchgPriceCode_call ( tip3_addr1 : URValue XAddress false ) ( tip3_addr2 : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) FLeX_Ф_getXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr1" }} tip3_addr1 ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr2" }} tip3_addr2 ) 
 . 
 Notation " 'FLeX_Ф_getXchgPriceCode_ref_' '(' tip3_addr1 tip3_addr2 ')' " := 
 ( URResult ( FLeX_Ф_getXchgPriceCode_ref_call 
 tip3_addr1 tip3_addr2 )) 
 (in custom URValue at level 0 , tip3_addr1 custom URValue at level 0 
 , tip3_addr2 custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_getSellTradingPair ( tip3_root : XAddress ) : UExpression XAddress false := 
 {{ 
 Л_myaddr_ { tvm_myaddr ( ) } ; 
 Л_pair_data_ { . flex_addr_ = myaddr FLeX., ^^ tip3_root_ = tip3_root FLeX., ^^ deploy_value_ = FLeX.tons_cfg_ ^^ trading_pair_deploy } ; 
 Л_std_addr_ := ^ prepare_trading_pair_state_init_and_addr ( pair_data , *pair_code_ FLeX.) ^^ second ; 
 Л_workchain_id_ := ^ std : : get < addr_std > ( FLeX.myaddr ^^ val ( ) FLeX.) ^^ workchain_id ; 
 return address : : make_std ( workchain_id , std_addr ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getSellTradingPair_call ( tip3_root : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_getSellTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_root" }} tip3_root ) 
 . 
 Notation " 'FLeX_Ф_getSellTradingPair_ref_' '(' tip3_root ')' " := 
 ( URResult ( FLeX_Ф_getSellTradingPair_ref_call 
 tip3_root )) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_getXchgTradingPair ( tip3_major_root : XAddress ) ( tip3_minor_root : XAddress ) : UExpression XAddress false := 
 {{ 
 Л_myaddr_ { tvm_myaddr ( ) } ; 
 Л_pair_data_ { . flex_addr_ = myaddr FLeX., ^^ tip3_major_root_ = tip3_major_root FLeX., ^^ tip3_minor_root_ = tip3_minor_root FLeX., ^^ deploy_value_ = FLeX.tons_cfg_ ^^ trading_pair_deploy } ; 
 Л_std_addr_ := ^ prepare_xchg_pair_state_init_and_addr ( pair_data , *xchg_pair_code_ FLeX.) ^^ second ; 
 Л_workchain_id_ := ^ std : : get < addr_std > ( FLeX.myaddr ^^ val ( ) FLeX.) ^^ workchain_id ; 
 return address : : make_std ( workchain_id , std_addr ) ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getXchgTradingPair_call ( tip3_major_root : URValue XAddress false ) ( tip3_minor_root : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) FLeX_Ф_getXchgTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_major_root" }} tip3_major_root ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_minor_root" }} tip3_minor_root ) 
 . 
 Notation " 'FLeX_Ф_getXchgTradingPair_ref_' '(' tip3_major_root tip3_minor_root ')' " := 
 ( URResult ( FLeX_Ф_getXchgTradingPair_ref_call 
 tip3_major_root tip3_minor_root )) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_getMinAmount : UExpression XInteger128 false := 
 {{ 
 return min_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getMinAmount_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getMinAmount 
 . 
 Notation " 'FLeX_Ф_getMinAmount_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getMinAmount_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_getDealsLimit : UExpression XInteger8 false := 
 {{ 
 return deals_limit_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getDealsLimit_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getDealsLimit 
 . 
 Notation " 'FLeX_Ф_getDealsLimit_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getDealsLimit_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф_getNotifyAddr : UExpression XAddress false := 
 {{ 
 return notify_addr_ ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф_getNotifyAddr_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getNotifyAddr 
 . 
 Notation " 'FLeX_Ф_getNotifyAddr_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getNotifyAddr_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition FLeX_Ф__fallback ( cell : (P ) : UExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition FLeX_Ф__fallback_call ( cell : URValue (P false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'FLeX_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( FLeX_Ф__fallback_ref_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_onTip3LendOwnershipMinValue : UExpression XInteger128 false := 
 {{ 
 return Price.tons_cfg_ ^^ process_queue + Price.tons_cfg_ ^^ transfer_tip3 + Price.tons_cfg_ ^^ send_notify + Price.tons_cfg_ ^^ return_ownership + Price.tons_cfg_ ^^ order_answer ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_onTip3LendOwnershipMinValue_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_onTip3LendOwnershipMinValue 
 . 
 Notation " 'Price_Ф_onTip3LendOwnershipMinValue_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_onTip3LendOwnershipMinValue_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_expected_wallet_address ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : UExpression XInteger256 false := 
 {{ 
 std : : optional < address > owner_addr ; 
 if ( internal_owner ) owner_addr = address : : make_std ( workchain_id_ , internal_owner ) ; 
 Л_wallet_data_ { Price.tip3cfg_ ^^ name , Price.tip3cfg_ ^^ symbol , Price.tip3cfg_ ^^ decimals , TokensType ( 0 ) , Price.tip3cfg_ ^^ root_public_key , wallet_pubkey , Price.tip3cfg_ ^^ root_address , owner_addr , { } , tip3_code_ , { } , workchain_id_ } ; 
 return prepare_wallet_state_init_and_addr ( wallet_data Price.) ^^ second ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_expected_wallet_address_call ( wallet_pubkey : URValue XInteger256 false ) ( internal_owner : URValue XInteger256 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Price_Ф_expected_wallet_address 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_pubkey" }} wallet_pubkey ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} internal_owner ) 
 . 
 Notation " 'Price_Ф_expected_wallet_address_ref_' '(' wallet_pubkey internal_owner ')' " := 
 ( URResult ( Price_Ф_expected_wallet_address_ref_call 
 wallet_pubkey internal_owner )) 
 (in custom URValue at level 0 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_verify_tip3_addr ( tip3_wallet : XAddress ) ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : UExpression XBool false := 
 {{ 
 Л_expected_address_ := ^ expected_wallet_address ( wallet_pubkey , internal_owner ) ; 
 return std : : get < addr_std > ( tip3_wallet ( ) Price.) ^^ address == expected_address ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_verify_tip3_addr_call ( tip3_wallet : URValue XAddress false ) ( wallet_pubkey : URValue XInteger256 false ) ( internal_owner : URValue XInteger256 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) Price_Ф_verify_tip3_addr 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_wallet" }} tip3_wallet ) 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_pubkey" }} wallet_pubkey ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} internal_owner ) 
 . 
 Notation " 'Price_Ф_verify_tip3_addr_ref_' '(' tip3_wallet wallet_pubkey internal_owner ')' " := 
 ( URResult ( Price_Ф_verify_tip3_addr_ref_call 
 tip3_wallet wallet_pubkey internal_owner )) 
 (in custom URValue at level 0 , tip3_wallet custom URValue at level 0 
 , wallet_pubkey custom ULValue at level 0 
 , internal_owner custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_on_sell_fail ( ec : XInteger ) ( wallet_in : ITONTokenWalletPtrP ) : UExpression OrderRetP false := 
 {{ 
 Л_incoming_value_ := ^ int_value ( Price.) ^^ get ( ) ; 
 tvm_rawreserve ( tvm_balance ( ) - incoming_value , rawreserve_flag : : up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 wallet_in ( Grams ( Price.tons_cfg_ ^^ return_ownership . get ( ) ) , IGNORE_ACTION_ERRORS Price.) ^^ returnOwnership ( ) ; 
 return { uint32 ( ec ) , { } , { } } ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_on_sell_fail_call ( ec : URValue XInteger false ) ( wallet_in : URValue ITONTokenWalletPtrP false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Price_Ф_on_sell_fail 
 ( SimpleLedgerableArg URValue {{ Λ "ec" }} ec ) 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_in" }} wallet_in ) 
 . 
 Notation " 'Price_Ф_on_sell_fail_ref_' '(' ec wallet_in ')' " := 
 ( URResult ( Price_Ф_on_sell_fail_ref_call 
 ec wallet_in )) 
 (in custom URValue at level 0 , ec custom URValue at level 0 
 , wallet_in custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_onTip3LendOwnership ( balance : XInteger128 ) ( lend_finish_time : XInteger32 ) ( pubkey : XInteger256 ) ( internal_owner : XInteger256 ) ( payload_cl : TvmCell ) ( answer_addr : XAddress ) : UExpression OrderRetP false := 
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
 Definition Price_Ф_onTip3LendOwnership_call ( balance : URValue XInteger128 false ) ( lend_finish_time : URValue XInteger32 false ) ( pubkey : URValue XInteger256 false ) ( internal_owner : URValue XInteger256 false ) ( payload_cl : URValue TvmCell false ) ( answer_addr : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ6 ) Price_Ф_onTip3LendOwnership 
 ( SimpleLedgerableArg URValue {{ Λ "balance" }} balance ) 
 ( SimpleLedgerableArg URValue {{ Λ "lend_finish_time" }} lend_finish_time ) 
 ( SimpleLedgerableArg URValue {{ Λ "pubkey" }} pubkey ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} internal_owner ) 
 ( SimpleLedgerableArg URValue {{ Λ "payload_cl" }} payload_cl ) 
 ( SimpleLedgerableArg URValue {{ Λ "answer_addr" }} answer_addr ) 
 . 
 Notation " 'Price_Ф_onTip3LendOwnership_ref_' '(' balance lend_finish_time pubkey internal_owner payload_cl answer_addr ')' " := 
 ( URResult ( Price_Ф_onTip3LendOwnership_ref_call 
 balance lend_finish_time pubkey internal_owner payload_cl answer_addr )) 
 (in custom URValue at level 0 , balance custom URValue at level 0 
 , lend_finish_time custom ULValue at level 0 
 , pubkey custom ULValue at level 0 
 , internal_owner custom ULValue at level 0 
 , payload_cl custom ULValue at level 0 
 , answer_addr custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_getPrice : UExpression XInteger128 false := 
 {{ 
 return price_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getPrice_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getPrice 
 . 
 Notation " 'Price_Ф_getPrice_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getPrice_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_getMinimumAmount : UExpression XInteger128 false := 
 {{ 
 return min_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getMinimumAmount_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getMinimumAmount 
 . 
 Notation " 'Price_Ф_getMinimumAmount_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getMinimumAmount_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_getSellAmount : UExpression XInteger128 false := 
 {{ 
 return sells_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getSellAmount_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getSellAmount 
 . 
 Notation " 'Price_Ф_getSellAmount_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getSellAmount_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_getBuyAmount : UExpression XInteger128 false := 
 {{ 
 return buys_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getBuyAmount_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getBuyAmount 
 . 
 Notation " 'Price_Ф_getBuyAmount_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getBuyAmount_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_getDetails : UExpression DetailsInfoP false := 
 {{ 
 return { getPrice ( ) , getMinimumAmount ( ) , getSellAmount ( ) , getBuyAmount ( ) } ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getDetails_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getDetails 
 . 
 Notation " 'Price_Ф_getDetails_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getDetails_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_getTonsCfg : UExpression TonsConfigP false := 
 {{ 
 return tons_cfg_ ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getTonsCfg_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getTonsCfg 
 . 
 Notation " 'Price_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getTonsCfg_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_getSells : UExpression ( XDictArray ) false := 
 {{ 
 return dict_array < OrderInfo > ( Price.sells_ ^^ begin ( ) , Price.sells_ ^^ end ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getSells_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getSells 
 . 
 Notation " 'Price_Ф_getSells_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getSells_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф_getBuys : UExpression ( XDictArray ) false := 
 {{ 
 return dict_array < OrderInfo > ( Price.buys_ ^^ begin ( ) , Price.buys_ ^^ end ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф_getBuys_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Price_Ф_getBuys 
 . 
 Notation " 'Price_Ф_getBuys_ref_' '(' ')' " := 
 ( URResult ( Price_Ф_getBuys_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Price_Ф__fallback ( cell : (P ) : UExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition Price_Ф__fallback_call ( cell : URValue (P false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) Price_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'Price_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( Price_Ф__fallback_ref_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Ф_numerator : UExpression XInteger128 false := 
 {{ 
 return num ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_numerator_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Ф_numerator 
 . 
 Notation " 'Ф_numerator_ref_' '(' ')' " := 
 ( URResult ( Ф_numerator_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Ф_denominator : UExpression XInteger128 false := 
 {{ 
 return denum ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_denominator_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) Ф_denominator 
 . 
 Notation " 'Ф_denominator_ref_' '(' ')' " := 
 ( URResult ( Ф_denominator_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition Ф_minor_cost ( amount : XInteger128 ) ( price : price_tP ) : UExpression ( XMaybe XInteger128 ) false := 
 {{ 
 Л_cost_ := ^ __builtin_tvm_muldivr ( .amount ^^ get ( ) , .price ^^ numerator ( .) ^^ get ( ) , .price ^^ denominator ( .) ^^ get ( ) ) ; 
 if ( cost > > 128 ) return { } ; 
 return uint128 { cost } ; 
 
 }} . 
 
 (*begin*) 
 Definition Ф_minor_cost_call ( amount : URValue XInteger128 false ) ( price : URValue price_tP false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_minor_cost 
 ( SimpleLedgerableArg URValue {{ Λ "amount" }} amount ) 
 ( SimpleLedgerableArg URValue {{ Λ "price" }} price ) 
 . 
 Notation " 'Ф_minor_cost_ref_' '(' amount price ')' " := 
 ( URResult ( Ф_minor_cost_ref_call 
 amount price )) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_on_ord_fail ( ec : XInteger ) ( wallet_in : ITONTokenWalletPtrP ) : UExpression OrderRetP false := 
 {{ 
 Л_incoming_value_ := ^ int_value ( PriceXchg.) ^^ get ( ) ; 
 tvm_rawreserve ( tvm_balance ( ) - incoming_value , rawreserve_flag : : up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 wallet_in ( Grams ( PriceXchg.tons_cfg_ ^^ return_ownership . get ( ) ) , IGNORE_ACTION_ERRORS PriceXchg.) ^^ returnOwnership ( ) ; 
 return { uint32 ( ec ) , { } , { } } ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_on_ord_fail_call ( ec : URValue XInteger false ) ( wallet_in : URValue ITONTokenWalletPtrP false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) PriceXchg_Ф_on_ord_fail 
 ( SimpleLedgerableArg URValue {{ Λ "ec" }} ec ) 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_in" }} wallet_in ) 
 . 
 Notation " 'PriceXchg_Ф_on_ord_fail_ref_' '(' ec wallet_in ')' " := 
 ( URResult ( PriceXchg_Ф_on_ord_fail_ref_call 
 ec wallet_in )) 
 (in custom URValue at level 0 , ec custom URValue at level 0 
 , wallet_in custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_onTip3LendOwnership ( lend_balance : XInteger128 ) ( lend_finish_time : XInteger32 ) ( pubkey : XInteger256 ) ( internal_owner : XInteger256 ) ( payload_cl : TvmCell ) ( answer_addr : XAddress ) : UExpression OrderRetP false := 
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
 Definition PriceXchg_Ф_onTip3LendOwnership_call ( lend_balance : URValue XInteger128 false ) ( lend_finish_time : URValue XInteger32 false ) ( pubkey : URValue XInteger256 false ) ( internal_owner : URValue XInteger256 false ) ( payload_cl : URValue TvmCell false ) ( answer_addr : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ6 ) PriceXchg_Ф_onTip3LendOwnership 
 ( SimpleLedgerableArg URValue {{ Λ "lend_balance" }} lend_balance ) 
 ( SimpleLedgerableArg URValue {{ Λ "lend_finish_time" }} lend_finish_time ) 
 ( SimpleLedgerableArg URValue {{ Λ "pubkey" }} pubkey ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} internal_owner ) 
 ( SimpleLedgerableArg URValue {{ Λ "payload_cl" }} payload_cl ) 
 ( SimpleLedgerableArg URValue {{ Λ "answer_addr" }} answer_addr ) 
 . 
 Notation " 'PriceXchg_Ф_onTip3LendOwnership_ref_' '(' lend_balance lend_finish_time pubkey internal_owner payload_cl answer_addr ')' " := 
 ( URResult ( PriceXchg_Ф_onTip3LendOwnership_ref_call 
 lend_balance lend_finish_time pubkey internal_owner payload_cl answer_addr )) 
 (in custom URValue at level 0 , lend_balance custom URValue at level 0 
 , lend_finish_time custom ULValue at level 0 
 , pubkey custom ULValue at level 0 
 , internal_owner custom ULValue at level 0 
 , payload_cl custom ULValue at level 0 
 , answer_addr custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_processQueue : UExpression True false := 
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
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_processQueue 
 . 
 Notation " 'PriceXchg_Ф_processQueue_ref_' '(' ')' " := 
 ( FuncallExpression ( PriceXchg_Ф_processQueue_ref_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition PriceXchg_Ф_cancelSell : UExpression True false := 
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
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_cancelSell 
 . 
 Notation " 'PriceXchg_Ф_cancelSell_ref_' '(' ')' " := 
 ( FuncallExpression ( PriceXchg_Ф_cancelSell_ref_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition PriceXchg_Ф_cancelBuy : UExpression True false := 
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
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_cancelBuy 
 . 
 Notation " 'PriceXchg_Ф_cancelBuy_ref_' '(' ')' " := 
 ( FuncallExpression ( PriceXchg_Ф_cancelBuy_ref_call 
 )) 
 (in custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 

Definition PriceXchg_Ф_getPriceNum : UExpression XInteger128 false := 
 {{ 
 return PriceXchg.price_ ^^ numerator ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getPriceNum_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getPriceNum 
 . 
 Notation " 'PriceXchg_Ф_getPriceNum_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_getPriceNum_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getPriceDenum : UExpression XInteger128 false := 
 {{ 
 return PriceXchg.price_ ^^ denominator ( ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getPriceDenum_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getPriceDenum 
 . 
 Notation " 'PriceXchg_Ф_getPriceDenum_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_getPriceDenum_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getDetails : UExpression DetailsInfoXchgP false := 
 {{ 
 return { getPriceNum ( ) , getPriceDenum ( ) , getMinimumAmount ( ) , getSellAmount ( ) , getBuyAmount ( ) } ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getDetails_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getDetails 
 . 
 Notation " 'PriceXchg_Ф_getDetails_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_getDetails_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getMinimumAmount : UExpression XInteger128 false := 
 {{ 
 return min_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getMinimumAmount_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getMinimumAmount 
 . 
 Notation " 'PriceXchg_Ф_getMinimumAmount_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_getMinimumAmount_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getTonsCfg : UExpression TonsConfigP false := 
 {{ 
 return tons_cfg_ ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getTonsCfg_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getTonsCfg 
 . 
 Notation " 'PriceXchg_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_getTonsCfg_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getSells : UExpression ( XDictArray ) false := 
 {{ 
 return dict_array < OrderInfoXchg > ( PriceXchg.sells_ ^^ begin ( ) , PriceXchg.sells_ ^^ end ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getSells_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getSells 
 . 
 Notation " 'PriceXchg_Ф_getSells_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_getSells_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getBuys : UExpression ( XDictArray ) false := 
 {{ 
 return dict_array < OrderInfoXchg > ( PriceXchg.buys_ ^^ begin ( ) , PriceXchg.buys_ ^^ end ( ) ) ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getBuys_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getBuys 
 . 
 Notation " 'PriceXchg_Ф_getBuys_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_getBuys_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getSellAmount : UExpression XInteger128 false := 
 {{ 
 return sells_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getSellAmount_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getSellAmount 
 . 
 Notation " 'PriceXchg_Ф_getSellAmount_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_getSellAmount_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_getBuyAmount : UExpression XInteger128 false := 
 {{ 
 return buys_amount_ ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_getBuyAmount_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_getBuyAmount 
 . 
 Notation " 'PriceXchg_Ф_getBuyAmount_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_getBuyAmount_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф__fallback ( cell : (P ) : UExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф__fallback_call ( cell : URValue (P false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) PriceXchg_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'PriceXchg_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( PriceXchg_Ф__fallback_ref_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_onTip3LendOwnershipMinValue : UExpression XInteger128 false := 
 {{ 
 return PriceXchg.tons_cfg_ ^^ process_queue + PriceXchg.tons_cfg_ ^^ transfer_tip3 + PriceXchg.tons_cfg_ ^^ send_notify + PriceXchg.tons_cfg_ ^^ return_ownership + PriceXchg.tons_cfg_ ^^ order_answer ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_onTip3LendOwnershipMinValue_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) PriceXchg_Ф_onTip3LendOwnershipMinValue 
 . 
 Notation " 'PriceXchg_Ф_onTip3LendOwnershipMinValue_ref_' '(' ')' " := 
 ( URResult ( PriceXchg_Ф_onTip3LendOwnershipMinValue_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_verify_tip3_addr ( cfg : Tip3ConfigP ) ( tip3_wallet : XAddress ) ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : UExpression XBool false := 
 {{ 
 Л_expected_address_ := ^ expected_wallet_address ( cfg , wallet_pubkey , internal_owner ) ; 
 return std : : get < addr_std > ( tip3_wallet ( ) PriceXchg.) ^^ address == expected_address ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_verify_tip3_addr_call ( cfg : URValue Tip3ConfigP false ) ( tip3_wallet : URValue XAddress false ) ( wallet_pubkey : URValue XInteger256 false ) ( internal_owner : URValue XInteger256 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ4 ) PriceXchg_Ф_verify_tip3_addr 
 ( SimpleLedgerableArg URValue {{ Λ "cfg" }} cfg ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_wallet" }} tip3_wallet ) 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_pubkey" }} wallet_pubkey ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} internal_owner ) 
 . 
 Notation " 'PriceXchg_Ф_verify_tip3_addr_ref_' '(' cfg tip3_wallet wallet_pubkey internal_owner ')' " := 
 ( URResult ( PriceXchg_Ф_verify_tip3_addr_ref_call 
 cfg tip3_wallet wallet_pubkey internal_owner )) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 
 , tip3_wallet custom ULValue at level 0 
 , wallet_pubkey custom ULValue at level 0 
 , internal_owner custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition PriceXchg_Ф_expected_wallet_address ( cfg : Tip3ConfigP ) ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : UExpression XInteger256 false := 
 {{ 
 std : : optional < address > owner_addr ; 
 if ( internal_owner ) owner_addr = address : : make_std ( workchain_id_ , internal_owner ) ; 
 Л_wallet_data_ { PriceXchg.cfg ^^ name , PriceXchg.cfg ^^ symbol , PriceXchg.cfg ^^ decimals , TokensType ( 0 ) , PriceXchg.cfg ^^ root_public_key , wallet_pubkey , PriceXchg.cfg ^^ root_address , owner_addr , { } , tip3_code_ , { } , workchain_id_ } ; 
 return prepare_wallet_state_init_and_addr ( wallet_data PriceXchg.) ^^ second ; 
 
 }} . 
 
 (*begin*) 
 Definition PriceXchg_Ф_expected_wallet_address_call ( cfg : URValue Tip3ConfigP false ) ( wallet_pubkey : URValue XInteger256 false ) ( internal_owner : URValue XInteger256 false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ3 ) PriceXchg_Ф_expected_wallet_address 
 ( SimpleLedgerableArg URValue {{ Λ "cfg" }} cfg ) 
 ( SimpleLedgerableArg URValue {{ Λ "wallet_pubkey" }} wallet_pubkey ) 
 ( SimpleLedgerableArg URValue {{ Λ "internal_owner" }} internal_owner ) 
 . 
 Notation " 'PriceXchg_Ф_expected_wallet_address_ref_' '(' cfg wallet_pubkey internal_owner ')' " := 
 ( URResult ( PriceXchg_Ф_expected_wallet_address_ref_call 
 cfg wallet_pubkey internal_owner )) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 
 , wallet_pubkey custom ULValue at level 0 
 , internal_owner custom ULValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition TradingPair_Ф_getFLeXAddr : UExpression XAddress false := 
 {{ 
 return flex_addr_ ; 
 
 }} . 
 
 (*begin*) 
 Definition TradingPair_Ф_getFLeXAddr_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) TradingPair_Ф_getFLeXAddr 
 . 
 Notation " 'TradingPair_Ф_getFLeXAddr_ref_' '(' ')' " := 
 ( URResult ( TradingPair_Ф_getFLeXAddr_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition TradingPair_Ф_getTip3Root : UExpression XAddress false := 
 {{ 
 return tip3_root_ ; 
 
 }} . 
 
 (*begin*) 
 Definition TradingPair_Ф_getTip3Root_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) TradingPair_Ф_getTip3Root 
 . 
 Notation " 'TradingPair_Ф_getTip3Root_ref_' '(' ')' " := 
 ( URResult ( TradingPair_Ф_getTip3Root_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition TradingPair_Ф__fallback ( cell : (P ) : UExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition TradingPair_Ф__fallback_call ( cell : URValue (P false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) TradingPair_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'TradingPair_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( TradingPair_Ф__fallback_ref_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition XchgPair_Ф_onDeploy : UExpression XBool false := 
 {{ 
 require ( int_value ( XchgPair.) ^^ get ( ) > deploy_value_ , error_code : : not_enough_tons ) ; 
 tvm_rawreserve ( XchgPair.deploy_value_ ^^ get ( ) , rawreserve_flag : : up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 return bool_t { true } ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф_onDeploy_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) XchgPair_Ф_onDeploy 
 . 
 Notation " 'XchgPair_Ф_onDeploy_ref_' '(' ')' " := 
 ( URResult ( XchgPair_Ф_onDeploy_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition XchgPair_Ф_getFLeXAddr : UExpression XAddress false := 
 {{ 
 return flex_addr_ ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф_getFLeXAddr_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) XchgPair_Ф_getFLeXAddr 
 . 
 Notation " 'XchgPair_Ф_getFLeXAddr_ref_' '(' ')' " := 
 ( URResult ( XchgPair_Ф_getFLeXAddr_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition XchgPair_Ф_getTip3MajorRoot : UExpression XAddress false := 
 {{ 
 return tip3_major_root_ ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф_getTip3MajorRoot_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) XchgPair_Ф_getTip3MajorRoot 
 . 
 Notation " 'XchgPair_Ф_getTip3MajorRoot_ref_' '(' ')' " := 
 ( URResult ( XchgPair_Ф_getTip3MajorRoot_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition XchgPair_Ф_getTip3MinorRoot : UExpression XAddress false := 
 {{ 
 return tip3_minor_root_ ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф_getTip3MinorRoot_call := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) XchgPair_Ф_getTip3MinorRoot 
 . 
 Notation " 'XchgPair_Ф_getTip3MinorRoot_ref_' '(' ')' " := 
 ( URResult ( XchgPair_Ф_getTip3MinorRoot_ref_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

Definition XchgPair_Ф__fallback ( cell : (P ) : UExpression XInteger false := 
 {{ 
 return 0 ; 
 
 }} . 
 
 (*begin*) 
 Definition XchgPair_Ф__fallback_call ( cell : URValue (P false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) XchgPair_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "cell" }} cell ) 
 . 
 Notation " 'XchgPair_Ф__fallback_ref_' '(' cell ')' " := 
 ( URResult ( XchgPair_Ф__fallback_ref_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope. 
 (*end*) 
 

End FLeXFuncs.




(* Definition plusassign (a b: XInteger) : UExpression  XInteger false :=
    {{
        a : XInteger @ "a" ; b : XInteger @ "b"  ; 
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
   (in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope. *)
