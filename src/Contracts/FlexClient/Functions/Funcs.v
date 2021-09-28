Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.ProofEnvironment2.
Require Import Ledger.
Require Import FuncSig.
Require Import Project.CommonConstSig.
Require Import FuncNotations.
Require Import UrsusTVM.tvmNotations.
Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
From elpi Require Import elpi.

Elpi Command AddLocalState.

Elpi Accumulate lp:{{

main [Name , Term, LocalStateFieldT] :-
  trm TrmInternal = Term,
  trm LocalStateField = LocalStateFieldT,
  str NameStr = Name,
  N is NameStr ^ "_j",
  coq.env.add-axiom N  (app [LocalStateField , TrmInternal]) _ , 
  coq.locate  N GR, 
  coq.TC.declare-instance GR 0,
  coq.say TrmInternal.
main _ :- coq.error "usage: AddLocalState <name> <term> <LocalStateField>".

}}.

Elpi Typecheck.
Elpi Export AddLocalState.

Elpi Command TestDefinitions. 
Elpi Accumulate lp:{{

pred get_name i:string , o:term.
get_name NameS NameG :-
    coq.locate NameS GR ,
    NameG = global GR . 

pred constructors_names i:string , o:list constructor.
constructors_names IndName Names :-
  std.assert! (coq.locate IndName (indt GR)) "not an inductive type",
  coq.env.indt GR _ _ _ _ Names _.

pred coqlist->list i:term, o: list term.
coqlist->list {{ [ ]%xlist }} [ ].
coqlist->list {{ (lp:X::lp:XS)%xlist }} [X | M] :- coqlist->list XS M.
coqlist->list X _ :- coq.say "error",
                    coq.say X.

main [ A ] :-
  coq.say  A. 
}}. 

Elpi Typecheck.
 
(* Module trainContractSpecModuleForFuncs := trainContractSpec XTypesModule StateMonadModule. *)

Module trainFuncs (dc : trainConstsTypesSig XTypesModule StateMonadModule) .

Module Export trainFuncNotationsModule := trainFuncNotations XTypesModule StateMonadModule dc. 
Import trainContractSpecModule(* ForFuncs *).tvmNotationsModule.

Module trainFuncsInternal <: trainContractSpecModule(* ForFuncs *).trainContractSpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.

Definition onlyOwner {X b}`{XDefault X} (e:UExpression X b) : UExpression X true .
   refine {{ require_ ( (tvm.pubkey() != 0) && (tvm.pubkey() == msg.pubkey()), 1 ) ; { _ } }} .
   refine {{ tvm.accept(); {e} }}.
Defined .

Existing Instance xbool_default.


Elpi AddLocalState _l1 (XHMap XAddress XBool) (LocalStateField).
Elpi AddLocalState _l2 (MessagesAndEventsStateLRecord) (LocalStateField).

Definition FlexClient_Ф_constructor ( pubkey : XInteger256 ) ( trading_pair_code : XCell ) ( xchg_pair_code : XCell ) : UExpression PhantomType true . 
         refine {{ pubkey : ( XInteger256 ) @ "pubkey" ; { _ } }} . 
         refine {{ trading_pair_code : ( XCell ) @ "trading_pair_code" ; { _ } }} . 
         refine {{ xchg_pair_code : ( XCell ) @ "xchg_pair_code" ; { _ } }} . 
         refine {{ require_ ( ( !{ pubkey } != 0 ) , error_code::zero_owner_pubkey ) ; { _ } }} . 
         refine {{ FlexClient.owner_ := !{ pubkey } ; { _ } }} . 
         refine {{ FlexClient.trading_pair_code_ := !{ trading_pair_code } ; { _ } }} . 
         refine {{ FlexClient.xchg_pair_code_ := !{ xchg_pair_code } ; { _ } }} . 
         refine {{ FlexClient.workchain_id_ := {} (*Std :: get < addr_std > ( Address { tvm_myaddr ( ) } . val ( ) ) . workchain_id *) ; { _ } }} . 
         refine {{ FlexClient.flex_ := {} (* Address :: make_std ( 0 , 0 ) *) ; { _ } }} . 
         refine {{ FlexClient.notify_addr_ := {} (* Address :: make_std ( 0 , 0 ) *) }} . 
 Defined . 
 
 
 Definition FlexClient_Ф_setFlexCfg ( tons_cfg : TonsConfig ) ( flex : addr_std_compact ) ( notify_addr : addr_std_compact ) : UExpression PhantomType true . 
         refine {{ tons_cfg : ( TonsConfig ) @ "tons_cfg" ; { _ } }} . 
         refine {{ flex : ( addr_std_compact ) @ "flex" ; { _ } }} . 
         refine {{ notify_addr : ( addr_std_compact ) @ "notify_addr" ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ FlexClient.tons_cfg_ := !{ tons_cfg } ; { _ } }} . 
         refine {{ FlexClient.flex_ := !{ flex } ; { _ } }} . 
         refine {{ FlexClient.notify_addr_ := !{ notify_addr } }} . 
 Defined . 
 
 
 Definition FlexClient_Ф_setExtWalletCode ( ext_wallet_code : XCell ) : UExpression PhantomType true . 
         refine {{ ext_wallet_code : ( XCell ) @ "ext_wallet_code" ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ FlexClient.ext_wallet_code_ ->set !{ ext_wallet_code }  }} . 
 Defined . 
 
 
 Definition FlexClient_Ф_setFlexWalletCode ( flex_wallet_code : XCell ) : UExpression PhantomType true . 
         refine {{ flex_wallet_code : ( XCell ) @ "flex_wallet_code" ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ FlexClient.flex_wallet_code_ ->set !{ flex_wallet_code } }} . 
 Defined . 
 
 
 Definition FlexClient_Ф_setFlexWrapperCode ( flex_wrapper_code : XCell ) : UExpression PhantomType true . 
         refine {{ flex_wrapper_code : ( XCell ) @ "flex_wrapper_code" ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ FlexClient.flex_wrapper_code_ ->set !{ flex_wrapper_code } }} . 
 Defined . 
 
 
 Definition FlexClient_Ф_deployTradingPair ( tip3_root : addr_std_compact ) ( deploy_min_value : XInteger128 ) ( deploy_value : XInteger128 ) ( min_trade_amount : XInteger128 ) 
: UExpression XAddress false (* true *) . 
         refine {{ tip3_root : ( addr_std_compact ) @ "tip3_root" ; { _ } }} . 
         refine {{ deploy_min_value : ( XInteger128 ) @ "deploy_min_value" ; { _ } }} . 
         refine {{ deploy_value : ( XInteger128 ) @ "deploy_value" ; { _ } }} . 
         refine {{ min_trade_amount : ( XInteger128 ) @ "min_trade_amount" ; { _ } }} . 
(*  	 	 refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} .  *)
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ new 'pair_data : ( TradingPair ) @ "pair_data" := {} ; { _ } }} . 
(*  	 	        NEW { . flex_addr_ = flex_ , . tip3_root_ = tip3_root } ; { _ } }} .  *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
(*  	 	  [ { state_init } , { std_addr } ] := prepare_trading_pair_state_init_and_addr ( pair_data , trading_pair_code_ ) ; { _ } }} .  *)
         refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {} ; { _ } }} . 
(*  	 	       ITradingPairPtr ( Address :: make_std ( FlexClient.workchain_id_ , std_addr ) ) ; { _ } }} .  *)
(*  	 	    refine {{ trade_pair :deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( min_trade_amount , deploy_min_value ) ; { _ } }} .  *)
         refine {{ return_ !{ trade_pair } }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_deployXchgPair ( tip3_major_root : addr_std_compact ) ( tip3_minor_root : addr_std_compact ) ( deploy_min_value : XInteger128 ) ( deploy_value : XInteger128 ) ( min_trade_amount : XInteger128 ) 
: UExpression XAddress false (* true *) . 
         refine {{ tip3_major_root : ( addr_std_compact ) @ "tip3_major_root" ; { _ } }} . 
         refine {{ tip3_minor_root : ( addr_std_compact ) @ "tip3_minor_root" ; { _ } }} . 
         refine {{ deploy_min_value : ( XInteger128 ) @ "deploy_min_value" ; { _ } }} . 
         refine {{ deploy_value : ( XInteger128 ) @ "deploy_value" ; { _ } }} . 
         refine {{ min_trade_amount : ( XInteger128 ) @ "min_trade_amount" ; { _ } }} . 
(*  	 	 refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} .  *)
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ new 'pair_data : ( XchgPair ) @ "pair_data" := {} ; { _ } }} . 
(*  	 	      NEW { . flex_addr_ = flex_ , . tip3_major_root_ = tip3_major_root , . tip3_minor_root_ = tip3_minor_root } ; { _ } }} .  *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
(*  	 	        [ { state_init } , { std_addr } ] := prepare_xchg_pair_state_init_and_addr ( pair_data , xchg_pair_code_ ) ; { _ } }} .  *)
         refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {}  ; { _ } }} . 
(*  	 	 { trade_pair } := IXchgPairPtr ( Address :: make_std ( FlexClient.workchain_id_ , std_addr ) ) ; { _ } }} .  *)
(*  	 	 refine {{ trade_pair :deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( min_trade_amount , deploy_min_value ) ; { _ } }} .  *)
         refine {{ return_ !{ trade_pair } }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_preparePrice ( price : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tip3_code : XCell ) ( tip3cfg : Tip3Config ) ( price_code : XCell ) 
: UExpression ( StateInit # XAddress # XInteger256 )%sol false . 
         refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
         refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
         refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
         refine {{ tip3_code : ( XCell ) @ "tip3_code" ; { _ } }} . 
         refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
         refine {{ price_code : ( XCell ) @ "price_code" ; { _ } }} . 
         refine {{ new 'price_data : ( Price ) @ "price_data" := {} ; { _ } }} . 
(*  	 	       { price_data } := NEW { . price_ = price , . sells_amount_ = uint128 ( 0 ) , . buys_amount_ = uint128 ( 0 ) , . flex_ = flex_ , . min_amount_ = min_amount , . deals_limit_ = deals_limit , . notify_addr_ = IFlexNotifyPtr ( notify_addr_ ) , . workchain_id_ = workchain_id_ , . tons_cfg_ = tons_cfg_ , . tip3_code_ = tip3_code , . tip3cfg_ = tip3cfg , . sells_ = { } , . buys_ = { } } ; { _ } }} .  *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
(*  	 	 [ { state_init } , { std_addr } ] := prepare_price_state_init_and_addr ( price_data , price_code ) ; { _ } }} .  *)
         refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
(*  	 	  { addr } := Address :: make_std ( FlexClient.workchain_id_ , std_addr ) ; { _ } }} .  *)
         refine {{ return_ {} (* [ !{ state_init } , !{ addr } , !{ std_addr } ] *) }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_deployPriceWithSell ( price : XInteger128 ) ( amount : XInteger128 ) ( lend_finish_time : XInteger32 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tons_value : XInteger128 ) ( price_code : XCell ) ( my_tip3_addr : addr_std_compact ) ( receive_wallet : addr_std_compact ) ( tip3cfg : Tip3Config ) 
: UExpression XAddress false (* true *) . 
         refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
         refine {{ amount : ( XInteger128 ) @ "amount" ; { _ } }} . 
         refine {{ lend_finish_time : ( XInteger32 ) @ "lend_finish_time" ; { _ } }} . 
         refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
         refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
         refine {{ tons_value : ( XInteger128 ) @ "tons_value" ; { _ } }} . 
         refine {{ price_code : ( XCell ) @ "price_code" ; { _ } }} . 
         refine {{ my_tip3_addr : ( addr_std_compact ) @ "my_tip3_addr" ; { _ } }} . 
         refine {{ receive_wallet : ( addr_std_compact ) @ "receive_wallet" ; { _ } }} . 
         refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
(*  	 	 refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
         refine {{ require_ ( ( FlexClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
         refine {{ tvm.accept () ; { _ } }} . *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {} ; { _ } }} . 
         refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
(*  	 	  [ { state_init } , { addr } , { std_addr } ] := preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code ) ; { _ } }} .  *)
         refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {} (* IPricePtr ( addr ) *) ; { _ } }} . 
         refine {{ new 'deploy_init_cl : ( XCell ) @ "deploy_init_cl" := {} (* build ( !{ state_init } ) . endc ( ) *) ; { _ } }} . 
         refine {{ new 'sell_args : ( SellArgs ) @ "sell_args" := {} ; { _ } }} . 
(*  	 	    { sell_args } := { . amount = !{ amount } , . receive_wallet = !{ receive_wallet } } ; { _ } }} .  *)
         refine {{ new 'payload : ( XCell ) @ "payload" := {}  (* build ( !{ sell_args } ) . endc ( ) *)  ; { _ } }} . 
(*  	 	 refine {{ ITONTokenWalletPtr my_tip3 ( my_tip3_addr ) ; { _ } }} . 
         refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . lendOwnership ( address { tvm_myaddr ( ) } , uint128 ( 0 ) , std_addr , amount , lend_finish_time , deploy_init_cl , payload ) ; { _ } }} . 
 *) 	 	 refine {{ return_ !{ price_addr } }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_deployPriceWithBuy ( price : XInteger128 ) ( amount : XInteger128 ) ( order_finish_time : XInteger32 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( deploy_value : XInteger128 ) ( price_code : XCell ) ( my_tip3_addr : addr_std_compact ) ( tip3cfg : Tip3Config ) 
: UExpression XAddress false (* true *) . 
         refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
         refine {{ amount : ( XInteger128 ) @ "amount" ; { _ } }} . 
         refine {{ order_finish_time : ( XInteger32 ) @ "order_finish_time" ; { _ } }} . 
         refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
         refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
         refine {{ deploy_value : ( XInteger128 ) @ "deploy_value" ; { _ } }} . 
         refine {{ price_code : ( XCell ) @ "price_code" ; { _ } }} . 
         refine {{ my_tip3_addr : ( addr_std_compact ) @ "my_tip3_addr" ; { _ } }} . 
         refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
 (* 	 	 refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
         refine {{ require_ ( ( FlexClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
         refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {} ; { _ } }} . 
         refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {} (* IPricePtr ( addr ) *) ; { _ } }} . 

(*  	 	 [ { state_init } , { addr } , { std_addr } ] := preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code ) ; { _ } }} .  *)
(*  	 	 refine {{ IPricePtr price_addr ( addr ) ; { _ } }} . 
         refine {{ price_addr ^^ deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . buyTip3 ( amount , my_tip3_addr , order_finish_time ) ; { _ } }} . 
 *) 	 	 
    refine {{ return_ !{ price_addr } }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_cancelSellOrder ( price : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( value : XInteger128 ) ( price_code : XCell ) ( tip3cfg : Tip3Config ) 
: UExpression PhantomType true . 
         refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
         refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
         refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
         refine {{ value : ( XInteger128 ) @ "value" ; { _ } }} . 
         refine {{ price_code : ( XCell ) @ "price_code" ; { _ } }} . 
         refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
         refine {{ require_ ( ( {} (* FlexClient.flex_wallet_code_ *) ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {} ; { _ } }} . 
         refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
(*  	 	  [ { state_init } , { addr } , { std_addr } ] := preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code ) ; { _ } }} .  *)
(*  	 	 refine {{ IPricePtr price_addr ( addr ) ; { _ } }} . 
         refine {{ price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelSell ( ) ; { _ } }} . 
 *) 
refine {{ {min_amount} := {} }} .
Defined . 
 
 
 Definition FlexClient_Ф_cancelBuyOrder ( price : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( value : XInteger128 ) ( price_code : XCell ) ( tip3cfg : Tip3Config ) : UExpression PhantomType true . 
         refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
         refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
         refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
         refine {{ value : ( XInteger128 ) @ "value" ; { _ } }} . 
         refine {{ price_code : ( XCell ) @ "price_code" ; { _ } }} . 
         refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
         refine {{ require_ ( ( {} (* FlexClient.flex_wallet_code_ *) ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {}  ; { _ } }} . 
         refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
(*  	 	  [ { state_init } , { addr } , { std_addr } ] := preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code ) ; { _ } }} .  *)
(*  	 	 refine {{ IPricePtr price_addr ( addr ) ; { _ } }} . 
         refine {{ price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelBuy ( ) ; { _ } }} . *) 
refine {{ {min_amount} := {} }} .
Defined . 
 
 
 Definition FlexClient_Ф_preparePriceXchg ( price_num : XInteger128 ) ( price_denum : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( major_tip3cfg : Tip3Config ) ( minor_tip3cfg : Tip3Config ) ( price_code : XCell ) 
: UExpression ( StateInit # XAddress # XInteger256 )%sol false . 
         refine {{ price_num : ( XInteger128 ) @ "price_num" ; { _ } }} . 
         refine {{ price_denum : ( XInteger128 ) @ "price_denum" ; { _ } }} . 
         refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
         refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
         refine {{ major_tip3cfg : ( Tip3Config ) @ "major_tip3cfg" ; { _ } }} . 
         refine {{ minor_tip3cfg : ( Tip3Config ) @ "minor_tip3cfg" ; { _ } }} . 
         refine {{ price_code : ( XCell ) @ "price_code" ; { _ } }} . 
         refine {{ new 'price_data : ( PriceXchg ) @ "price_data" := {} ; { _ } }} . 
(*  	 	     { price_data } := NEW { . price_ = { price_num , price_denum } , . sells_amount_ = uint128 ( 0 ) , . buys_amount_ = uint128 ( 0 ) , . flex_ = flex_ , . min_amount_ = min_amount , . deals_limit_ = deals_limit , . notify_addr_ = IFlexNotifyPtr ( notify_addr_ ) , . workchain_id_ = workchain_id_ , . tons_cfg_ = tons_cfg_ , . tip3_code_ = flex_wallet_code_ . get ( ) , . major_tip3cfg_ = major_tip3cfg , . minor_tip3cfg_ = minor_tip3cfg , . sells_ = { } , . buys_ = { } } ; { _ } }} .  *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
(*  	 	  [ { state_init } , { std_addr } ] := prepare_price_xchg_state_init_and_addr ( price_data , price_code ) ; { _ } }} .  *)
         refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
(*  	 	  { addr } := Address :: make_std ( FlexClient.workchain_id_ , std_addr ) ; { _ } }} .  *)
         refine {{ return_ {} (* [ !{ state_init } , !{ addr } , std_addr ]  *) }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_cancelXchgOrder ( sell : XBool ) ( price_num : XInteger128 ) ( price_denum : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( value : XInteger128 ) ( xchg_price_code : XCell ) ( major_tip3cfg : Tip3Config ) ( minor_tip3cfg : Tip3Config ) 
: UExpression PhantomType true . 
         refine {{ sell : ( XBool ) @ "sell" ; { _ } }} . 
         refine {{ price_num : ( XInteger128 ) @ "price_num" ; { _ } }} . 
         refine {{ price_denum : ( XInteger128 ) @ "price_denum" ; { _ } }} . 
         refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
         refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
         refine {{ value : ( XInteger128 ) @ "value" ; { _ } }} . 
         refine {{ xchg_price_code : ( XCell ) @ "xchg_price_code" ; { _ } }} . 
         refine {{ major_tip3cfg : ( Tip3Config ) @ "major_tip3cfg" ; { _ } }} . 
         refine {{ minor_tip3cfg : ( Tip3Config ) @ "minor_tip3cfg" ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
         refine {{ require_ ( ( {} (* FlexClient.flex_wallet_code_ *) ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {} ; { _ } }} . 
         refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
(*  	 	      [ { state_init } , { addr } , { std_addr } ] := preparePriceXchg ( price_num , price_denum , min_amount , deals_limit , major_tip3cfg , minor_tip3cfg , xchg_price_code ) ; { _ } }} .  *)
(*  	 	 refine {{ IPriceXchgPtr price_addr ( addr ) ; { _ } }} . 
 *) 	 	 
     refine {{ if ( !{ sell } ) then { { _ } } ; { _ } }} . 
             refine {{ {min_amount} := {}    (* price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelSell ( ) *) }} . 
         refine {{ {min_amount} := {} (* price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelBuy ( )  *) }} . 
 Defined . 
 
 
 Definition FlexClient_Ф_transfer ( dest : addr_std_compact ) ( value : XInteger128 ) ( bounce : XBool ) : UExpression PhantomType true . 
         refine {{ dest : ( addr_std_compact ) @ "dest" ; { _ } }} . 
         refine {{ value : ( XInteger128 ) @ "value" ; { _ } }} . 
         refine {{ bounce : ( XBool ) @ "bounce" ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ { dest } := {} (* tvm.transfer ( !{dest} , !{value} , !{bounce} ) *) }} . 
 Defined . 
 
 
 Definition FlexClient_Ф_deployPriceXchg ( sell : XBool ) ( price_num : XInteger128 ) ( price_denum : XInteger128 ) ( amount : XInteger128 ) ( lend_amount : XInteger128 ) ( lend_finish_time : XInteger32 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tons_value : XInteger128 ) ( xchg_price_code : XCell ) ( my_tip3_addr : addr_std_compact ) ( receive_wallet : addr_std_compact ) ( major_tip3cfg : Tip3Config ) ( minor_tip3cfg : Tip3Config ) 
: UExpression XAddress false (* true *) . 
         refine {{ sell : ( XBool ) @ "sell" ; { _ } }} . 
         refine {{ price_num : ( XInteger128 ) @ "price_num" ; { _ } }} . 
         refine {{ price_denum : ( XInteger128 ) @ "price_denum" ; { _ } }} . 
         refine {{ amount : ( XInteger128 ) @ "amount" ; { _ } }} . 
         refine {{ lend_amount : ( XInteger128 ) @ "lend_amount" ; { _ } }} . 
         refine {{ lend_finish_time : ( XInteger32 ) @ "lend_finish_time" ; { _ } }} . 
         refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
         refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
         refine {{ tons_value : ( XInteger128 ) @ "tons_value" ; { _ } }} . 
         refine {{ xchg_price_code : ( XCell ) @ "xchg_price_code" ; { _ } }} . 
         refine {{ my_tip3_addr : ( addr_std_compact ) @ "my_tip3_addr" ; { _ } }} . 
         refine {{ receive_wallet : ( addr_std_compact ) @ "receive_wallet" ; { _ } }} . 
         refine {{ major_tip3cfg : ( Tip3Config ) @ "major_tip3cfg" ; { _ } }} . 
         refine {{ minor_tip3cfg : ( Tip3Config ) @ "minor_tip3cfg" ; { _ } }} . 
(*  	 	 refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} .  *)
(*  	 	 refine {{ require_ ( ( FlexClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} .  *)
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ new 'state_init : ( StateInit ) @ "state_init" := {} ; { _ } }} . 
         refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
         refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
(*  	 	  { state_init } , { addr } , { std_addr } ] := preparePriceXchg ( price_num , price_denum , min_amount , deals_limit , major_tip3cfg , minor_tip3cfg , xchg_price_code ) ; { _ } }} .  *)
         refine {{ new 'price_addr : ( auto ) @ "price_addr" := {} (* IPriceXchgPtr ( addr ) *) ; { _ } }} . 
         refine {{ new 'deploy_init_cl : ( XCell ) @ "deploy_init_cl" := {} (* build ( !{ state_init } ) . endc ( ) *) ; { _ } }} . 
         refine {{ new 'payload_args : ( PayloadArgs ) @ "payload_args" := {} ; { _ } }} . 
(*  	 	  { payload_args } := { . sell = !{ sell } , . amount = !{ amount } , . receive_tip3_wallet = !{ receive_wallet } , . client_addr = Address { tvm_myaddr ( ) } } ; { _ } }} .  *)
         refine {{ new 'payload : ( XCell ) @ "payload" := {} (* build ( !{ payload_args } ) . endc ( ) *) ; { _ } }} . 
(*  	 	 refine {{ ITONTokenWalletPtr my_tip3 ( my_tip3_addr ) ; { _ } }} . 
         refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . lendOwnership ( address { tvm_myaddr ( ) } , uint128 ( 0 ) , std_addr , lend_amount , lend_finish_time , deploy_init_cl , payload ) ; { _ } }} . 
 *) 	 	 refine {{ return_ !{price_addr} }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_deployWrapperWithWallet ( wrapper_pubkey : XInteger256 ) ( wrapper_deploy_value : XInteger128 ) ( wrapper_keep_balance : XInteger128 ) ( ext_wallet_balance : XInteger128 ) ( set_internal_wallet_value : XInteger128 ) ( tip3cfg : Tip3Config ) 
: UExpression XAddress false (* true *) . 
         refine {{ wrapper_pubkey : ( XInteger256 ) @ "wrapper_pubkey" ; { _ } }} . 
         refine {{ wrapper_deploy_value : ( XInteger128 ) @ "wrapper_deploy_value" ; { _ } }} . 
         refine {{ wrapper_keep_balance : ( XInteger128 ) @ "wrapper_keep_balance" ; { _ } }} . 
         refine {{ ext_wallet_balance : ( XInteger128 ) @ "ext_wallet_balance" ; { _ } }} . 
         refine {{ set_internal_wallet_value : ( XInteger128 ) @ "set_internal_wallet_value" ; { _ } }} . 
         refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
(*  	 	 refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
         refine {{ require_ ( ( FlexClient.ext_wallet_code_ ) , error_code::missed_ext_wallet_code ) ; { _ } }} . 
         refine {{ require_ ( ( FlexClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
         refine {{ require_ ( ( FlexClient.flex_wrapper_code_ ) , error_code::missed_flex_wrapper_code ) ; { _ } }} . 
         refine {{ tvm.accept () ; { _ } }} . *) 	 	 
     refine {{ new 'wrapper_data : ( XAddress (* WrapperPtr *) ) @ "wrapper_data" := {} ; { _ } }} . 
               (* { . name_ = tip3cfg . name , . symbol_ = tip3cfg . symbol , . decimals_ = tip3cfg . decimals , 
              . workchain_id_ = workchain_id_ , . root_public_key_ = wrapper_pubkey , . total_granted_ = { } , . internal_wallet_code_ = { } , 
              . owner_address_ = address { tvm_myaddr ( ) } , . start_balance_ = Grams ( wrapper_keep_balance . get ( ) ) , . external_wallet_ = { } } *)  
         refine {{ new 'wrapper_init : ( StateInit ) @ "wrapper_init" := {} ; { _ } }} . 
         refine {{ new 'wrapper_hash_addr : ( XAddress ) @ "wrapper_hash_addr" := {} ; { _ } }} . 
(*  	 	 [ { wrapper_init } , { wrapper_hash_addr } ] := prepare_wrapper_state_init_and_addr ( flex_wrapper_code_ . get ( ) , wrapper_data ) ; { _ } }} .  *)
     refine {{ new 'wrapper_addr : XAddress @ "wrapper_addr" := {} ; { _ } }} . 
(*  	 	  IWrapperPtr wrapper_addr ( address : : make_std ( workchain_id_ , wrapper_hash_addr ) ) ; { _ } }} .  *)
         refine {{ new 'wallet_init : ( StateInit ) @ "wallet_init" := {} ; { _ } }} . 
         refine {{ new 'wallet_hash_addr : ( XAddress ) @ "wallet_hash_addr" := {} ; { _ } }} . 
(*  	 	 [ { wallet_init } , { wallet_hash_addr } ] := prepare_external_wallet_state_init_and_addr ( tip3cfg . name , tip3cfg . symbol , tip3cfg . decimals , tip3cfg . root_public_key , wrapper_pubkey , tip3cfg . root_address , wrapper_addr . get ( ) , ext_wallet_code_ . get ( ) , workchain_id_ ) ; { _ } }} .  *)
(*  	 	 refine {{ ITONTokenWalletPtr wallet_addr ( address : : make_std ( workchain_id_ , wallet_hash_addr ) ) ; { _ } }} . 
         refine {{ wallet_addr . deploy_noop ( wallet_init , Grams ( ext_wallet_balance . get ( ) ) ) ; { _ } }} . 
         refine {{ wrapper_addr . deploy ( wrapper_init , Grams ( wrapper_deploy_value . get ( ) ) ) . init ( wallet_addr . get ( ) ) ; { _ } }} . 
         refine {{ wrapper_addr ( Grams ( set_internal_wallet_value . get ( ) ) ) . setInternalWalletCode ( flex_wallet_code_ . get ( ) ) ; { _ } }} .  *)
         refine {{ return_ !{wrapper_addr} }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_deployEmptyFlexWallet ( pubkey : XInteger256 ) ( tons_to_wallet : XInteger128 ) ( tip3cfg : Tip3Config ) 
: UExpression XAddress false (* true *) . 
         refine {{ pubkey : ( XInteger256 ) @ "pubkey" ; { _ } }} . 
         refine {{ tons_to_wallet : ( XInteger128 ) @ "tons_to_wallet" ; { _ } }} . 
         refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
(*  	 	 refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
         refine {{ require_ ( ( FlexClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . *) 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
         refine {{ new 'init : ( StateInit ) @ "init" := {} ; { _ } }} . 
         refine {{ new 'hash_addr : ( XAddress ) @ "hash_addr" := {} ; { _ } }} . 
(*  	 	     [ { init } , { hash_addr } ] := prepare_internal_wallet_state_init_and_addr ( tip3cfg . name , tip3cfg . symbol , tip3cfg . decimals , tip3cfg . root_public_key , pubkey , tip3cfg . root_address , address { tvm_myaddr ( ) } , flex_wallet_code_ . get ( ) , workchain_id_ ) ; { _ } }} . 
*)
refine {{ new 'new_wallet : ( XAddress ) @ "new_wallet" := {} ; { _ } }} . 
(* 	 	 refine {{ ITONTokenWalletPtr new_wallet ( address : : make_std ( workchain_id_ , hash_addr ) ) ; { _ } }} . 
         refine {{ new_wallet . deploy_noop ( init , Grams ( tons_to_wallet . get ( ) ) ) ; { _ } }} . 
 *) 	 	 
     refine {{ return_ !{ new_wallet } }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_burnWallet ( tons_value : XInteger128 ) ( out_pubkey : XInteger256 ) ( out_internal_owner : addr_std_compact ) ( my_tip3_addr : addr_std_compact ) : UExpression PhantomType true . 
         refine {{ tons_value : ( XInteger128 ) @ "tons_value" ; { _ } }} . 
         refine {{ out_pubkey : ( XInteger256 ) @ "out_pubkey" ; { _ } }} . 
         refine {{ out_internal_owner : ( addr_std_compact ) @ "out_internal_owner" ; { _ } }} . 
         refine {{ my_tip3_addr : ( addr_std_compact ) @ "my_tip3_addr" ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == FlexClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
(*  	 	 refine {{ ITONTokenWalletPtr my_tip3 ( my_tip3_addr ) ; { _ } }} . 
         refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) ) . burn ( out_pubkey , out_internal_owner ) ; { _ } }} . 
 *) 
refine {{ { tons_value } := {} }} .
Defined . 
 
 
 Definition FlexClient_Ф_getOwner : UExpression XInteger256 false . 
         refine {{ return_ FlexClient.owner_ }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_getFlex : UExpression XAddress false . 
         refine {{ return_ FlexClient.flex_ }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_hasExtWalletCode : UExpression XBool false . 
         refine {{ return_ {} (* bool_t { ! ! ext_wallet_code_ } *) }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_hasFlexWalletCode : UExpression XBool false . 
         refine {{ return_ {} (* bool_t { ! ! flex_wallet_code_ }  *)}} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_hasFlexWrapperCode : UExpression XBool false . 
         refine {{ return_ {} (* bool_t { ! ! flex_wrapper_code_ } *)  }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф_getPayloadForDeployInternalWallet ( owner_pubkey : XInteger256 ) ( owner_addr : addr_std_compact ) ( tons : XInteger128 ) : UExpression XCell false . 
         refine {{ owner_pubkey : ( XInteger256 ) @ "owner_pubkey" ; { _ } }} . 
         refine {{ owner_addr : ( addr_std_compact ) @ "owner_addr" ; { _ } }} . 
         refine {{ tons : ( XInteger128 ) @ "tons" ; { _ } }} . 
         refine {{ return_ {} (* build ( FlexDeployWalletArgs { !{ owner_pubkey } , !{ owner_addr } , !{ tons } } ) . endc ( ) *) }} . 
 Defined . 
 
 
 
 Definition FlexClient_Ф__fallback ( x : XCell ) : UExpression XInteger false . 
         refine {{ x : ( XCell ) @ "x" ; { _ } }} . 
         refine {{ return_ 0 }} . 
 Defined . 
 


Elpi TestDefinitions Definition constructor' (_depth: XInteger) : public UExpression PhantomType true :=
{{
    _depth: XInteger @ "_depth" ; 
    new 'xxx : XAddress @ "xxx" := {} ;
    require_ ( ((tvm.pubkey() != 0) && (tvm.pubkey() == msg.pubkey())) \\
                      (msg.sender() == m_parent), 1 ) ;
    tvm.accept();
    
    m_depth := !{_depth} 
}}.


End trainFuncsInternal.
End trainFuncs.








