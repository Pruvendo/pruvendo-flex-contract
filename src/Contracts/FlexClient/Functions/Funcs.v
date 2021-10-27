Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
From elpi Require Import elpi.
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Contracts.FlexClient.Ledger.
Require Import Contracts.FlexClient.Functions.FuncSig.
Require Import Contracts.FlexClient.Functions.FuncNotations.
Require Import Contracts.FlexClient.Interface.


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

Module Funcs (dc : ConstsTypesSig XTypesModule StateMonadModule) . 
 
Module Export FuncNotationsModuleForFuncs := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.tvmNotationsModule.

Module FuncsInternal <: SpecModuleForFuncNotations.SpecSig. 
 
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

Definition constructor ( pubkey : URValue ( XInteger256 ) false ) ( trading_pair_code : URValue ( XCell ) false ) ( xchg_pair_code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( { pubkey } != 0 ) , error_code::zero_owner_pubkey ) ; { _ } }} . 
 	 	 refine {{ _owner_ := { pubkey } ; { _ } }} . 
 	 	 refine {{ _trading_pair_code_ := { trading_pair_code } ; { _ } }} . 
 	 	 refine {{ _xchg_pair_code_ := { xchg_pair_code } ; { _ } }} . 
 	 	 refine {{ _workchain_id_ := {} (* Std :: get < addr_std > ( Address { tvm_myaddr ( ) } . val ( ) ) . workchain_id *) ; { _ } }} . 
 	 	 refine {{ _flex_ := {} (* Address :: make_std ( 0 , 0 ) *) }} . 
 Defined . 
 
 Definition setFlexCfg 
( tons_cfg : URValue ( TonsConfigLRecord ) false ) 
( flex : URValue ( XAddress ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _tons_cfg_ := { tons_cfg } ; { _ } }} . 
 	 	 refine {{ _flex_ := { flex }  }} . 
 Defined . 
 
 Definition setExtWalletCode ( ext_wallet_code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _ext_wallet_code_ ->set ( { ext_wallet_code } ) }} . 
 Defined . 
 
 Definition setFlexWalletCode ( flex_wallet_code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _flex_wallet_code_  ->set (  { flex_wallet_code } ) }} . 
 Defined . 
 
 
 
 
 Definition setFlexWrapperCode ( flex_wrapper_code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _flex_wrapper_code_  ->set (  { flex_wrapper_code } ) }} . 
 Defined . 
 
(* std::pair<StateInit, uint256> prepare_trading_pair_state_init_and_addr(DTradingPair pair_data, cell pair_code) {
  cell pair_data_cl = prepare_persistent_data<ITradingPair, void, DTradingPair>({}, pair_data);
  StateInit pair_init {
    /*split_depth*/{}, /*special*/{},
(*     pair_code, pair_data_cl, /*library*/{} *)
  };
  cell pair_init_cl = build(pair_init).make_cell();
  return { pair_init, uint256(tvm_hash(pair_init_cl)) };
} *)

 Definition deployTradingPair ( tip3_root : URValue ( XAddress ) false ) ( deploy_min_value : URValue ( XInteger128 ) false ) ( deploy_value : URValue ( XInteger128 ) false ) ( min_trade_amount : URValue ( XInteger128 ) false ) ( notify_addr : URValue ( XAddress ) false ) : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} .
 	 	 refine {{ new 'pair_data : ( TradingPairLRecord ) @ "pair_data" :=  
 	 	        [$ _flex_ ⇒ { TradingPair_ι_flex_addr_ } ; 
               { tip3_root } ⇒ { TradingPair_ι_tip3_root_ } ; 
                 0 ⇒ { TradingPair_ι_notify_addr_ }  
               $] ; { _ } }} . 
 	 	 refine {{ new 'state_init : ( StateInitLRecord ) @ "state_init" := {} ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := {} (* prepare_trading_pair_state_init_and_addr ( pair_data , trading_pair_code_ ) *) ; { _ } }} . 
 	 	 refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {} ; { _ } }} . 
 	 	             (*  ITradingPairPtr ( Address :: make_std ( workchain_id_ , std_addr ) )  *) 
(*  	 	 refine {{ trade_pair.deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( min_trade_amount , deploy_min_value , notify_addr ) ; { _ } }} .  *)
 	 	 refine {{ return_ {} (* trade_pair.get ( ) *) }} . 
 Defined . 

 Definition deployXchgPair ( tip3_major_root : URValue ( address_t ) false ) 
                           ( tip3_minor_root : URValue ( address_t ) false ) 
                           ( deploy_min_value : URValue ( XInteger128 ) false ) 
                           ( deploy_value : URValue ( XInteger128 ) false ) 
                           ( min_trade_amount : URValue ( XInteger128 ) false ) 
                           ( notify_addr : URValue ( address_t ) false ) 
                            : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} .
 	 	 refine {{ new 'pair_data : ( XchgPairLRecord ) @ "pair_data" :=  
               	 	 [$ (* _flex_  ⇒ { XchgPair_ι_flex_addr_ } ; *) 
                      { tip3_major_root } ⇒ { XchgPair_ι_tip3_major_root_ } ; 
                      { tip3_minor_root } ⇒ { XchgPair_ι_tip3_minor_root_ } ; 
                      0 ⇒ { XchgPair_ι_notify_addr_ }
                          $] ; { _ } }} . 
 	 	 refine {{ state_init : ( StateInitLRecord ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ std_addr : ( XAddress ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := {} (* prepare_xchg_pair_state_init_and_addr ( pair_data , xchg_pair_code_ ) *) ; { _ } }} . 
 	 	 refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {} ; { _ } }} . 
 	 	 refine {{ { trade_pair } := {} (* IXchgPairPtr ( Address :: make_std ( workchain_id_ , std_addr ) ) *) ; { _ } }} . 
(*  	 	 refine {{ trade_pair.deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( min_trade_amount , deploy_min_value , notify_addr ) ; { _ } }} .  *)
 	 	 refine {{ return_ {} (* trade_pair.get ( ) *) }} . 
 Defined .
 
 Definition deployPriceWithSell 
( price : URValue ( XInteger128 ) false ) 
( amount : URValue ( XInteger128 ) false ) 
( lend_finish_time : URValue ( XInteger32 ) false ) 
( min_amount : URValue ( XInteger128 ) false ) 
( deals_limit : URValue ( XInteger8 ) false ) 
( tons_value : URValue ( XInteger128 ) false ) 
( price_code : URValue ( XCell ) false ) 
( my_tip3_addr : URValue ( XAddress ) false ) 
( receive_wallet : URValue ( XAddress ) false ) 
( tip3cfg : URValue ( Tip3ConfigLRecord ) false ) 
( notify_addr : URValue ( XAddress ) false ) 
: UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'state_init : ( StateInitLRecord ) @ "state_init" := {} ; { _ } }} . 
 	 	 refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XAddress ) @ "std_addr" := {} ; { _ } }} . 
 

(*      refine {{ new 'qqq : (( StateInitLRecord # XAddress # XInteger256 )%sol) @ "qqq" := {} ; {_} }} .
     refine {{ {qqq} := preparePrice_ ( {price} {min_amount} {deals_limit} _flex_wallet_code_ {tip3cfg}  {price_code}  {notify_addr} ) ; { _ } }} .
 *)
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := {} (* preparePrice_ ( {price} {min_amount} {deals_limit} _flex_wallet_code_ {tip3cfg}  {price_code}  {notify_addr} ) *) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {} (* IPricePtr ( addr ) *); { _ } }} . 
 	 	 refine {{ new 'deploy_init_cl : ( XCell ) @ "deploy_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ { deploy_init_cl } := {} (* build ( { state_init } ) . endc ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'sell_args : ( SellArgsLRecord ) @ "sell_args" :=
                   [$ {amount} ⇒ {SellArgs_ι_amount} 
           (*  {receive_wallet} ⇒ { SellArgs_ι_receive_wallet } *) 
                    $] ; { _ } }} .
 	 	 refine {{ new 'payload : ( XCell ) @ "payload" := {} ; { _ } }} . 
 	 	 refine {{ { payload } := {} (* build ( { sell_args } ) . endc ( ) *) ; { _ } }} . 
     refine {{ new 'my_tip3 : ( XAddress ) @ "my_tip3" := { my_tip3_addr } ; { _ } }} .
 
(* 	 	 refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . lendOwnership ( address { tvm_myaddr ( ) } , uint128 ( 0 ) , std_addr , amount , lend_finish_time , deploy_init_cl , payload ) ; { _ } }} . *)
 	 	 refine {{ return_ !{price_addr} }} . 
 Defined . 
 
 Definition deployPriceWithBuy ( price : URValue ( XInteger128 ) false ) ( amount : URValue ( XInteger128 ) false ) ( order_finish_time : URValue ( XInteger32 ) false ) ( min_amount : URValue ( XInteger128 ) false ) ( deals_limit : URValue ( XInteger8 ) false ) ( deploy_value : URValue ( XInteger128 ) false ) ( price_code : URValue ( XCell ) false ) ( my_tip3_addr : URValue ( address_t ) false ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( notify_addr : URValue ( address_t ) false ) : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ state_init : ( StateInitLRecord ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ addr : ( XAddress ) @ "addr" ; { _ } }} . 
 	 	 refine {{ std_addr : ( XInteger256 ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := {} (* preparePrice_ ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code , notify_addr ) *) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr":= {} ; { _ } }} . 
 (*	 refine {{ price_addr.deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . buyTip3 ( amount , my_tip3_addr , order_finish_time ) ; { _ } }} . *)
 	 	 refine {{ return_ !{price_addr} }} . 
 Defined . 
 
 Definition cancelSellOrder ( price : URValue ( XInteger128 ) false ) ( min_amount : URValue ( XInteger128 ) false ) ( deals_limit : URValue ( XInteger8 ) false ) ( value : URValue ( XInteger128 ) false ) ( price_code : URValue ( XCell ) false ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( notify_addr : URValue ( address_t ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ state_init : ( StateInitLRecord ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ new 'addr : ( XAddress ) @ "addr":= {} ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XInteger256 ) @ "std_addr" := {}; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := {} (* preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code , notify_addr ) *) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {}  ; { _ } }} . 
(*  	 	 refine {{ price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelSell ( ) ; { _ } }} .  *)
refine {{ {price_addr} := !{price_addr} }} .
 Defined . 
 
 Definition cancelBuyOrder ( price : URValue ( XInteger128 ) false ) ( min_amount : URValue ( XInteger128 ) false ) ( deals_limit : URValue ( XInteger8 ) false ) ( value : URValue ( XInteger128 ) false ) ( price_code : URValue ( XCell ) false ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( notify_addr : URValue ( address_t ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'state_init : ( StateInitLRecord ) @ "state_init" := {}; { _ } }} . 
 	 	 refine {{ new 'addr : ( XAddress ) @ "addr":= {} ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XInteger256 ) @ "std_addr" := {}; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := {} (* preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code , notify_addr )  *); { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {}; { _ } }} . 
 	 	 refine {{ {price_addr} := !{price_addr} (* price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelBuy ( ) *) }} . 
 Defined . 
 
 Definition cancelXchgOrder ( sell : URValue ( XBool ) false ) ( price_num : URValue ( XInteger128 ) false ) ( price_denum : URValue ( XInteger128 ) false ) ( min_amount : URValue ( XInteger128 ) false ) ( deals_limit : URValue ( XInteger8 ) false ) ( value : URValue ( XInteger128 ) false ) ( xchg_price_code : URValue ( XCell ) false ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( notify_addr : URValue ( address_t ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'state_init : ( StateInitLRecord ) @ "state_init" := {}; { _ } }} . 
 	 	 refine {{ new 'addr : ( XAddress ) @ "addr":= {} ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XInteger256 ) @ "std_addr" := {}; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := {} (* preparePriceXchg ( price_num , price_denum , min_amount , deals_limit , major_tip3cfg , minor_tip3cfg , xchg_price_code , notify_addr ) *) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {} ; { _ } }} . 
 	 	 refine {{ if ( { sell } ) then { { _ } } else { { _ } } }} . 
 	 	 	 refine {{ {price_addr} := !{price_addr} (* price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelSell ( )*) }} . 
 	 	 refine {{ {price_addr} := !{price_addr} (* price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelBuy ( ) *) }} . 
 Defined . 
 
 Definition transfer ( dest : URValue ( address_t ) false ) ( value : URValue ( XInteger128 ) false ) ( bounce : URValue ( XBool ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () (*;  { _ } }} . 
 	 	 refine {{ tvm_transfer ( dest , value . get ( ) , bounce . get ( ) ) ; { _ } *) }} . 
 Defined . 
 
 Definition deployPriceXchg ( sell : URValue ( XBool ) false ) ( price_num : URValue ( XInteger128 ) false ) ( price_denum : URValue ( XInteger128 ) false ) ( amount : URValue ( XInteger128 ) false ) ( lend_amount : URValue ( XInteger128 ) false ) ( lend_finish_time : URValue ( XInteger32 ) false ) ( min_amount : URValue ( XInteger128 ) false ) ( deals_limit : URValue ( XInteger8 ) false ) ( tons_value : URValue ( XInteger128 ) false ) ( xchg_price_code : URValue ( XCell ) false ) ( my_tip3_addr : URValue ( address_t ) false ) ( receive_wallet : URValue ( address_t ) false ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( notify_addr : URValue ( address_t ) false ) : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'state_init : ( StateInitLRecord ) @ "state_init" := {}; { _ } }} . 
 	 	 refine {{ new 'addr : ( XAddress ) @ "addr":= {} ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XInteger256 ) @ "std_addr" := {}; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := {} (* preparePriceXchg ( price_num , price_denum , min_amount , deals_limit , major_tip3cfg , minor_tip3cfg , xchg_price_code , notify_addr ) *) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := !{addr} ; { _ } }} . 
 	 	 refine {{ new 'deploy_init_cl : ( XCell ) @ "deploy_init_cl" := {} (* ; { _ } }} . 
 	 	                           build ( { state_init } ) . endc ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'payload_args : ( PayloadArgsLRecord ) @ "payload_args" := 
             [$ 
                  { sell } ⇒ { PayloadArgs_ι_sell } ;
                  { amount } ⇒ { PayloadArgs_ι_amount } ;
                  { receive_wallet } ⇒ { PayloadArgs_ι_receive_tip3_wallet } ;
                  ( tvm.address () ) ⇒ { PayloadArgs_ι_client_addr } $] ; { _ } }} .
 	 	 refine {{ new 'payload : ( XCell ) @ "payload" := {} (* ; { _ } }} . 
 	 	 refine {{ { payload } := build ( { payload_args } ) . endc ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'my_tip3 : ( XAddress ) @ "payload" := {my_tip3_addr} (* ; { _ } }} . 
 	 	 refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . lendOwnership ( address { tvm_myaddr ( ) } , uint128 ( 0 ) , std_addr , lend_amount , lend_finish_time , deploy_init_cl , payload ) *) ; { _ } }} . 
 	 	 refine {{ return_ !{price_addr} }} . 
 Defined . 
 

(* std::pair<StateInit, uint256> prepare_wallet_state_init_and_addr(DTONTokenWallet wallet_data) {
  cell wallet_data_cl =
    prepare_persistent_data<ITONTokenWallet, wallet_replay_protection_t, DTONTokenWallet>(
#ifdef TIP3_ENABLE_EXTERNAL
      wallet_replay_protection_t::init(),
#else
      {},
#endif
      wallet_data);
  StateInit wallet_init {
    /*split_depth*/{}, /*special*/{},
    wallet_data.code_, wallet_data_cl, /*library*/{}
  };
  cell wallet_init_cl = build(wallet_init).make_cell();
  return { wallet_init, uint256(tvm_hash(wallet_init_cl)) };
} 

*)

 Definition deployWrapperWithWallet ( wrapper_pubkey : URValue ( XInteger256 ) false )
                                    ( wrapper_deploy_value : URValue ( XInteger128 ) false ) 
                                    ( wrapper_keep_balance : URValue ( XInteger128 ) false ) 
                                    ( ext_wallet_balance : URValue ( XInteger128 ) false ) 
                                    ( set_internal_wallet_value : URValue ( XInteger128 ) false ) 
                                    ( tip3cfg : URValue ( Tip3ConfigLRecord ) false ) 
                                    : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _ext_wallet_code_ ) , error_code::missed_ext_wallet_code ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wrapper_code_ ) , error_code::missed_flex_wrapper_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'wrapper_data : ( DWrapperLRecord ) @ "wrapper_data" := 
               	 	 [$ 
              ( {tip3cfg} ^^ Tip3Config.name ) ⇒ { DWrapper_ι_name_ } ;
              ( {tip3cfg} ^^ Tip3Config.symbol ) ⇒ { DWrapper_ι_symbol_ } ; 
              ( {tip3cfg} ^^ Tip3Config.decimals ) ⇒ { DWrapper_ι_decimals_ } ;  
                _workchain_id_ ⇒ { DWrapper_ι_workchain_id_ } ; 
                {wrapper_pubkey} ⇒ { DWrapper_ι_root_public_key_ } ; 
               {} ⇒ { DWrapper_ι_total_granted_ } ; 
               {} ⇒ { DWrapper_ι_internal_wallet_code_ } ; 
              ( ( tvm.address () ) -> set () ) ⇒ { DWrapper_ι_owner_address_ } ; 
               {wrapper_keep_balance} ⇒ { DWrapper_ι_start_balance_ } ; 
               {} ⇒ { DWrapper_ι_external_wallet_ } 
               $] ; { _ } }} .
 	 	 refine {{ new 'wrapper_init : ( StateInitLRecord ) @ "wrapper_init" := {} ; { _ } }} . 
 	 	 refine {{ new 'wrapper_hash_addr : ( XInteger256 ) @ "wrapper_hash_addr" := {} ; { _ } }} . 
 	 	 refine {{ [ { wrapper_init } , { wrapper_hash_addr } ] := {}(*  prepare_wrapper_state_init_and_addr ( flex_wrapper_code_ . get ( ) , wrapper_data ) *) ; { _ } }} . 
 	 	 refine {{ new 'wrapper_addr : ( XAddress ) @ "wrapper_addr" := {} ; { _ } }}.
(*  	 	 refine {{ IWrapperPtr wrapper_addr ( address : : make_std ( workchain_id_ , wrapper_hash_addr ) ) ; { _ } }} .  *)
 	 	 refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := {} ; { _ } }} . 
 	 	 refine {{ new 'wallet_hash_addr : ( XInteger256 ) @ "wallet_hash_addr" := {}  ; { _ } }} . 
 	 	 refine {{ [ { wallet_init } , { wallet_hash_addr } ] := {} (* prepare_external_wallet_state_init_and_addr ( tip3cfg . name , tip3cfg . symbol , tip3cfg . decimals , tip3cfg . root_public_key , wrapper_pubkey , tip3cfg . root_address , wrapper_addr . get ( ) , ext_wallet_code_ . get ( ) , workchain_id_ ) *) ; { _ } }} . 
 	 	 refine {{ new 'wallet_addr : ( XAddress ) @ "wallet_addr" := {} ; { _ } }}.
(*  	 	 refine {{ ITONTokenWalletPtr wallet_addr ( address : : make_std ( workchain_id_ , wallet_hash_addr ) ) ; { _ } }} . 
 	 	 refine {{ wallet_addr.deploy_noop ( wallet_init , Grams ( ext_wallet_balance . get ( ) ) ) ; { _ } }} . 
 	 	 refine {{ wrapper_addr.deploy ( wrapper_init , Grams ( wrapper_deploy_value . get ( ) ) ) . init ( wallet_addr . get ( ) ) ; { _ } }} . 
 	 	 refine {{ wrapper_addr ( Grams ( set_internal_wallet_value . get ( ) ) ) . setInternalWalletCode ( flex_wallet_code_ . get ( ) ) ; { _ } }} . 
 *) 	 	 refine {{ return_ !{wrapper_addr}   }} . 
 Defined . 
 

(* std::pair<StateInit, uint256> prepare_internal_wallet_state_init_and_addr(
  string name, string symbol, uint8 decimals, uint256 root_public_key,
  uint256 wallet_public_key, address root_address, std::optional<address> owner_address,
  cell code, int8 workchain_id
) {
  DTONTokenWalletInternal wallet_data {
    name, symbol, decimals,
    uint128(0), root_public_key, wallet_public_key,
    root_address, owner_address,
    {}, code, workchain_id
  };
  cell wallet_data_cl =
    prepare_persistent_data<ITONTokenWallet, void, DTONTokenWalletInternal>({}, wallet_data);
  StateInit wallet_init {
    /*split_depth*/{}, /*special*/{},
    code, wallet_data_cl, /*library*/{}
  };
  cell wallet_init_cl = build(wallet_init).make_cell();
  return { wallet_init, uint256(tvm_hash(wallet_init_cl)) };
} *)

 Definition deployEmptyFlexWallet ( pubkey : URValue ( XInteger256 ) false ) ( tons_to_wallet : URValue ( XInteger128 ) false ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) false ) : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'init : ( StateInitLRecord ) @ "init" := {} ; { _ } }} . 
 	 	 refine {{ new 'hash_addr : ( XInteger256 ) @ "hash_addr" := {} ; { _ } }} . 
 	 	 refine {{ [ { init } , { hash_addr } ] := {} (* prepare_internal_wallet_state_init_and_addr ( tip3cfg . name , tip3cfg . symbol , tip3cfg . decimals , tip3cfg . root_public_key , pubkey , tip3cfg . root_address , address { tvm_myaddr ( ) } , flex_wallet_code_ . get ( ) , workchain_id_ ) *) ; { _ } }} . 
 	 	 refine {{ new 'new_wallet : ( XAddress ) @ "new_wallet" := {} ; { _ } }}.
(*  	 	 refine {{ ITONTokenWalletPtr new_wallet ( address : : make_std ( workchain_id_ , hash_addr ) ) ; { _ } }} . 
 	 	 refine {{ new_wallet.deploy_noop ( init , Grams ( tons_to_wallet . get ( ) ) ) ; { _ } }} . *) 
 	 	 refine {{ return_ !{new_wallet} }} . 
 Defined . 
  
 Definition burnWallet ( tons_value : URValue ( XInteger128 ) false ) ( out_pubkey : URValue ( XInteger256 ) false ) ( out_internal_owner : URValue ( address_t ) false ) ( my_tip3_addr : URValue ( address_t ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'my_tip3 : ( XAddress ) @ "my_tip3" := {} ; { _ } }}.
(*  	 	 refine {{ ITONTokenWalletPtr my_tip3 ( my_tip3_addr ) ; { _ } }} . 
 	 	 refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) ) . burn ( out_pubkey , out_internal_owner )   }} . 
 *) 
refine {{ {my_tip3} := !{my_tip3} }} .
Defined . 
 
 Definition getOwner : UExpression XInteger256 false . 
 	 	 refine {{ return_ _owner_ }} . 
 Defined . 
 
 Definition getFlex : UExpression XAddress false . 
 	 	 refine {{ return_ _flex_ }} . 
 Defined . 
 
 Definition hasExtWalletCode : UExpression XBool false . 
 	 	 refine {{ return_ {} (* ( ~ ( ~ _ext_wallet_code_ ) ) *) }} . 
 Defined . 
  
 Definition hasFlexWalletCode : UExpression XBool false . 
 	 	 refine {{ return_ {} (* bool_t { ! ! flex_wallet_code_ } *) }} . 
 Defined . 
 
 Definition hasFlexWrapperCode : UExpression XBool false . 
 	 	 refine {{ return_ {} (* bool_t { ! ! flex_wrapper_code_ } *)  }} . 
 Defined . 
 
 Definition getPayloadForDeployInternalWallet ( owner_pubkey : URValue ( XInteger256 ) false ) ( owner_addr : URValue ( address_t ) false ) ( tons : URValue ( XInteger128 ) false ) : UExpression XCell false . 
 	 	 refine {{ return_ {} (* build ( FlexDeployWalletArgs { { owner_pubkey } , { owner_addr } , { tons } } ) . endc ( ) *) }} . 
 Defined . 
 
 Definition _fallback ( msg : URValue ( XCell ) false ) ( msg_body : URValue ( XSlice ) false ) : UExpression XInteger false . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
(* std::pair<StateInit, uint256> prepare_price_state_init_and_addr(DPrice price_data, cell price_code) {
  cell price_data_cl = prepare_persistent_data<IPrice, void, DPrice>({}, price_data);
  StateInit price_init {
    /*split_depth*/{}, /*special*/{},
    price_code, price_data_cl, /*library*/{}
  };
  cell price_init_cl = build(price_init).make_cell();
  return { price_init, uint256(tvm_hash(price_init_cl)) };
} *)

Definition preparePrice ( price : URValue ( XInteger128 ) false ) ( min_amount : URValue ( XInteger128 ) false ) ( deals_limit : URValue ( XInteger8 ) false ) ( tip3_code : URValue ( XCell ) false ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( price_code : URValue ( XCell ) false ) ( notify_addr : URValue ( address_t ) false ) : UExpression ( StateInitLRecord # XAddress # XInteger256 )%sol false . 
 	 	 refine {{ new 'price_data : ( DPriceLRecord ) @ "price_data" :=  
               	 	 [$ { price } ⇒ { DPrice_ι_price_ } ; 
               0 ⇒ { DPrice_ι_sells_amount_ } ; 
               0 ⇒ { DPrice_ι_buys_amount_ } ; 
(*  _flex_  ⇒ { DPrice_ι_flex_ } ; *)
               { min_amount } ⇒ { DPrice_ι_min_amount_ } ; 
               { deals_limit } ⇒ { DPrice_ι_deals_limit_ } ; 
               { notify_addr } ⇒ { DPrice_ι_notify_addr_ } ; 
                _workchain_id_  ⇒ { DPrice_ι_workchain_id_ } ; 
                _tons_cfg_  ⇒ { DPrice_ι_tons_cfg_ } ; 
               { tip3_code } ⇒ { DPrice_ι_tip3_code_ } ; 
               { tip3cfg } ⇒ { DPrice_ι_tip3cfg_ } ; 
               {} ⇒ { DPrice_ι_sells_ } ; 
               {} ⇒ { DPrice_ι_buys_ } 
               $] ; { _ } }} . 
 	 	 refine {{ new 'state_init : ( StateInitLRecord ) @ "state_init" := {} ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XInteger256 ) @ "std_addr" := {} ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := {} (* prepare_price_state_init_and_addr ( price_data , price_code ) *) ; { _ } }} . 
 	 	 refine {{ new 'addr : ( XAddress ) @ "addr" := {} ; { _ } }} . 
(*  	 	 refine {{ { addr } := Address :: make_std ( workchain_id_ , std_addr ) ; { _ } }} .  *)
 	 	 refine {{ return_ {} (* [ !{ state_init } , !{ addr } , !{ std_addr } ] *) }} . 
 Defined . 

(* std::pair<StateInit, uint256> prepare_price_xchg_state_init_and_addr(DPriceXchg price_data, cell price_code) {
  cell price_data_cl = prepare_persistent_data<IPriceXchg, void, DPriceXchg>({}, price_data);
  StateInit price_init {
    /*split_depth*/{}, /*special*/{},
    price_code, price_data_cl, /*library*/{}
  };
  cell price_init_cl = build(price_init).make_cell();
  return { price_init, uint256(tvm_hash(price_init_cl)) };
} *)
 
 Definition preparePriceXchg ( price_num : URValue ( XInteger128 ) false ) ( price_denum : URValue ( XInteger128 ) false ) ( min_amount : URValue ( XInteger128 ) false ) ( deals_limit : URValue ( XInteger8 ) false ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) false ) ( price_code : URValue ( XCell ) false ) ( notify_addr : URValue ( address_t ) false ) : UExpression ( StateInitLRecord # XAddress # XInteger256 )%sol false . 
 	 	 refine {{ new 'price_data : ( DPriceXchgLRecord ) @ "price_data" :=  
               [$
                 [$ {price_num} ⇒ {RationalPrice_ι_num} ; 
                    {price_denum} ⇒ {RationalPrice_ι_denum} $] 
                                     ⇒ { DPriceXchg_ι_price_ } ;
               0 ⇒ { DPriceXchg_ι_sells_amount_ } ;
               0 ⇒ { DPriceXchg_ι_buys_amount_ }  ;
(*  _flex_ ⇒ { DPriceXchg_ι_flex_ } ; *)
               { min_amount } ⇒ { DPriceXchg_ι_min_amount_ } ;
               { deals_limit } ⇒ { DPriceXchg_ι_deals_limit_ } ; 
               { notify_addr } ⇒ { DPriceXchg_ι_notify_addr_ } ; 
               _workchain_id_ ⇒ { DPriceXchg_ι_workchain_id_ } ;
               _tons_cfg_ ⇒ { DPriceXchg_ι_tons_cfg_ } ;

               ( _flex_wallet_code_ -> get_default () ) ⇒ { DPriceXchg_ι_tip3_code_ } ;

               { major_tip3cfg } ⇒ { DPriceXchg_ι_major_tip3cfg_ } ; 
               { minor_tip3cfg } ⇒ { DPriceXchg_ι_minor_tip3cfg_ } ; 
               {} ⇒ { DPriceXchg_ι_sells_ } ; 
               {} ⇒ { DPriceXchg_ι_buys_ }  
                                             $] ; { _ } }} . 
 	 	 refine {{ new 'state_init : ( StateInitLRecord ) @ "state_init" := {} ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XInteger256 ) @ "std_addr" := {} ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := {} (* prepare_price_xchg_state_init_and_addr ( price_data , price_code ) *) ; { _ } }} . 
 	 	 refine {{ new 'addr : ( XAddress ) @ "addr" := {} (* Address :: make_std ( workchain_id_ , std_addr ) *) ; { _ } }} . 
 	 	 refine {{ return_ {} (* [ !{ state_init } , !{ addr } , !{ std_addr } ] *) }} . 
 Defined . 

End FuncsInternal.
End Funcs.








