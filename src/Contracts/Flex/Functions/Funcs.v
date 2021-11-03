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
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.Flex.Ledger.
Require Import Contracts.Flex.Functions.FuncSig.
Require Import Contracts.Flex.Functions.FuncNotations.
Require Import Contracts.Flex.Interface.

(*this elpi code move to the Ursus lib afterwards*)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.


Elpi Command AddLocalState.

Elpi Accumulate lp:{{

main [Name , Term, LocalStateFieldT] :-
  trm TrmInternal = Term,
  trm LocalStateField = LocalStateFieldT,
  str NameStr = Name,
  N is NameStr ^ "_j",
  coq.env.add-axiom N  (app [LocalStateField , TrmInternal]) _ , 
  coq.locate  N GR, 
  coq.TC.declare-instance GR 0.
  /* coq.say TrmInternal. */
main _ :- coq.error "usage: AddLocalState <name> <term> <LocalStateField>".

}}.

Elpi Typecheck.
Elpi Export AddLocalState.

Module Funcs (dc : ConstsTypesSig XTypesModule StateMonadModule) .

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

Export SpecModuleForFuncNotations(* ForFuncs *).tvmNotationsModule.

Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Local Notation UE := (UExpression _ _)(only parsing).
Local Notation UEf := (UExpression _ false)(only parsing).
Local Notation UEt := (UExpression _ true)(only parsing).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
Notation " 'private' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.


Definition constructor ( deployer_pubkey : URValue ( XInteger256 ) false ) ( ownership_description : URValue ( XString ) false ) ( owner_address : URValue ( XMaybe XAddress ) false ) ( tons_cfg : URValue ( TonsConfigLRecord ) false ) ( deals_limit : URValue ( XInteger8 ) false ) ( listing_cfg : URValue ( ListingConfigLRecord ) false ) : UExpression PhantomType true . 
 	 	 refine {{ _deployer_pubkey_ := { deployer_pubkey } ; { _ } }} . 
 	 	 refine {{ _ownership_description_ := { ownership_description } ; { _ } }} . 
 	 	 refine {{ _owner_address_ := { owner_address } ; { _ } }} . 
 	 	 refine {{ _deals_limit_ := { deals_limit } ; { _ } }} . 
 	 	 refine {{ _tons_cfg_ := { tons_cfg } ; { _ } }} . 
 	 	 refine {{ _listing_cfg_ := { listing_cfg } ; { _ } }} . 
 	 	 refine {{ _workchain_id_ := {} (* get ( address { tvm_myaddr ( ) } . val ( ) ) . workchain_id *) ; { _ } }} . 
 	 	 refine {{ require_ ( (({listing_cfg} ^^ ListingConfig.register_pair_cost) >= 
                          ( {listing_cfg} ^^ ListingConfig.reject_pair_cost )
                          + ( {listing_cfg} ^^ ListingConfig.register_return_value ) ) , 1(* error_code::costs_inconsistency *) ) ; { _ } }} . 
refine {{ return_ {} }} .
 Defined . 

 Definition constructor_left { R a1 a2 a3 a4 a5 a6 }  ( deployer_pubkey : URValue ( XInteger256 ) a1 ) ( ownership_description : URValue ( XString ) a2 ) ( owner_address : URValue ( XMaybe XAddress ) a3 ) ( tons_cfg : URValue ( TonsConfigLRecord ) a4 ) ( deals_limit : URValue ( XInteger8 ) a5 ) ( listing_cfg : URValue ( ListingConfigLRecord ) a6 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) constructor 
 deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg ) . 
 
 Notation " 'constructor_' '(' deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg ')' " := 
 ( constructor_left 
 deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg ) 
 (in custom ULValue at level 0 , deployer_pubkey custom URValue at level 0 
 , ownership_description custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , tons_cfg custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 
 
(*   void setSpecificCode(uint8 type, cell code) {
    switch (static_cast<code_type>(type.get())) {
    case code_type::trade_pair_code: setPairCode(code); return;
    case code_type::xchg_pair_code: setXchgPairCode(code); return;
    case code_type::wrapper_code: setWrapperCode(code); return;
    case code_type::ext_wallet_code: setExtWalletCode(code); return;
    case code_type::flex_wallet_code: setFlexWalletCode(code); return;
    case code_type::price_code: setPriceCode(code); return;
    case code_type::xchg_price_code: setXchgPriceCode(code); return;
    }
  }
 *)

 Definition setPairCode ( code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _pair_code_ ) , 1(* error_code::cant_override_code *) ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , 1(* error_code::sender_is_not_deployer *) ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ require_ ( ( {code} -> to_slice () -> refs () == #{2} ) , 1(* error_code::unexpected_refs_count_in_code *) ) ; { _ } }} . 
 	 	 refine {{ _pair_code_ := {} (* builder ( ) . stslice ( code.ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 
 
 
 
 
 Definition setXchgPairCode ( code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _xchg_pair_code_ ) , 1(* error_code::cant_override_code *) ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , 1(* error_code::sender_is_not_deployer *) ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ require_ ( ( {code} -> to_slice () -> refs () == #{2} ) , 1(* error_code::unexpected_refs_count_in_code *) ) ; { _ } }} . 
 	 	 refine {{ _xchg_pair_code_ := {}(* builder ( ) . stslice ( code ^^ XCell:ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 
 
 Definition setWrapperCode ( code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ! _wrapper_code_ ) , 1(* error_code::cant_override_code *) ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , 1(* error_code::sender_is_not_deployer *) ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ require_ ( ( {code} -> to_slice () -> refs () == #{2} ) , 1(* error_code::unexpected_refs_count_in_code *) ) ; { _ } }} . 
 	 	 refine {{ _wrapper_code_ := {} (* builder ( ) . stslice ( code ^^ XCell:ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 


 Definition setPriceCode ( code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _price_code_ ) , 1(* error_code::cant_override_code *) ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , 1(* error_code::sender_is_not_deployer *) ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _price_code_ -> set ( { code } ) }} . 
 Defined . 
 
 Definition setXchgPriceCode ( code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _xchg_price_code_ ) , 1(* error_code::cant_override_code *) ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , 1(* error_code::sender_is_not_deployer *) ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _xchg_price_code_ -> set ({ code }) }} . 
 Defined .  
 
 Definition setExtWalletCode ( code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _ext_wallet_code_ ) , 1 (*  error_code::cant_override_code *) ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , 1 (* error_code::sender_is_not_deployer *) ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _ext_wallet_code_ -> set ( { code } ) }} . 
 Defined . 
 
 Definition setFlexWalletCode ( code : URValue ( XCell ) false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _flex_wallet_code_ ) , 1 (* error_code::cant_override_code *) ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , 1 (*  error_code::sender_is_not_deployer *) ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _flex_wallet_code_ -> set ( { code } ) }} . 
 Defined . 
 
 
 Definition transfer ( tto : URValue ( XAddress ) false ) ( tons : URValue ( XInteger128 ) false ) : UExpression PhantomType false . 
(*  	 	 refine {{ check.owner () ; { _ } }} .  *)
 	 	 refine {{ tvm.accept () (* ; { _ } }} . 
 	 	 refine {{ tvm_transfer ( tto , tons . get ( ) , true ) *) }} . 
 Defined . 

 Definition prepare_trading_pair_state_init_and_addr ( pair_data : URValue ( DTradingPairLRecord ) false ) ( pair_code : URValue ( XCell ) false ) : UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 	 	 refine {{ new 'pair_data_cl : ( XCell ) @ "pair_data_cl" := {} ; { _ } }} . 
 	 	 refine {{ { pair_data_cl } := {} (* prepare_persistent_data ( { } , pair_data ) *) ; { _ } }} . 
 	 	 refine {{ new 'pair_init : ( StateInitLRecord ) @ "pair_init" := 
                 [$ {}  ⇒ {StateInit_ι_split_depth} ;
                    {}  ⇒ {StateInit_ι_special} ; 
           ( ({pair_code}) -> set () ) ⇒ {StateInit_ι_code} ; 
           ( (!{pair_data_cl}) -> set () ) ⇒ {StateInit_ι_data} ; 
            {}  ⇒ {StateInit_ι_library} $] ; { _ } }} .

 	 	 refine {{ new 'pair_init_cl : ( XCell ) @ "pair_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ { pair_init_cl } := {} (* build ( !{ pair_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ pair_init } , {} (* tvm_hash ( pair_init_cl ) *) ] }} . 
 Defined . 

 Definition prepare_trading_pair_state_init_and_addr_right { a1 a2 }  ( pair_data : URValue ( DTradingPairLRecord ) a1 ) ( pair_code : URValue ( XCell ) a2 ) : URValue ( StateInitLRecord # XInteger256 )%sol ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_trading_pair_state_init_and_addr 
 pair_data pair_code ) . 
 
 Notation " 'prepare_trading_pair_state_init_and_addr_' '(' pair_data ',' pair_code ')' " := 
 ( prepare_trading_pair_state_init_and_addr_right 
 pair_data pair_code ) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 
 , pair_code custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_trading_pair ( flex : URValue ( XAddress ) false ) ( tip3_root : URValue ( XAddress ) false ) ( pair_code : URValue ( XCell ) false ) : UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 	 	 refine {{ new 'pair_data : ( DTradingPairLRecord ) @ "pair_data" :=  
               	 	 [$ ( tvm.address () ) ⇒ { DTradingPair_ι_flex_addr_ } ; 
                     { tip3_root } ⇒ { DTradingPair_ι_tip3_root_ } ; 
                     0 ⇒ { DTradingPair_ι_min_amount_ } ; 
                     0 ⇒ { DTradingPair_ι_notify_addr_ }  
                    $] ; { _ } }} . 
 	 	 refine {{ return_ ( prepare_trading_pair_state_init_and_addr_ ( !{ pair_data } , { pair_code } ) ) }} . 
 Defined .
 
 Definition prepare_trading_pair_right { a1 a2 a3 }  ( flex : URValue ( XAddress ) a1 ) ( tip3_root : URValue ( XAddress ) a2 ) ( pair_code : URValue ( XCell ) a3 ) : URValue ( StateInitLRecord # XInteger256 )%sol ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) prepare_trading_pair 
 flex tip3_root pair_code ) . 
 
 Notation " 'prepare_trading_pair_' '(' flex ',' tip3_root ',' pair_code ')' " := 
 ( prepare_trading_pair_right 
 flex tip3_root pair_code ) 
 (in custom URValue at level 0 , flex custom URValue at level 0 
 , tip3_root custom URValue at level 0 
 , pair_code custom URValue at level 0 ) : ursus_scope . 

 Definition registerTradingPair ( pubkey : URValue ( XInteger256 ) false ) ( tip3_root : URValue ( XAddress ) false ) ( min_amount : URValue ( XInteger128 ) false ) ( notify_addr : URValue ( XAddress ) false ) : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( {}  (* int.value () *) > ( _listing_cfg_ ^^ ListingConfig.register_pair_cost) ) , 1 (* error_code::not_enough_funds *) ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( ~ {} (* _trading_pair_listing_requests_ .contains ( pubkey.get ( ) ) *) ) , 1(* error_code::trading_pair_with_such_pubkey_already_requested *) ) ; { _ } }} . 
(*  	 	 refine {{ trading_pair_listing_requests_.set_at ( pubkey . get ( ) , { int_sender ( ) , uint128 ( int_value ( ) . get ( ) ) - listing_cfg_ . register_return_value , tip3_root , min_amount , notify_addr } ) ; { _ } }} .  *)
(*  	 	 refine {{ set_int_return_value ( listing_cfg_ . register_return_value . get ( ) ) ; { _ } }} .  *)
 	 	 refine {{ new 'state_init : ( StateInitLRecord ) @ "state_init" := {} ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XInteger256 ) @ "std_addr" := {} ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := prepare_trading_pair_ ( tvm.address () , {tip3_root} , _pair_code_ -> get_default () ) ; { _ } }} . 
 	 	 refine {{ return_ {} (* Address :: make_std ( workchain_id_ , std_addr ) *) }} . 
 Defined .
 
Definition approveTradingPairImpl ( pubkey : URValue ( XInteger256 ) false ) 
( trading_pair_listing_requests : URValue ( XHMap XInteger256 TradingPairListingRequestLRecord ) false ) ( pair_code : URValue ( XCell ) false ) ( workchain_id : URValue ( XInteger8 ) false ) ( listing_cfg : URValue ( ListingConfigLRecord ) false ) : UExpression ( XAddress # (XHMap XInteger256 TradingPairListingRequestLRecord) )%sol true . 
 	 	 refine {{ new 'opt_req_info : ( XMaybe TradingPairListingRequestLRecord ) @ "opt_req_info" := {} ; { _ } }} . 
 	 	                     (* trading_pair_listing_requests.extract ( pubkey.get ( ) ) *)  
 	 	 refine {{ require_ ( !{opt_req_info}  , 1 (* error_code::trading_pair_not_requested *) ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( TradingPairListingRequestLRecord ) @ "req_info" := {} ; { _ } }} . 
 	 	 refine {{ { req_info } := (!{opt_req_info}) -> get_default () ; { _ } }} . 
 	 	 refine {{ state_init : ( StateInitLRecord ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ std_addr : ( XInteger256 ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := 
                prepare_trading_pair_ ( tvm.address () , 
                (!{req_info}) ^^ TradingPairListingRequest.tip3_root , 
                {pair_code} ) ; { _ } }} . 
 	 	 refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {} (*  
 	 	  ITradingPairPtr ( Address :: make_std ( !{ workchain_id } , std_addr ) )  *); { _ } }} . 
(* 	 	 refine {{ trade_pair.deploy ( state_init , Grams ( listing_cfg . pair_deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( req_info . min_amount , listing_cfg . pair_keep_balance , req_info . notify_addr ) ; { _ } }} .  *)
 	 	 refine {{ new 'remaining_funds : ( XInteger128 ) @ "remaining_funds" := {} (*  
 	 	   req_info.client_funds - listing_cfg ^^ ListingConfigLRecord:register_pair_cost *) ; { _ } }} . 
(*  	 	 refine {{ IListingAnswerPtr ( req_info . client_addr ) ( Grams ( remaining_funds . get ( ) ) ) . onTradingPairApproved ( pubkey , trade_pair . get ( ) ) ; { _ } }} .  *)
 	 	 refine {{ return_ [ !{trade_pair} , {trading_pair_listing_requests} ] }} . 
 Defined .

 Definition approveTradingPairImpl_right { a1 a2 a3 a4 a5 }  
( pubkey : URValue ( XInteger256 ) a1 ) 
( trading_pair_listing_requests : URValue ( XHMap XInteger256 TradingPairListingRequestLRecord ) a2 ) 
( pair_code : URValue ( XCell ) a3 )
 ( workchain_id : URValue ( XInteger8 ) a4 ) 
( listing_cfg : URValue ( ListingConfigLRecord ) a5 ) : URValue ( XAddress # (XHMap XInteger256 TradingPairListingRequestLRecord) )%sol true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) approveTradingPairImpl 
 pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg ) . 
 
 Notation " 'approveTradingPairImpl_' '(' pubkey , trading_pair_listing_requests , pair_code , workchain_id , listing_cfg ')' " := 
 ( approveTradingPairImpl_right 
 pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , trading_pair_listing_requests custom URValue at level 0 
 , pair_code custom URValue at level 0 
 , workchain_id custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 


 Definition approveTradingPair_INTERNAL ( pubkey : URValue ( XInteger256 ) false ) : UExpression XAddress true . 
(*  	 	 refine {{ check_owner ( ) ; { _ } }} .  *)
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {} ; { _ } }} . 
 	 	 refine {{ new 'new_trading_pair_listing_requests : 
         ( XHMap XInteger256 TradingPairListingRequestLRecord ) @ "new_trading_pair_listing_requests" := {} ; { _ } }} . 
 	 	 refine {{ [ { trade_pair } , { new_trading_pair_listing_requests } ] := 
            approveTradingPairImpl_ ( {pubkey} , _trading_pair_listing_requests_ , _pair_code_ -> get_default () , _workchain_id_ , _listing_cfg_ ) ; { _ } }} . 
 	 	 refine {{ _trading_pair_listing_requests_ := !{new_trading_pair_listing_requests} ; { _ } }} . 
 	 	 refine {{ new 'value_gr : XInteger @ "value_gr" := {} (* int_value ( ) *) ; { _ } }} . 
(*  	 	 refine {{ tvm_rawreserve ( tvm_balance ( ) - value_gr ( ) , rawreserve_flag : : up_to ) ; { _ } }} .  *)
(*  	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) }} .  *)
 	 refine {{ return_ !{ trade_pair } }} . 
 Defined .

 Definition approveTradingPair_INTERNAL_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) approveTradingPair_INTERNAL 
 pubkey ) . 
 
 Notation " 'approveTradingPair_INTERNAL_' '(' pubkey ')' " := 
 ( approveTradingPair_INTERNAL_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition approveTradingPair_EXTERNAL ( pubkey : URValue ( XInteger256 ) false ) : UExpression XAddress true . 
(*  	 	 refine {{ check_owner ( ) ; { _ } }} .  *)
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {} ; { _ } }} . 
 	 	 refine {{ new 'new_trading_pair_listing_requests : 
         ( XHMap XInteger256 TradingPairListingRequestLRecord ) @ "new_trading_pair_listing_requests" := {} ; { _ } }} . 
 	 	 refine {{ [ { trade_pair } , { new_trading_pair_listing_requests } ] := 
            approveTradingPairImpl_ ( {pubkey} , _trading_pair_listing_requests_ , _pair_code_ -> get_default () , _workchain_id_ , _listing_cfg_ ) ; { _ } }} . 
 	 	 refine {{ _trading_pair_listing_requests_ := !{new_trading_pair_listing_requests} ; { _ } }} . 
  	 refine {{ return_ !{ trade_pair } }} . 
Defined .

 Definition approveTradingPair_EXTERNAL_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) approveTradingPair_EXTERNAL 
 pubkey ) . 
 
 Notation " 'approveTradingPair_EXTERNAL_' '(' pubkey ')' " := 
 ( approveTradingPair_EXTERNAL_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition rejectTradingPairImpl ( pubkey : URValue ( XInteger256 ) false ) 
( trading_pair_listing_requests : URValue ( XHMap XInteger256 TradingPairListingRequestLRecord ) false ) 
( listing_cfg : URValue ( ListingConfigLRecord ) false ) : UExpression ( XHMap XInteger TradingPairListingRequestLRecord ) true . 

 	 	 refine {{ new 'opt_req_info : ( XMaybe TradingPairListingRequestLRecord ) @ "opt_req_info" := {} ; { _ } }} . 
(*  	 	 refine {{ { opt_req_info } := trading_pair_listing_requests.extract ( pubkey ) ; { _ } }} .  *)
 	 	 refine {{ require_ ( !{ opt_req_info }  , 1 (* error_code::trading_pair_not_requested *) ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( TradingPairListingRequestLRecord ) @ "req_info" := 
                    (!{opt_req_info}) -> get_default ()  ; { _ } }} . 
 	 	 refine {{ new 'remaining_funds : ( XInteger128 ) @ "remaining_funds" := 
            ( (!{req_info}) ^^ TradingPairListingRequest.client_funds ) - ( ({listing_cfg}) ^^ ListingConfig.reject_pair_cost ) ; { _ } }} . 
(*  	 	 refine {{ IListingAnswerPtr( req_info . client_addr ) ( Grams ( remaining_funds . get ( ) ) ) . onTradingPairRejected ( pubkey ) ; { _ } }} .  *)
 	 	 refine {{ return_ { trading_pair_listing_requests } }} . 
 Defined . 

 Definition rejectTradingPairImpl_right { a1 a2 a3 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( trading_pair_listing_requests : URValue ( XHMap XInteger256  TradingPairListingRequestLRecord ) a2 ) ( listing_cfg : URValue ( ListingConfigLRecord ) a3 ) : URValue ( XHMap XInteger256 TradingPairListingRequestLRecord ) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) rejectTradingPairImpl 
 pubkey trading_pair_listing_requests listing_cfg ) . 

 Notation " 'rejectTradingPairImpl_' '(' pubkey , trading_pair_listing_requests , listing_cfg ')' " := 
 ( rejectTradingPairImpl_right 
 pubkey trading_pair_listing_requests listing_cfg ) 
 (in custom URValue at level 0 , 
   pubkey custom URValue at level 0 
 , trading_pair_listing_requests custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope .

 Definition rejectTradingPair_INTERNAL ( pubkey : URValue ( XInteger256 ) false ) : UExpression XBool true . 
(*  	 	 refine {{ check_owner ( ) ; { _ } }} .  *)
 	 	 refine {{ _trading_pair_listing_requests_ := 
              rejectTradingPairImpl_ ( { pubkey } , _trading_pair_listing_requests_ , _listing_cfg_ ) ; { _ } }} . 
 	 	 refine {{ new 'value_gr : XInteger @ "value_gr" := {} (* int_value ( ) *) ; { _ } }} . 
(*  	 	 	 refine {{ tvm_rawreserve ( tvm_balance ( ) - value_gr ( ) , rawreserve_flag : : up_to ) ; { _ } }} .  *)
 	 refine {{ new 'value_gr : XInteger @ "value_gr" := {} (* int_value ( ) *) ; { _ } }} .  	 	 	 
(*    refine {{ Set_int_return_flag ( SEND_ALL_GAS ) }} .  *)
 	 refine {{ return_ TRUE }} . 
 Defined . 

 Definition rejectTradingPair_INTERNAL_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) rejectTradingPair_INTERNAL 
 pubkey ) . 
 
 Notation " 'rejectTradingPair_INTERNAL_' '(' pubkey ')' " := 
 ( rejectTradingPair_INTERNAL_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition rejectTradingPair_EXTERNAL ( pubkey : URValue ( XInteger256 ) false ) : UExpression XBool true . 
(*  	 	 refine {{ check_owner ( ) ; { _ } }} .  *)
 	 	 refine {{ _trading_pair_listing_requests_ := 
              rejectTradingPairImpl_ ( { pubkey } , _trading_pair_listing_requests_ , _listing_cfg_ ) ; { _ } }} . 
 	 refine {{ return_ TRUE }} . 
 Defined . 

 Definition rejectTradingPair_EXTERNAL_right { a1 }  ( pubkey : URValue ( XInteger256 ) a1 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) rejectTradingPair_EXTERNAL 
 pubkey ) . 
 
 Notation " 'rejectTradingPair_EXTERNAL_' '(' pubkey ')' " := 
 ( rejectTradingPair_EXTERNAL_right 
 pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_xchg_pair_state_init_and_addr 
( pair_data : URValue ( DXchgPairLRecord ) false ) 
( pair_code : URValue ( XCell ) false ) 
: UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 	 	 refine {{ new 'pair_data_cl : ( XCell ) @ "pair_data_cl" := {} 
                 (* := prepare_persistent_data ( { } , pair_data ) *) ; { _ } }} . 
 	 	 refine {{ new 'pair_init : ( StateInitLRecord ) @ "pair_init" := 
                [$ {} ⇒ { StateInit_ι_split_depth } ; 
                   {} ⇒ { StateInit_ι_special } ; 
                  {pair_code} -> set () ⇒ { StateInit_ι_code } ;
                (!{pair_data_cl}) -> set () ⇒ { StateInit_ι_data } ;
                 {} ⇒ { StateInit_ι_library } $] ; { _ } }} . 
 	 	 refine {{ new 'pair_init_cl : ( XCell ) @ "pair_init_cl" := {} 
                (* build ( !{ pair_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ pair_init } , {} (* tvm_hash ( pair_init_cl ) *) ] }} . 
 Defined . 

 Definition prepare_xchg_pair_state_init_and_addr_right { a1 a2 }  ( pair_data : URValue ( DXchgPairLRecord ) a1 ) ( pair_code : URValue ( XCell ) a2 ) : URValue ( StateInitLRecord # XInteger256 )%sol ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_xchg_pair_state_init_and_addr 
 pair_data pair_code ) . 
 
 Notation " 'prepare_xchg_pair_state_init_and_addr_' '(' pair_data , pair_code ')' " := 
 ( prepare_xchg_pair_state_init_and_addr_right 
 pair_data pair_code ) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 
 , pair_code custom URValue at level 0 ) : ursus_scope .

Definition approveXchgPairImpl ( pubkey : URValue ( XInteger256 ) false ) 
( xchg_pair_listing_requests : URValue ( XHMap XInteger XchgPairListingRequestLRecord ) false ) 
( xchg_pair_code : URValue ( XCell ) false ) 
( workchain_id : URValue ( XInteger8 ) false ) 
( listing_cfg : URValue ( ListingConfigLRecord ) false ) 
: UExpression ( XAddress # (XHMap XInteger XchgPairListingRequestLRecord ) )%sol true . 

 	 	 refine {{ new 'opt_req_info : ( XMaybe XchgPairListingRequestLRecord ) @ "opt_req_info" := {}(* 
              xchg_pair_listing_requests.extract ( pubkey ) *) ; { _ } }} . 
 	 	 refine {{ require_ ( !{ opt_req_info }  , 1 (* error_code::xchg_pair_not_requested *) ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( XchgPairListingRequestLRecord ) @ "req_info" := 
                          (!{opt_req_info}) -> get_default () ; { _ } }} . 
 	 	 refine {{ new 'pair_data : ( DXchgPairLRecord ) @ "pair_data" :=  
               	 	 [$ tvm.address () ⇒ { DXchgPair_ι_flex_addr_ } ; 
              ( (!{req_info}) ^^  XchgPairListingRequest.tip3_major_root ) ⇒ { DXchgPair_ι_tip3_major_root_ } ; 
              ( (!{req_info}) ^^  XchgPairListingRequest.tip3_minor_root ) ⇒ { DXchgPair_ι_tip3_minor_root_ } ; 
               0 ⇒ { DXchgPair_ι_min_amount_ } ; 
               0 ⇒ { DXchgPair_ι_notify_addr_ }  
               $] ; { _ } }} . 
 	 	 refine {{ state_init : ( StateInitLRecord ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ std_addr : ( XInteger256 ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := prepare_xchg_pair_state_init_and_addr_ ( !{pair_data} , {xchg_pair_code} ) ; { _ } }} . 
 	 	 refine {{ new 'xchg_pair : ( XAddress ) @ "xchg_pair" := {} 
                (* IXchgPairPtr ( Address :: make_std ( !{ workchain_id } , std_addr ) ) *) ; { _ } }} . 
(*  	 	 refine {{ xchg_pair.deploy ( state_init , Grams ( listing_cfg . pair_deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( req_info . min_amount , listing_cfg . pair_keep_balance , req_info . notify_addr ) ; { _ } }} .  *)
 	 	 refine {{ new 'remaining_funds : ( XInteger128 ) @ "remaining_funds" := 
                ( (!{req_info}) ^^ XchgPairListingRequest.client_funds ) - 
                  ( ({listing_cfg}) ^^ ListingConfig.register_pair_cost ) ; { _ } }} . 
(*  	 	 refine {{ IListingAnswerPtr ( req_info . client_addr ) ( Grams ( remaining_funds . get ( ) ) ) . onXchgPairApproved ( pubkey , xchg_pair . get ( ) ) ; { _ } }} .  *)
 	 	 refine {{ return_ [ !{xchg_pair} , { xchg_pair_listing_requests } ] }} . 
 Defined .

 Definition approveXchgPairImpl_right { a1 a2 a3 a4 a5 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( xchg_pair_listing_requests : URValue ( XHMap XInteger256  XchgPairListingRequestLRecord ) a2 ) ( xchg_pair_code : URValue ( XCell ) a3 ) ( workchain_id : URValue ( XInteger8 ) a4 ) ( listing_cfg : URValue ( ListingConfigLRecord ) a5 ) : URValue ( XAddress # (XHMap XInteger XchgPairListingRequestLRecord ) )%sol true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) approveXchgPairImpl 
 pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg ) . 
 
 Notation " 'approveXchgPairImpl_' '(' pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg ')' " := 
 ( approveXchgPairImpl_right 
 pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , xchg_pair_listing_requests custom URValue at level 0 
 , xchg_pair_code custom URValue at level 0 
 , workchain_id custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

 Definition rejectXchgPairImpl 
( pubkey : URValue ( XInteger256 ) false ) 
( xchg_pair_listing_requests : URValue ( XHMap XInteger256 XchgPairListingRequestLRecord ) false ) 
( listing_cfg : URValue ( ListingConfigLRecord ) false ) : 
UExpression ( XHMap XInteger256 XchgPairListingRequestLRecord ) true . 
 	 	 refine {{ new 'opt_req_info : ( XMaybe XchgPairListingRequestLRecord ) @ "opt_req_info" := {} 
           (* xchg_pair_listing_requests.extract (pubkey) *) ; { _ } }} . 
 	 	 refine {{ require_ ( !{ opt_req_info } , 1 (* error_code::xchg_pair_not_requested *) ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( XchgPairListingRequestLRecord ) @ "req_info" := 
                  (!{opt_req_info}) -> get_default () ; { _ } }} . 
 	 	 refine {{ new 'remaining_funds : ( XInteger128 ) @ "remaining_funds" := 
          ( (!{req_info}) ^^ XchgPairListingRequest.client_funds )
                 - ( ({listing_cfg}) ^^ ListingConfig.reject_pair_cost ) ; { _ } }} . 
(*  	 	 refine {{ IListingAnswerPtr( req_info . client_addr ) ( Grams ( remaining_funds . get ( ) ) ) . onXchgPairRejected ( pubkey ) ; { _ } }} .  *)
 	 	 refine {{ return_ { xchg_pair_listing_requests } }} . 
 Defined . 
 
 Definition rejectXchgPairImpl_right { a1 a2 a3 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( xchg_pair_listing_requests : URValue ( XHMap XInteger256  XchgPairListingRequestLRecord ) a2 ) ( listing_cfg : URValue ( ListingConfigLRecord ) a3 ) : URValue ( XHMap XInteger XchgPairListingRequestLRecord) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) rejectXchgPairImpl 
 pubkey xchg_pair_listing_requests listing_cfg ) . 
 
 Notation " 'rejectXchgPairImpl_' '(' pubkey xchg_pair_listing_requests listing_cfg ')' " := 
 ( rejectXchgPairImpl_right 
 pubkey xchg_pair_listing_requests listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , xchg_pair_listing_requests custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope .

 Definition prepare_wrapper_state_init_and_addr 
( wrapper_code : URValue ( XCell ) false ) 
( wrapper_data : URValue ( DWrapperLRecord ) false ) 
: UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 	 	 refine {{ new 'wrapper_data_cl : ( XCell ) @ "wrapper_data_cl" := {} 
              (*  prepare_persistent_data_ ( wrapper_replay_protection_t : : init ( ) , wrapper_data ) *) ; { _ } }} . 
 	 	 refine {{ new 'wrapper_init : ( StateInitLRecord ) @ "wrapper_init" := 

               [$ {} ⇒ { StateInit_ι_split_depth } ; 
                  {} ⇒ { StateInit_ι_special } ;
               ({wrapper_code}) -> set () ⇒ { StateInit_ι_code } ;
               (!{wrapper_data_cl}) -> set () ⇒ { StateInit_ι_data } ;  
                  {} ⇒ { StateInit_ι_library } 
               $]; { _ } }} . 

 	 	 refine {{ new 'wrapper_init_cl : ( XCell ) @ "wrapper_init_cl" := {} (* 
 	 	 refine {{ { wrapper_init_cl } := build ( !{ wrapper_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ wrapper_init } , {} (* tvm_hash ( wrapper_init_cl ) *) ] }} . 
 Defined . 

 Definition prepare_wrapper_state_init_and_addr_right { a1 a2 }  ( wrapper_code : URValue ( XCell ) a1 ) ( wrapper_data : URValue ( DWrapperLRecord ) a2 ) : URValue ( StateInitLRecord # XInteger256 )%sol ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_wrapper_state_init_and_addr 
 wrapper_code wrapper_data ) . 
 
 Notation " 'prepare_wrapper_state_init_and_addr_' '(' wrapper_code , wrapper_data ')' " := 
 ( prepare_wrapper_state_init_and_addr_right 
 wrapper_code wrapper_data ) 
 (in custom URValue at level 0 , wrapper_code custom URValue at level 0 
 , wrapper_data custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_external_wallet_state_init_and_addr 
( name : URValue ( XString ) false ) 
( symbol : URValue ( XString ) false ) 
( decimals : URValue ( XInteger8 ) false ) 
( root_public_key : URValue ( XInteger256 ) false ) 
( wallet_public_key : URValue ( XInteger256 ) false ) 
( root_address : URValue ( XAddress ) false ) 
( owner_address : URValue ( XMaybe XAddress ) false ) 
( code : URValue ( XCell ) false ) 
( workchain_id : URValue ( XInteger8 ) false ) 
: UExpression ( StateInitLRecord # XInteger256 )%sol false .

refine {{ new 'wallet_data : ( DTONTokenWalletExternalLRecord ) @ "wallet_data" := 
                 [$ 
                       {name} ⇒ {DTONTokenWalletExternal_ι_name_ } ; 
                       {symbol} ⇒ {DTONTokenWalletExternal_ι_symbol_ } ;
                       {decimals} ⇒ {DTONTokenWalletExternal_ι_decimals_ } ; 
                        0 ⇒ {DTONTokenWalletExternal_ι_balance_} ; 
                       {root_public_key} ⇒ {DTONTokenWalletExternal_ι_root_public_key_ } ; 
                       {wallet_public_key} ⇒ {DTONTokenWalletExternal_ι_wallet_public_key_ } ; 
                       {root_address} ⇒ {DTONTokenWalletExternal_ι_root_address_ } ; 
                       {owner_address} ⇒ {DTONTokenWalletExternal_ι_owner_address_ } ; 
                       {code} ⇒ {DTONTokenWalletExternal_ι_code_ } ; 
                       {} ⇒ {DTONTokenWalletExternal_ι_allowance_ } ; 
                       {workchain_id} ⇒ {DTONTokenWalletExternal_ι_workchain_id_ } 
                               $] ; { _ } }} . 

 refine {{ new 'wallet_data_cl : ( XCell ) @ "wallet_data_cl" := {} (* 
             prepare_persistent_data ( external_wallet_replay_protection_t : : init ( ) , wallet_data ) *) ; { _ } }} . 
 refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 
               [$ {} ⇒ { StateInit_ι_split_depth } ; 
                  {} ⇒ { StateInit_ι_special } ;
               ({code}) -> set () ⇒ { StateInit_ι_code } ;
               (!{wallet_data_cl}) -> set () ⇒ { StateInit_ι_data } ;  
                  {} ⇒ { StateInit_ι_library } 
               $]; { _ } }} . 

 refine {{ new 'wallet_init_cl : ( XCell ) @ "wallet_init_cl" := {} 
          (*  build ( !{ wallet_init } ) . make_cell ( ) *) ; { _ } }} . 
 refine {{ return_ [ !{ wallet_init } , {} (* tvm_hash ( wallet_init_cl ) *) ] }} . 
 Defined . 

 Definition prepare_external_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XInteger8 ) a3 ) ( root_public_key : URValue ( XInteger256 ) a4 ) ( wallet_public_key : URValue ( XInteger256 ) a5 ) ( root_address : URValue ( XAddress ) a6 ) ( owner_address : URValue ( XMaybe XAddress ) a7 ) ( code : URValue ( XCell ) a8 ) ( workchain_id : URValue ( XInteger8 ) a9 ) : URValue ( StateInitLRecord # XInteger256 )%sol ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_external_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_external_wallet_state_init_and_addr_' '(' name , symbol , decimals , root_public_key , wallet_public_key , root_address , owner_address , code , workchain_id ')' " := 
 ( prepare_external_wallet_state_init_and_addr_right 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 
 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 
 , root_public_key custom URValue at level 0 
 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , code custom URValue at level 0 
 , workchain_id custom URValue at level 0 ) : ursus_scope . 

 Definition approveWrapperImpl 
( pubkey : URValue ( XInteger256 ) false ) 
( wrapper_listing_requests : URValue ( XHMap XInteger256  WrapperListingRequestLRecord ) false ) 
( wrapper_code : URValue ( XCell ) false ) 
( ext_wallet_code : URValue ( XCell ) false ) 
( flex_wallet_code : URValue ( XCell ) false ) 
( workchain_id : URValue ( XInteger8 ) false ) 
( listing_cfg : URValue ( ListingConfigLRecord ) false ) 
: UExpression ( XAddress # (XHMap XInteger256 WrapperListingRequestLRecord) )%sol true . 

 refine {{ new 'opt_req_info : ( XMaybe WrapperListingRequestLRecord ) @ "opt_req_info" := {}
       (* wrapper_listing_requests.extract ( pubkey ^^ XInteger256:get ( ) ) *) ; { _ } }} . 
 refine {{ require_ ( !{ opt_req_info }  , 1 (* error_code::wrapper_not_requested *) ) ; { _ } }} . 
 refine {{ new 'req_info : ( WrapperListingRequestLRecord ) @ "req_info" := 
               (!{opt_req_info}) -> get_default () ; { _ } }} . 
 refine {{ new 'tip3cfg : ( Tip3ConfigLRecord ) @ "tip3cfg" := 
                 (!{req_info}) ^^ WrapperListingRequest.tip3cfg ; { _ } }} .
 refine {{ new 'wrapper_data : ( DWrapperLRecord ) @ "wrapper_data" :=  
               	 [$ ( (!{ tip3cfg }) ^^ Tip3Config.name ) ⇒ { DWrapper_ι_name_ } ; 
               ( (!{ tip3cfg }) ^^ Tip3Config.symbol ) ⇒ { DWrapper_ι_symbol_ } ; 
               ( (!{ tip3cfg }) ^^ Tip3Config.decimals ) ⇒ { DWrapper_ι_decimals_ } ; 
               { workchain_id } ⇒ { DWrapper_ι_workchain_id_ } ; 
               { pubkey } ⇒ { DWrapper_ι_root_public_key_ } ; 
               {} ⇒ { DWrapper_ι_total_granted_ } ; 
               {} ⇒ { DWrapper_ι_internal_wallet_code_ } ; 
              ( ( tvm.address () ) -> set () )  ⇒ { DWrapper_ι_owner_address_ } ; 
               ( {listing_cfg} ^^ ListingConfig.wrapper_keep_balance ) ⇒ { DWrapper_ι_start_balance_ } ; 
               {} ⇒ { DWrapper_ι_external_wallet_ }  
               $] ; { _ } }} . 
 	 	 refine {{ wrapper_init : ( StateInitLRecord ) @ "wrapper_init" ; { _ } }} . 
 	 	 refine {{ wrapper_hash_addr : ( XInteger256 ) @ "wrapper_hash_addr" ; { _ } }} . 
 	 	 refine {{ [ { wrapper_init } , { wrapper_hash_addr } ] := 
               prepare_wrapper_state_init_and_addr_ ( {wrapper_code} , !{wrapper_data} ) ; { _ } }} . 
 refine {{ new 'wrapper_addr : XAddress @ "wrapper_addr" := {} ; { _ } }} .
(*  	 	 refine {{ IWrapperPtr wrapper_addr ( address : : make_std ( workchain_id , wrapper_hash_addr ) ) ; { _ } }} .  *)
 	 	 refine {{ wallet_init : ( StateInitLRecord ) @ "wallet_init" ; { _ } }} . 
 	 	 refine {{ wallet_hash_addr : ( XInteger256 ) @ "wallet_hash_addr" ; { _ } }} . 
 	 	 refine {{ [ { wallet_init } , { wallet_hash_addr } ] := 
       prepare_external_wallet_state_init_and_addr_ 
           ( (!{ tip3cfg }) ^^ Tip3Config.name , 
             (!{ tip3cfg }) ^^ Tip3Config.symbol , 
             (!{ tip3cfg }) ^^ Tip3Config.decimals , 
             (!{ tip3cfg }) ^^ Tip3Config.root_public_key , 
              {pubkey} , 
             (!{ tip3cfg }) ^^ Tip3Config.root_address , 
             (!{wrapper_addr}) -> set () , 
              {ext_wallet_code} , 
              {workchain_id} ) ; { _ } }} . 
 refine {{ new 'wallet_addr : XAddress @ "wallet_addr" := {} ; { _ } }} .
(*  	 	 refine {{ ITONTokenWalletPtr wallet_addr ( address : : make_std ( workchain_id , wallet_hash_addr ) ) ; { _ } }} .  *)
(*  	 	 refine {{ wallet_addr.deploy_noop ( wallet_init , Grams ( listing_cfg . ext_wallet_balance . get ( ) ) ) ; { _ } }} . 
 	 	 refine {{ wrapper_addr.deploy ( wrapper_init , Grams ( listing_cfg . wrapper_deploy_value . get ( ) ) ) . init ( wallet_addr . get ( ) ) ; { _ } }} . 
 	 	 refine {{ wrapper_addr ( Grams ( listing_cfg . set_internal_wallet_value . get ( ) ) ) . setInternalWalletCode ( flex_wallet_code ) ; { _ } }} . 
 *) 	 	 refine {{ return_ [ !{wrapper_addr} , { wrapper_listing_requests } ] }} . 
 Defined .

 Definition approveWrapperImpl_right { a1 a2 a3 a4 a5 a6 a7 }  
( pubkey : URValue ( XInteger256 ) a1 ) 
( wrapper_listing_requests : URValue ( XHMap XInteger256  WrapperListingRequestLRecord ) a2 )
( wrapper_code : URValue ( XCell ) a3 ) 
( ext_wallet_code : URValue ( XCell ) a4 ) 
( flex_wallet_code : URValue ( XCell ) a5 )
 ( workchain_id : URValue ( XInteger8 ) a6 ) 
( listing_cfg : URValue ( ListingConfigLRecord ) a7 ) 
: URValue ( XAddress # (XHMap XInteger256 WrapperListingRequestLRecord) )%sol true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) approveWrapperImpl 
 pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg ) . 
 
 Notation " 'approveWrapperImpl_' '(' pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg ')' " := 
 ( approveWrapperImpl_right 
 pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , wrapper_listing_requests custom URValue at level 0 
 , wrapper_code custom URValue at level 0 
 , ext_wallet_code custom URValue at level 0 
 , flex_wallet_code custom URValue at level 0 
 , workchain_id custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

Definition rejectWrapperImpl 
( pubkey : URValue ( XInteger256 ) false ) 
( wrapper_listing_requests : URValue (XInteger256 # WrapperListingRequestLRecord)%sol false ) 
( listing_cfg : URValue ( ListingConfigLRecord ) false ) 
: UExpression (XInteger256 # WrapperListingRequestLRecord)%sol true . 

 	 	 refine {{ new 'opt_req_info : ( XMaybe WrapperListingRequestLRecord ) @ "opt_req_info" := {} 
        (* wrapper_listing_requests.extract ( pubkey ) *) ; { _ } }} . 
 	 	 refine {{ require_ ( !{ opt_req_info } , 1 (* error_code::wrapper_not_requested *) ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( WrapperListingRequestLRecord ) @ "req_info" := 
                             (!{opt_req_info}) -> get_default () ; { _ } }} . 
 	 	 refine {{ new 'remaining_funds : ( XInteger128 ) @ "remaining_funds" := 
              ( (!{req_info}) ^^ WrapperListingRequest.client_funds ) - 
                ( {listing_cfg} ^^ ListingConfig.reject_wrapper_cost ) ; { _ } }} . 
(*  	 	 refine {{ IListingAnswerPtr( req_info . client_addr ) ( Grams ( remaining_funds . get ( ) ) ) . onWrapperRejected ( pubkey ) ; { _ } }} .  *)
 	 	 refine {{ return_ { wrapper_listing_requests } }} . 
 Defined .

 Definition approveTradingPair ( pubkey : URValue ( XInteger256 ) false ) : UExpression XAddress false . 
(*  	 	 refine {{ check_owner ( ) ; { _ } }} .  *)
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {} ; { _ } }} . 
 	 	 refine {{ new 'new_trading_pair_listing_requests : 
         ( XHMap XInteger256 TradingPairListingRequestLRecord ) @ "new_trading_pair_listing_requests" := {} ; { _ } }} . 
 	 	 refine {{ [ { trade_pair } , { new_trading_pair_listing_requests } ] := 
            approveTradingPairImpl_ ( {pubkey} , _trading_pair_listing_requests_ , _pair_code_ -> get_default () , _workchain_id_ , _listing_cfg_ ) ; { _ } }} . 

 	 	 refine {{ trading_pair_listing_requests_ := new_trading_pair_listing_requests ; { _ } }} . 
 	 	 refine {{ if ( Internal ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { auto value_gr = int_value ( ) ; { _ } }} . 
 	 	 	 refine {{ tvm_rawreserve ( tvm_balance ( ) - value_gr ( ) , rawreserve_flag : : up_to ) ; { _ } }} . 
 	 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) }} . 
 	 refine {{ return_ !{ trade_pair } ; { _ } }} . 
 
 Defined . 

End FuncsInternal.
End Funcs.








