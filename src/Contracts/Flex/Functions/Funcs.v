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
Set Typeclasses Depth 10.


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
 
(*  Definition approveTradingPairImpl ( pubkey : URValue ( XInteger256 ) false ) 
( trading_pair_listing_requests : URValue ( XHMap XInteger256 TradingPairListingRequestLRecord ) false ) ( pair_code : URValue ( XCell ) false ) ( workchain_id : URValue ( XInteger8 ) false ) ( listing_cfg : URValue ( ListingConfigLRecord ) false ) : UExpression ( XHMap XInteger TradingPairListingRequestLRecord ) true . 
 	 	 refine {{ new 'opt_req_info : ( XMaybe TradingPairListingRequestLRecord ) @ "opt_req_info" := {} ; { _ } }} . 
 	 	                     (* trading_pair_listing_requests.extract ( pubkey.get ( ) ) *)  
 	 	 refine {{ require_ ( { opt_req_info }  , 1 (* error_code::trading_pair_not_requested *) ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( auto ) @ "req_info" := {} ; { _ } }} . 
 	 	 refine {{ { req_info } := *opt_req_info ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := prepare_trading_pair ( address { tvm_myaddr ( ) } , req_info . tip3_root , pair_code ) ; { _ } }} . 
 	 	 refine {{ new 'trade_pair : ( auto ) @ "trade_pair" := {} ; { _ } }} . 
 	 	 refine {{ { trade_pair } := ITradingPairPtr ( Address :: make_std ( !{ workchain_id } , std_addr ) ) ; { _ } }} . 
 	 	 refine {{ trade_pair ^^ auto:deploy ( state_init , Grams ( listing_cfg . pair_deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( req_info . min_amount , listing_cfg . pair_keep_balance , req_info . notify_addr ) ; { _ } }} . 
 	 	 refine {{ new 'remaining_funds : ( auto ) @ "remaining_funds" := {} ; { _ } }} . 
 	 	 refine {{ { remaining_funds } := req_info ^^ auto:client_funds - listing_cfg ^^ ListingConfigLRecord:register_pair_cost ; { _ } }} . 
 	 	 refine {{ address ( * IListingAnswerPtr * ) ( req_info . client_addr ) ( Grams ( remaining_funds . get ( ) ) ) . onTradingPairApproved ( pubkey , trade_pair . get ( ) ) ; { _ } }} . 
 	 	 refine {{ return_ [ trade_pair ^^ auto:get ( ) , !{ trading_pair_listing_requests } ] ; { _ } }} . 
 Defined . 
 




 Definition approveTradingPair ( pubkey : URValue ( XInteger256 ) false ) : UExpression XAddress false . 
(*  	 	 refine {{ check_owner ( ) ; { _ } }} .  *)
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ trade_pair : ( auto ) @ "trade_pair" ; { _ } }} . 
 	 	 refine {{ new_trading_pair_listing_requests : ( auto ) @ "new_trading_pair_listing_requests" ; { _ } }} . 
 	 	 refine {{ [ { trade_pair } , { new_trading_pair_listing_requests } ] := approveTradingPairImpl ( pubkey , trading_pair_listing_requests_ , pair_code_ . get ( ) , workchain_id_ , listing_cfg_ ) ; { _ } }} . 
 	 	 refine {{ trading_pair_listing_requests_ := new_trading_pair_listing_requests ; { _ } }} . 
 	 	 refine {{ if ( Internal ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { auto value_gr = int_value ( ) ; { _ } }} . 
 	 	 	 refine {{ tvm_rawreserve ( tvm_balance ( ) - value_gr ( ) , rawreserve_flag : : up_to ) ; { _ } }} . 
 	 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) }} . 
 	 refine {{ return_ !{ trade_pair } ; { _ } }} . 
 
 Defined . 
 *)





















End FuncsInternal.
End Funcs.








