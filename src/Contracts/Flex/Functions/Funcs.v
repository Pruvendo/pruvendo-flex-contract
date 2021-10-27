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


(* Set Typeclasses Debug.
Check || 1 ||.
About IfElseExpression.
Arguments IfElseExpression {_} {_} {_} {_} {_} {_} {_} {_} {R} (* & {_} *) {B} {bb} {xb} {yb} & {_} {_} _ _ _ .
Set Typeclasses Iterative Deepening.
Check {{  if m_value then { {_: UEf} } else { {_: UEf} } }}. 

About IfElseExpression. *)

Definition constructor 
( deployer_pubkey : URValue XInteger256 false) 
( ownership_description : URValue XString false ) 
( owner_address : URValue ( XMaybe XAddress ) false ) 
( transfer_tip3 : URValue ( XInteger128) false  ) 
( return_ownership : URValue ( XInteger128) false  ) 
( trading_pair_deploy : URValue ( XInteger128) false  ) 
( order_answer : URValue ( XInteger128) false  ) 
( process_queue : URValue ( XInteger128) false  ) 
( send_notify : URValue ( XInteger128) false  ) 
( deals_limit : URValue ( XInteger8) false  ) : UExpression PhantomType false . 
 	 	 refine {{ _deployer_pubkey_ := { deployer_pubkey } ; { _ } }} . 
 	 	 refine {{ _ownership_description_ := { ownership_description } ; { _ } }} . 
 	 	 refine {{ _owner_address_ := { owner_address } ; { _ } }} . 
 	 	 refine {{ _deals_limit_ := { deals_limit } ; { _ } }} . 
 	 	 refine {{ _tons_cfg_ := [$ 
                 { transfer_tip3 } ⇒ {TonsConfig_ι_transfer_tip3} ; 
              { return_ownership } ⇒ {TonsConfig_ι_return_ownership} ;  
           { trading_pair_deploy } ⇒ {TonsConfig_ι_trading_pair_deploy} ;  
                  { order_answer } ⇒ {TonsConfig_ι_order_answer} ; 
                 { process_queue } ⇒ {TonsConfig_ι_process_queue} ;  
                   { send_notify } ⇒ {TonsConfig_ι_send_notify} 
                             $] 
      }} . 
 Defined . 

 Definition setPairCode ( code : URValue XCell false ) : UExpression PhantomType true . 
  	 refine {{ require_ ( ( ~ _pair_code_ ) , error_code::cant_override_code ) ; { _ } }} .
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) ,error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ require_ ( ( {code} -> to_slice () ) -> refs () == #{2} , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ _pair_code_ := {} (* builder ( ) . stslice ( code . ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 

 Definition setXchgPairCode ( code : URValue XCell false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _xchg_pair_code_ ) , error_code::cant_override_code ) ; { _ } }} .
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ require_ ( ( ( {code} -> to_slice () ) -> refs () == #{2} ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ _xchg_pair_code_ := {} (* builder ( ) . stslice ( code . ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 

 Definition setPriceCode ( code : URValue XCell false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _price_code_ ) , error_code::cant_override_code ) ; { _ } }} .
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _price_code_ ->set ( { code } ) }} . 
 Defined .

 Definition setXchgPriceCode ( code : URValue XCell false ) : UExpression PhantomType true . 
	 	 refine {{ require_ ( ( ~ _xchg_price_code_ ) ,  error_code::cant_override_code  ) ; { _ } }} .
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) ,  error_code::sender_is_not_deployer  ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _xchg_price_code_ ->set ( { code } ) }} . 
 Defined . 

 Definition transfer_INTERNAL ( tto : URValue XAddress false ) ( tons : URValue XInteger128 false ) : UExpression PhantomType true . 
 	 	 refine {{ new 'internal_ownership : ( XBool ) @ "internal_ownership" := {} ; { _ } }} . 
 	 	 refine {{ { internal_ownership } := {} (* !! _owner_address_ *)  ; { _ } }} . 
 	 	 refine {{ require_ ( ( !{ internal_ownership } && ( {} (* int.sender () *) ==  _owner_address_ -> get_default () ) ) , error_code::message_sender_is_not_my_owner ) ;{ _ } }} . 
 	 	 refine {{ tvm.accept () (* ; { _ } }} . 
 	 	 refine {{ tvm.transfer ( !{tto} , !{tons} , TRUE ) *) }} . 
 Defined . 

 Definition transfer_EXTERNAL ( tto : URValue XAddress false ) ( tons : URValue XInteger128 false ) : UExpression PhantomType true . 
 	 	 refine {{ new 'internal_ownership : ( XBool ) @ "internal_ownership" := {} ; { _ } }} . 
 	 	 refine {{ { internal_ownership } := {} (* !! _owner_address_ *)  ; { _ } }} . 
 	 	 refine {{ require_ ( ( ( ~ !{ internal_ownership } ) && (msg.pubkey () == _deployer_pubkey_ ) ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () (* ; { _ } }} . 
 	 	 refine {{ tvm.transfer ( to , tons . get ( ) , true )  *) }} . 
 Defined . 

 Definition isFullyInitialized : UExpression XBool false . 
 	 	 refine {{ return_ {} (*  _pair_code_ && _price_code_ && _xchg_pair_code_ && _xchg_price_code_ *) }} . 
 Defined . 

 Definition getTonsCfg : UExpression TonsConfigLRecord false . 
 	 	 refine {{ return_ _tons_cfg_ }} . 
 Defined . 

 Definition getTradingPairCode : UExpression XCell false . 
 	 	 refine {{ return_ _pair_code_ ->get_default () }} . 
 Defined .

 Definition getXchgPairCode : UExpression XCell false . 
 	 	 refine {{ return_ _xchg_pair_code_ ->get_default () }} . 
 Defined . 

 Definition getSellPriceCode ( tip3_addr : URValue XAddress false ) : UExpression XCell true . 
 	 	 refine {{ require_ ( ( ( ( ( _price_code_ -> get_default () )  -> to_slice () ) -> refs () ) == #{2} ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ new 'salt : ( XCell ) @ "salt" := {} ; { _ } }} . 
 	 	 refine {{ { salt } := {} (* builder ( ) . stslice ( tvm_myaddr ( ) ) . stslice ( tip3_addr . sl ( ) ) . endc ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ {} (* builder ( ) . stslice ( price_code_ - > ctos ( ) ) . stref ( !{ salt } ) . endc ( ) *) }} . 
 Defined . 
 
 Definition getXchgPriceCode ( tip3_addr1 : URValue XAddress false ) ( tip3_addr2 : URValue XAddress false ) : UExpression XCell true . 
 	 	 refine {{ require_ ( ( ( ( ( _price_code_ -> get_default () )  -> to_slice () ) -> refs () ) == #{2} ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ new 'keys : ( XAddress # XAddress )%sol @ "keys" := {} ; { _ } }} . 
 	 	 refine {{ { keys } := [ { tip3_addr1 } , { tip3_addr2 } ] ; { _ } }} . 
 	 	 refine {{ return_ {} (* builder ( ) . stslice ( xchg_price_code_ - > ctos ( ) ) . stref ( build ( !{ keys } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 
 
 Definition getSellTradingPair ( tip3_root : URValue XAddress false ) : UExpression XAddress false . 
 	 	 refine {{ new 'myaddr : ( XAddress ) @ "myaddr" := {} ; { _ } }} . 
 	 	 refine {{ { myaddr } := tvm.address () ; { _ } }} . 
 	 	 refine {{ new 'pair_data : ( DTradingPairLRecord ) @ "pair_data" := {} ; { _ } }} . 
 	 	refine {{ { pair_data } :=
                      [$ !{ myaddr } ⇒ { DTradingPair_ι_flex_addr_ } ; 
                       { tip3_root } ⇒ { DTradingPair_ι_tip3_root_ } ; 
                                   0 ⇒ { DTradingPair_ι_min_amount_ } ; 
                                  0  ⇒ { DTradingPair_ι_notify_addr_ } 
                $] ; { _ } }} .
 	 	 refine {{ new 'std_addr : ( StateInitLRecord ) @ "std_addr" := {} ; { _ } }} . 
 	 	 refine {{ { std_addr } := {} (* prepare_trading_pair_state_init_and_addr ( !{ pair_data } , *pair_code_ ) . second *) ; { _ } }} . 
 	 	 refine {{ new 'workchain_id : ( addr_stdLRecord ) @ "workchain_id" := {} ; { _ } }} . 
 	 	 refine {{ { workchain_id } := {} (* std :: get < addr_std > ( myaddr . val ( ) ) . workchain_id *) ; { _ } }} . 
 	 	 refine {{ return_ {} (* address :: make_std ( !{ workchain_id } , !{ std_addr } ) *) }} . 
 Defined . 
 
 Definition getXchgTradingPair ( tip3_major_root : URValue XAddress false ) ( tip3_minor_root : URValue XAddress false ) : UExpression XAddress false . 
 	 	 refine {{ new 'myaddr : ( XAddress ) @ "myaddr" := {} ; { _ } }} . 
 	 	 refine {{ { myaddr } := tvm.address () ; { _ } }} . 
 	 	 refine {{ new 'pair_data : ( DXchgPairLRecord ) @ "pair_data" := {} ; { _ } }} .
     refine {{ {pair_data} := 
                       [$  !{ myaddr } ⇒ { DXchgPair_ι_flex_addr_ } ;
                   { tip3_major_root } ⇒ { DXchgPair_ι_tip3_major_root_ } ; 
                   { tip3_minor_root } ⇒ { DXchgPair_ι_tip3_minor_root_ } ; 
                                     0 ⇒ { DXchgPair_ι_min_amount_ } ; 
                                     0 ⇒ { DXchgPair_ι_notify_addr_ }  
               $] ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( StateInitLRecord ) @ "std_addr" := {} ; { _ } }} . 
 	 	 refine {{ { std_addr } := {} (* prepare_xchg_pair_state_init_and_addr ( !{ pair_data } , *xchg_pair_code_ ) . second *) ; { _ } }} . 
 	 	 refine {{ new 'workchain_id : ( addr_stdLRecord ) @ "workchain_id" := {} ; { _ } }} . 
 	 	 refine {{ { workchain_id } := {} (* std :: get < addr_std > ( myaddr . val ( ) ) . workchain_id *) ; { _ } }} . 
 	 	 refine {{ return_ {} (* address :: make_std ( !{ workchain_id } , !{ std_addr } ) *) }} . 
 Defined . 

 Definition getDealsLimit : UExpression XInteger8 false . 
 	 	 refine {{ return_ _deals_limit_ }} . 
 Defined .

 Definition getOwnershipInfo : UExpression FlexOwnershipInfoLRecord false . 
 	 	 refine {{ return_ [$ _deployer_pubkey_  ⇒ {FlexOwnershipInfo_ι_deployer_pubkey} ; 
                          _ownership_description_  ⇒ {FlexOwnershipInfo_ι_ownership_description} ; 
                          _owner_address_  ⇒ {FlexOwnershipInfo_ι_owner_contract} $] }} . 
 Defined . 
 
 Definition _fallback ( msg : URValue XCell false ) ( msg_body : URValue XSlice false ) : UExpression XInteger false . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 Definition prepare_flex_state_init_and_addr ( flex_data : URValue ContractLRecord false ) 
                                             ( flex_code : URValue XCell false ) 
: UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 	 	 refine {{ flex_data : ( ContractLRecord ) @ "flex_data" ; { _ } }} . 
 	 	 refine {{ flex_code : ( XCell ) @ "flex_code" ; { _ } }} . 
 	 	 refine {{ new 'flex_data_cl : ( XCell ) @ "flex_data_cl" := {} ; { _ } }} . 
 	 	 refine {{ { flex_data_cl } := {} (* prepare_persistent_data ( flex_replay_protection_t : : init ( ) , flex_data ) *) ; { _ } }} . 
 	 	 refine {{ new 'flex_init : ( StateInitLRecord ) @ "flex_init" := {} ; { _ } }} . 
 	 	 refine {{ { flex_init } := [$ {} ⇒ {StateInit_ι_split_depth} ; 
                                   {} ⇒ {StateInit_ι_special} ;
                            (!{flex_code}) -> set ()  ⇒ {StateInit_ι_code} ; 
                         ( !{flex_data_cl}) -> set () ⇒ {StateInit_ι_data} ;
                                   {} ⇒ {StateInit_ι_library} $] ; { _ } }} . 	 	 
     refine {{ new 'flex_init_cl : ( XCell ) @ "flex_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ { flex_init_cl } := {} (* build ( !{ flex_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ flex_init } , {} (* tvm.hash ( !{ flex_init_cl } ) *) ] }} . 
 Defined . 


End FuncsInternal.
End Funcs.








