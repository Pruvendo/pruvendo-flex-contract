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

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import CommonNotations.
Require Import Project.CommonConstSig.
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.XchgPair.Ledger.
Require Import Contracts.XchgPair.Functions.FuncSig.
Require Import Contracts.XchgPair.Functions.FuncNotations.
Require Contracts.XchgPair.Interface.

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

Module Type Has_Internal.

Parameter Internal: bool .

End Has_Internal.

Module Funcs (ha : Has_Internal)(dc : ConstsTypesSig XTypesModule StateMonadModule) .

Import ha.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

Export SpecModuleForFuncNotations(* ForFuncs *).CommonNotationsModule.

Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
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

Existing Instance xbool_default.

Parameter int_value__ : URValue uint false .
Notation " 'int_value' '(' ')' " := 
 ( int_value__ ) 
 (in custom URValue at level 0 ) : ursus_scope .

Parameter set_int_return_flag :UExpression XBool false .
Notation " 'set_int_return_flag_' '(' ')' " := 
 ( set_int_return_flag ) 
 (in custom ULValue at level 0 ) : ursus_scope . 

Definition onDeploy 
( min_amount : ( uint128 ) ) 
( deploy_value : ( uint128 ) ) 
( notify_addr : ( XAddress ) ) 
: UExpression XBool true . 
 	 	 refine {{ require_ ( ( ( int_value ( ) ) > #{ deploy_value } ) , 1 (* error_code::not_enough_tons *) ) ; { _ } }} . 
(*  	 	 refine {{ require_ ( ( _min_amount_ ) , 1 (* error_code::double_deploy *) ) ; { _ } }} .  *)
 	 	 refine {{ require_ ( ( #{ min_amount } ) > 0  , 1 (* error_code::zero_min_amount *) ) ; { _ } }} . 
 	 	 refine {{ _min_amount_ := #{ min_amount } ; { _ } }} . 
 	 	 refine {{ _notify_addr_ := #{ notify_addr } ; { _ } }} . 
(*  	 	 refine {{ tvm.rawreserve ( #{deploy_value} , 1 (* rawreserve_flag::up_to *) ) ; { _ } }} .  *)
 	 	 refine {{ set_int_return_flag_ ( ) (* SEND_ALL_GAS *) ; { _ } }} . 
 	 	 refine {{ return_ TRUE  }} . 
 Defined . 
 
 
 
 
 Definition getFlexAddr : UExpression XAddress false . 
 	 	 refine {{ return_ _flex_addr_  }} . 
 Defined . 
 
 
 
 
 Definition getTip3MajorRoot : UExpression XAddress false . 
 	 	 refine {{ return_ _tip3_major_root_  }} . 
 Defined . 
 
 
 
 
 Definition getTip3MinorRoot : UExpression XAddress false . 
 	 	 refine {{ return_ _tip3_minor_root_ }} . 
 Defined . 
 
 
 
 
 Definition getMinAmount : UExpression uint128 false . 
 	 	 refine {{ return_ _min_amount_ }} . 
 Defined . 
 
 
 
 
 Definition getNotifyAddr : UExpression XAddress false . 
 	 	 refine {{ return_ _notify_addr_ }} . 
 Defined . 
 
 
 
 
 Definition _fallback ( msg : ( XCell ) ) ( msg_body : ( XSlice ) ) : UExpression uint false . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
Definition prepare_persistent_data { X Y } (persistent_data_header : X) 
                                           (base : Y): UExpression XCell false .
 refine {{ return_ {} }} .  
Defined .

Definition prepare_persistent_data_right { X Y a1 a2 }  
                                    ( persistent_data_header : URValue ( X ) a1 ) 
                                    ( base : URValue ( Y ) a2 ) 
               : URValue ( XCell ) (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args ( LedgerableWithArgs:= λ2 ) prepare_persistent_data 
persistent_data_header base ) . 
 
 Notation " 'prepare_persistent_data_' '(' a ',' b ')' " := 
 ( prepare_persistent_data_right 
 a b ) 
 (in custom URValue at level 0 , 
   a custom URValue at level 0 
 , b custom URValue at level 0 ) : ursus_scope . 

 
 
 Definition prepare_xchg_pair_state_init_and_addr ( pair_data : ( ContractLRecord ) ) ( pair_code : ( XCell ) ) : UExpression ( StateInitLRecord # uint256 ) false . 
 	 	 refine {{ new 'pair_data_cl : ( XCell ) @ "pair_data_cl" := 
                    prepare_persistent_data_ ( {} , #{pair_data} ) ; { _ } }} . 
 	 	 refine {{ new 'pair_init : ( StateInitLRecord ) @ "pair_init" := 
                        [ {} , {} , (#{pair_code}) -> set () , (!{pair_data_cl}) -> set () , {} ] ; { _ } }} . 
 	 	 refine {{ new 'pair_init_cl : ( XCell ) @ "pair_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ {pair_init_cl} := {} (* build ( !{pair_init} ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ pair_init } , {} (* tvm.hash ( !{pair_init_cl} ) *) ] }} . 
 Defined . 

 
End FuncsInternal.
End Funcs.


