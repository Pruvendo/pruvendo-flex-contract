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

Require Import Project.CommonConstSig.
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.Wrapper.Ledger.
Require Import Contracts.Wrapper.Functions.FuncSig.
Require Import Contracts.Wrapper.Functions.FuncNotations.
Require Contracts.Wrapper.Interface.

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

Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.

(* Existing Instance xbool_default. *)

  (* StateInit getStateInit(const message<anyval> &msg) {
    if (msg.init->isa<ref<StateInit>>()) {
      return_ msg.init->get<ref<StateInit>>()();
    } else {
      return_ msg.init->get<StateInit>();
    }
  } *)
Definition getStateInit ( msg : ULValue message<anyval> ) : UExpression StateInitLRecord FALSE . 
 	 	 	 refine {{ if ( msg_init - > isa < ref < StateInit > > () ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ return_ msg_init - > get < ref < StateInit > > () () }} . 
 	     refine {{ return_ msg_init - > get < StateInit > () }} . 
Defined . 
 
 
 
 
 Definition init ( external_wallet : ( XAddress ) ) : UExpression XBool TRUE . 
 	 	 	 refine {{ require_ ( ( ~ _external_wallet_ ) , error_code::cant_override_external_wallet ) ; _ }} . 
 	 	 refine {{ new 'parsed_msg : ( auto ) @ "parsed_msg" := {} ; _ }} . 
 	 	 refine {{ { parsed_msg } := parse ( parser ( msg_slice () ) , error_code::bad_incoming_msg ) ; _ }} . 
 	 	 refine {{ require_ ( ( ~ ~ parsed_msg_init ) , error_code::bad_incoming_msg ) ; _ }} . 
 	 	 refine {{ new 'init : ( auto ) @ "init" := {} ; _ }} . 
 	 	 refine {{ init_ := getStateInit_ ( (!{ parsed_msg }) ) ; _ }} . 
 	 	 refine {{ require_ ( ( ~ ~ init_ ^^ auto:code ) , error_code::bad_incoming_msg ) ; _ }} . 
 	 	 refine {{ new 'mycode : ( auto ) @ "mycode" := {} ; _ }} . 
 	 	 refine {{ { mycode } := *init ^^ code ; _ }} . 
 	 	 refine {{ require_ ( ( (!{ mycode }) ^^ auto:ctos () . srefs () == 3 ) , error_code::unexpected_refs_count_in_code ) ; _ }} . 
 	 	 refine {{ parser mycode_parser ( (!{ mycode }) . ctos () ) ; _ }} . 
 	 	 refine {{ mycode_parser ^^ ldref () ; _ }} . 
 	 	 refine {{ mycode_parser ^^ ldref () ; _ }} . 
 	 	 refine {{ new 'mycode_salt : ( auto ) @ "mycode_salt" := {} ; _ }} . 
 	 	 refine {{ { mycode_salt } := mycode_parser ^^ ldrefrtos () ; _ }} . 
 	 	 refine {{ new 'flex_addr : ( auto ) @ "flex_addr" := {} ; _ }} . 
 	 	 refine {{ { flex_addr } := parse ( (!{ mycode_salt }) ) ; _ }} . 
 	 	 refine {{ require_ ( ( (!{ flex_addr }) == int_sender () ) , error_code::only_flex_may_deploy_me ) ; _ }} . 
 	 	 refine {{ _external_wallet_ := (#{ external_wallet }) ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( _start_balance_ . get () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ return_ bool_t TRUE }} . 
 Defined . 
 
 
 
 
 Definition setInternalWalletCode ( wallet_code : ( XCell ) ) : UExpression XBool TRUE . 
 	 	 	 refine {{ check_owner_ () ; _ }} . 
 	 	 refine {{ tvm.accept () ; _ }} . 
 	 	 refine {{ require_ ( ( ~ _internal_wallet_code_ ) , error_code::cant_override_wallet_code ) ; _ }} . 
 	 	 refine {{ _internal_wallet_code_ := (#{ wallet_code }) ; _ }} . 
 	 	 refine {{ if ( Internal ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ { auto value_gr = int_value () ; _ }} . 
 	 	 	 refine {{ tvm.rawreserve ( tvm.balance () - value_gr () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) }} . 
 	 refine {{ return_ bool_t TRUE ; _ }} . 
 
 Defined . 
 
 
 
 
 Definition deployEmptyWallet ( pubkey : ( XInteger256 ) ) ( internal_owner : ( XAddress ) ) ( grams : ( XInteger128 ) ) : UExpression XAddress FALSE . 
 	 	 	 refine {{ new 'value_gr : ( auto ) @ "value_gr" := {} ; _ }} . 
 	 	 refine {{ { value_gr } := int_value () ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
 	 	 refine {{ dest : ( auto ) @ "dest" ; _ }} . 
 	 	 refine {{ [ wallet_init , dest ] := calc_internal_wallet_init_ ( (#{ pubkey }) , (#{ internal_owner }) ) ; _ }} . 
 	 	 refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; _ }} . 
 	 	 refine {{ dest_handle ^^ deploy_noop ( wallet_init , Grams ( (#{ grams }) . get () ) ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ return_ dest }} . 
 Defined . 
 
 
 
 
 Definition onTip3Transfer ( answer_addr : ( XAddress ) ) ( balance : ( XInteger128 ) ) ( new_tokens : ( XInteger128 ) ) ( sender_pubkey : ( XInteger256 ) ) ( sender_owner : ( XAddress ) ) ( payload : ( XCell ) ) : UExpression WrapperRetLRecord TRUE . 
 	 	 	 refine {{ require_ ( ( int_sender () == _external_wallet_ - > get () ) , error_code::not_my_wallet_notifies ) ; _ }} . 
 	 	 refine {{ set_int_sender ( (#{ answer_addr }) ) ; _ }} . 
 	 	 refine {{ set_int_return_value ( 0 ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ new 'args : ( auto ) @ "args" := {} ; _ }} . 
 	 	 refine {{ { args } := parse ( (#{ payload }) . ctos () ) ; _ }} . 
 	 	 refine {{ new 'value_gr : ( auto ) @ "value_gr" := {} ; _ }} . 
 	 	 refine {{ { value_gr } := int_value () ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
 	 	 refine {{ dest : ( auto ) @ "dest" ; _ }} . 
 	 	 refine {{ [ wallet_init , dest ] := calc_internal_wallet_init_ ( (!{ args }) . pubkey , (!{ args }) . internal_owner ) ; _ }} . 
 	 	 refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; _ }} . 
 	 	 refine {{ dest_handle ^^ deploy ( wallet_init , Grams ( (!{ args }) . grams . get () ) ) . accept ( (#{ new_tokens }) , int_sender () , (!{ args }) . grams ) ; _ }} . 
 	 	 refine {{ _total_granted_ += (#{ new_tokens }) ; _ }} . 
 	 	 refine {{ return_ [ 0 , dest_handle ^^ get () ] }} . 
 Defined . 
 
 
 
 
 Definition burn ( answer_addr : ( XAddress ) ) ( sender_pubkey : ( XInteger256 ) ) ( sender_owner : ( XAddress ) ) ( out_pubkey : ( XInteger256 ) ) ( out_internal_owner : ( XAddress ) ) ( tokens : ( XInteger128 ) ) : UExpression PhantomType TRUE . 
 	 	 	 refine {{ require_ ( ( _total_granted_ >= (#{ tokens }) ) , error_code::burn_unallocated ) ; _ }} . 
 	 	 refine {{ sender : ( auto ) @ "sender" ; _ }} . 
 	 	 refine {{ (!{ value_gr }) : ( auto ) @ "value_gr" ; _ }} . 
 	 	 refine {{ [ sender , { value_gr } ] := int_sender_and_value () ; _ }} . 
 	 	 refine {{ require_ ( ( sender == expected_internal_address_ ( (#{ sender_pubkey }) ) , (#{ sender_owner }) ) ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ ( *external_wallet_ ) ( Grams ( 0 ) , SEND_ALL_GAS ) . transferToRecipient ( (#{ answer_addr }) , (#{ out_pubkey }) , (#{ out_internal_owner }) , (#{ tokens }) , uint128 ( 0 ) , bool_t TRUE , bool_t FALSE ) ; _ }} . 
 	 	 refine {{ _total_granted_ -= (#{ tokens }) }} . 
 Defined . 
 
 
 
 
 Definition requestTotalGranted : UExpression XInteger128 FALSE . 
 	 	 	 refine {{ new 'value_gr : ( auto ) @ "value_gr" := {} ; _ }} . 
 	 	 refine {{ { value_gr } := int_value () ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ return_ _total_granted_ }} . 
 Defined . 
 
 
 
 
 Definition getDetails : UExpression wrapper_details_infoLRecord FALSE . 
 	 	 	 refine {{ return_ [ getName_ () , getSymbol_ () , getDecimals_ () , getRootKey_ () , getTotalGranted_ () , getInternalWalletCode_ () , getOwnerAddress_ () , getExternalWallet_ () ] }} . 
 Defined . 
 
 
 
 
 Definition getName : UExpression XString FALSE . 
 	 	 	 refine {{ return_ _name_ }} . 
 Defined . 
 
 
 
 
 Definition getSymbol : UExpression XString FALSE . 
 	 	 	 refine {{ return_ _symbol_ }} . 
 Defined . 
 
 
 
 
 Definition getDecimals : UExpression XInteger8 FALSE . 
 	 	 	 refine {{ return_ _decimals_ }} . 
 Defined . 
 
 
 
 
 Definition getRootKey : UExpression XInteger256 FALSE . 
 	 	 	 refine {{ return_ _root_public_key_ }} . 
 Defined . 
 
 
 
 
 Definition getTotalGranted : UExpression XInteger128 FALSE . 
 	 	 	 refine {{ return_ _total_granted_ }} . 
 Defined . 
 
 
 
 
 Definition hasInternalWalletCode : UExpression XBool FALSE . 
 	 	 	 refine {{ return_ bool_t { ~ ~ _internal_wallet_code_ } }} . 
 Defined . 
 
 
 
 
 Definition getInternalWalletCode : UExpression XCell FALSE . 
 	 	 	 refine {{ return_ _internal_wallet_code_ ^^ get () }} . 
 Defined . 
 
 
 
 
 Definition getOwnerAddress : UExpression XAddress FALSE . 
 	 	 	 refine {{ return_ _owner_address_ ? *owner_address_ : Address :: make_std ( 0 , 0 ) }} . 
 Defined . 
 
 
 
 
 Definition getExternalWallet : UExpression XAddress FALSE . 
 	 	 	 refine {{ return_ _external_wallet_ - > get () }} . 
 Defined . 
 
 
 
 
 Definition getWalletAddress ( pubkey : ( XInteger256 ) ) ( owner : ( XAddress ) ) : UExpression XAddress FALSE . 
 	 	 	 refine {{ return_ calc_internal_wallet_init_ ( (#{ pubkey }) , (#{ owner }) ) . second }} . 
 Defined . 
 
 
 
 
 Definition _on_bounced ( cell : ( (LRecord ) ) ( msg_body : ( XSlice ) ) : UExpression XInteger TRUE . 
 	 	 	 refine {{ tvm.accept () ; _ }} . 
 	 	 refine {{ new 'Args : ( usingLRecord ) @ "Args" := {} ; _ }} . 
 	 	 refine {{ { Args } := args_struct_t ; _ }} . 
 	 	 refine {{ parser p ( (#{ msg_body }) ) ; _ }} . 
 	 	 refine {{ require_ ( ( p ^^ ldi ( 32 ) == - 1 ) , error_code::wrong_bounced_header ) ; _ }} . 
 	 	 refine {{ opt_hdr : ( auto ) @ "opt_hdr" ; _ }} . 
 	 	 refine {{ =p : ( auto ) @ "=p" ; _ }} . 
 	 	 refine {{ [ opt_hdr , =p ] := parse_continue < abiv1::internal_msg_header > ( p ) ; _ }} . 
 	 	 refine {{ require_ ( ( opt_hdr && opt_hdr - > function_id == id_v < &ITONTokenWallet::accept > ) , error_code::wrong_bounced_header ) ; _ }} . 
 	 	 refine {{ new 'args : ( auto ) @ "args" := {} ; _ }} . 
 	 	 refine {{ { args } := parse ( p , error_code::wrong_bounced_args ) ; _ }} . 
 	 	 refine {{ new 'bounced_val : ( auto ) @ "bounced_val" := {} ; _ }} . 
 	 	 refine {{ { bounced_val } := (!{ args }) ^^ auto:tokens ; _ }} . 
 	 	 refine {{ hdr : ( auto ) @ "hdr" ; _ }} . 
 	 	 refine {{ persist : ( auto ) @ "persist" ; _ }} . 
 	 	 refine {{ [ hdr , persist ] := load_persistent_data < IWrapper , wrapper_replay_protection_t , DWrapper > () ; _ }} . 
 	 	 refine {{ require_ ( ( (!{ bounced_val }) <= persist ^^ _total_granted_ ) , error_code::wrong_bounced_args ) ; _ }} . 
 	 	 refine {{ persist ^^ _total_granted_ - = (!{ bounced_val }) ; _ }} . 
 	 	 refine {{ save_persistent_data < IWrapper , wrapper_replay_protection_t > ( hdr , persist ) ; _ }} . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 
 
 
 Definition getInternalWalletCodeHash : UExpression XInteger256 FALSE . 
 	 	 	 refine {{ return_ uint256 { __builtin_tvm.hashcu ( _internal_wallet_code_ . get () ) } }} . 
 Defined . 
 
 
 
 
 Definition _fallback ( msg : ( XCell ) ) ( msg_body : ( XSlice ) ) : UExpression XInteger FALSE . 
 	 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 
 
 
 Definition optional_owner ( owner : ( XAddress ) ) : UExpression XMaybe XAddress FALSE . 
 	 	 	 refine {{ return_ Std :: get < addr_std > ( (#{ owner }) () ) . address ? std::optional ( (#{ owner }) ) : std::optional () }} . 
 Defined . 
 
 
 
 
 Definition expected_internal_address ( sender_public_key : ( XInteger256 ) ) ( sender_owner_addr : ( XAddress ) ) : UExpression XAddress FALSE . 
 	 	 	 refine {{ new 'hash_addr : ( XInteger256 ) @ "hash_addr" := {} ; _ }} . 
 	 	 refine {{ { hash_addr } := prepare_internal_wallet_state_init_and_addr ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ sender_public_key }) , Address { tvm.address () } , optional_owner_ ( (#{ sender_owner_addr }) ) , _internal_wallet_code_ ^^ get () , _workchain_id_ ) . second ; _ }} . 
 	 	 refine {{ return_ Address :: make_std ( _workchain_id_ , (!{ hash_addr }) ) }} . 
 Defined . 
 
 
 
 
 Definition calc_internal_wallet_init ( pubkey : ( XInteger256 ) ) ( owner_addr : ( XAddress ) ) : UExpression ( StateInitLRecord * XAddress ) FALSE . 
 	 	 	 refine {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
 	 	 refine {{ dest_addr : ( auto ) @ "dest_addr" ; _ }} . 
 	 	 refine {{ [ wallet_init , dest_addr ] := prepare_internal_wallet_state_init_and_addr ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ pubkey }) , address { tvm.address () } , optional_owner_ ( (#{ owner_addr }) ) , _internal_wallet_code_ . get () , _workchain_id_ ) ; _ }} . 
 	 	 refine {{ new 'dest : ( XAddress ) @ "dest" := {} ; _ }} . 
 	 	 refine {{ { dest } := Address :: make_std ( _workchain_id_ , dest_addr ) ; _ }} . 
 	 	 refine {{ return_ [ wallet_init , (!{ dest }) ] }} . 
 Defined . 
 
 
 
 
 Definition is_internal_owner : UExpression XBool FALSE . 
 	 	 	 refine {{ return_ _owner_address_ ^^ has_value () }} . 
 Defined . 
 
 
 
 
 Definition check_internal_owner : UExpression PhantomType TRUE . 
 	 	 	 refine {{ require_ ( ( is_internal_owner_ () ) , error_code::internal_owner_disabled ) ; _ }} . 
 	 	 refine {{ require_ ( ( *owner_address_ == int_sender () ) , error_code::message_sender_is_not_my_owner ) }} . 
 Defined . 
 
 
 
 
 Definition check_external_owner : UExpression PhantomType TRUE . 
 	 	 	 refine {{ require_ ( ( ~ is_internal_owner_ () ) , error_code::internal_owner_enabled ) ; _ }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _root_public_key_ ) , error_code::message_sender_is_not_my_owner ) }} . 
 Defined . 
 
 
 
 
 Definition check_owner : UExpression PhantomType FALSE . 
 	 	 	 refine {{ if ( Internal ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ check_internal_owner_ () }} . 
 	 	 refine {{ check_external_owner_ () ; _ }} . 
 
 
 Defined . 
 
 
 
 
 Definition prepare_wrapper_state_init_and_addr ( wrapper_code : ( XCell ) ) ( wrapper_data : ( DWrapperLRecord ) ) : UExpression ( StateInitLRecord * XInteger256 ) FALSE . 
 	 	 	 refine {{ new 'wrapper_data_cl : ( XCell ) @ "wrapper_data_cl" := {} ; _ }} . 
 	 	 refine {{ { wrapper_data_cl } := prepare_persistent_data ( wrapper_replay_protection_t::init () , (#{ wrapper_data }) ) ; _ }} . 
 	 	 refine {{ new 'wrapper_init : ( StateInitLRecord ) @ "wrapper_init" := 	 	 
 	 	 	 [ {} , {} , (#{ wrapper_code }) , (!{ wrapper_data_cl }) , {} ] ; _ }} . 
 	 	 refine {{ new 'wrapper_init_cl : ( XCell ) @ "wrapper_init_cl" := {} ; _ }} . 
 	 	 refine {{ { wrapper_init_cl } := build ( (!{ wrapper_init }) ) . make_cell () ; _ }} . 
 	 	 refine {{ return_ [ (!{ wrapper_init }) , tvm.hash ( (!{ wrapper_init_cl }) ) ] }} . 
 Defined . 
 
 
 
 
 .


End FuncsInternal.
End Funcs.








