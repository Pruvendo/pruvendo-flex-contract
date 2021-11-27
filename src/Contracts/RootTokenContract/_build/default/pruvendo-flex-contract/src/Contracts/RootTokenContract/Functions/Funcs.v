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
Require Import Contracts.RootTokenContract.Ledger.
Require Import Contracts.RootTokenContract.Functions.FuncSig.
Require Import Contracts.RootTokenContract.Functions.FuncNotations.
Require Contracts.RootTokenContract.Interface.

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
 
Module Type Has_Internal.

Parameter Internal: bool .

End Has_Internal.

Module Funcs (ha : Has_Internal)(dc : ConstsTypesSig XTypesModule StateMonadModule) .

Import ha.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

(* Export SpecModuleForFuncNotations(* ForFuncs *).CommonNotationsModule.
 *)
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


Definition constructor ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( root_owner : ( XAddress ) ) ( total_supply : ( XUInteger128 ) ) : UExpression PhantomType TRUE . 
 	 	 	 refine {{ require_ ( ( ( (#{ root_public_key }) != 0 ) or ( std::get < addr_std > ( (#{ root_owner }) () ) . address != 0 ) ) , error_code::define_pubkey_or_internal_owner ) ; _ }} . 
 	 	 refine {{ require_ ( ( (#{ decimals }) < 4 ) , error_code::too_big_decimals ) ; _ }} . 
 	 	 refine {{ _name_ := (#{ name }) ; _ }} . 
 	 	 refine {{ _symbol_ := (#{ symbol }) ; _ }} . 
 	 	 refine {{ _decimals_ := (#{ decimals }) ; _ }} . 
 	 	 refine {{ _root_public_key_ := (#{ root_public_key }) ; _ }} . 
 	 	 refine {{ _total_supply_ := (#{ total_supply }) ; _ }} . 
 	 	 refine {{ _total_granted_ := 0 ; _ }} . 
 	 	 refine {{ _owner_address_ := optional_owner_ ( (#{ root_owner }) ) ; _ }} . 
 	 	 refine {{ _start_balance_ := tvm.balance () }} . 
 Defined . 
 
 
 
 
 Definition setWalletCode ( wallet_code : ( XCell ) ) : UExpression XBool TRUE . 
 	 	 	 refine {{ check_owner_ ( TRUE ) ; _ }} . 
 	 	 refine {{ tvm.accept () ; _ }} . 
 	 	 refine {{ require_ ( ( ~ _wallet_code_ ) , error_code::cant_override_wallet_code ) ; _ }} . 
 	 	 refine {{ _wallet_code_ := (#{ wallet_code }) ; _ }} . 
 	 	 refine {{ if ( Internal ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ { auto value_gr = int_value () ; _ }} . 
 	 	 	 refine {{ tvm.rawreserve ( tvm.balance () - value_gr () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) }} . 
 	 refine {{ return bool_t TRUE ; _ }} . 
 
 Defined . 
 
 
 
 
 Definition deployWallet ( pubkey : ( XUInteger256 ) ) ( internal_owner : ( XAddress ) ) ( tokens : ( XUInteger128 ) ) ( grams : ( XUInteger128 ) ) : UExpression XAddress TRUE . 
 	 	 	 refine {{ check_owner_ () ; _ }} . 
 	 	 refine {{ tvm.accept () ; _ }} . 
 	 	 refine {{ require_ ( ( _total_granted_ + (#{ tokens }) <= _total_supply_ ) , error_code::not_enough_balance ) ; _ }} . 
 	 	 refine {{ require_ ( ( (#{ pubkey }) != 0 || std::get < addr_std > ( (#{ internal_owner }) () ) . address != 0 ) , error_code::define_pubkey_or_internal_owner ) ; _ }} . 
 	 	 refine {{ address answer_addr ; _ }} . 
 	 	 refine {{ if ( Internal ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ { auto value_gr = int_value () ; _ }} . 
 	 	 	 refine {{ tvm.rawreserve ( tvm.balance () - value_gr () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 	 refine {{ answer_addr := int_sender () }} . 
 	 refine {{ { answer_addr := Address { tvm.address () } }} . 
 refine {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
 	 	 refine {{ dest : ( auto ) @ "dest" ; _ }} . 
 	 	 refine {{ [ wallet_init , dest ] := calc_wallet_init_ ( (#{ pubkey }) , (#{ internal_owner }) ) ; _ }} . 
 refine {{ temporary_data::setglob ( global_id::answer_id , return_func_id () - > get () ) ; _ }} . 
 refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; _ }} . 
 refine {{ dest_handle ^^ deploy ( wallet_init , Grams ( (#{ grams }) . get () ) ) . accept ( (#{ tokens }) , answer_addr , (#{ grams }) ) ; _ }} . 
 refine {{ _total_granted_ += (#{ tokens }) ; _ }} . 
 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 refine {{ return_ dest ; _ }} . 
 
 
 Defined . 
 
 
 
 
 Definition deployEmptyWallet ( pubkey : ( XUInteger256 ) ) ( internal_owner : ( XAddress ) ) ( grams : ( XUInteger128 ) ) : UExpression XAddress TRUE . 
 	 	 	 refine {{ require_ ( ( (#{ pubkey }) != 0 || std::get < addr_std > ( (#{ internal_owner }) () ) . address != 0 ) , error_code::define_pubkey_or_internal_owner ) ; _ }} . 
 	 	 refine {{ new 'value_gr : ( auto ) @ "value_gr" := {} ; _ }} . 
 	 	 refine {{ { value_gr } := int_value () ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
 	 	 refine {{ dest : ( auto ) @ "dest" ; _ }} . 
 	 	 refine {{ [ wallet_init , dest ] := calc_wallet_init_ ( (#{ pubkey }) , (#{ internal_owner }) ) ; _ }} . 
 	 	 refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; _ }} . 
 	 	 refine {{ dest_handle ^^ deploy_noop ( wallet_init , Grams ( (#{ grams }) . get () ) ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ return_ dest }} . 
 Defined . 
 
 
 
 
 Definition grant ( dest : ( XAddress ) ) ( tokens : ( XUInteger128 ) ) ( grams : ( XUInteger128 ) ) : UExpression PhantomType TRUE . 
 	 	 	 refine {{ check_owner_ () ; _ }} . 
 	 	 refine {{ require_ ( ( _total_granted_ + (#{ tokens }) <= _total_supply_ ) , error_code::not_enough_balance ) ; _ }} . 
 	 	 refine {{ tvm.accept () ; _ }} . 
 	 	 refine {{ address answer_addr ; _ }} . 
 	 	 refine {{ new 'msg_flags : ( XUInteger ) @ "msg_flags" := {} ; _ }} . 
 	 	 refine {{ { msg_flags } := 0 ; _ }} . 
 	 	 refine {{ if ( Internal ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ { auto (!{ value_gr }) = int_value () ; _ }} . 
 	 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 	 refine {{ { msg_flags } := SEND_ALL_GAS ; _ }} . 
 	 	 	 refine {{ (#{ grams }) := 0 ; _ }} . 
 	 	 	 refine {{ answer_addr := int_sender () }} . 
 	 refine {{ { answer_addr := Address { tvm.address () } }} . 
 refine {{ ITONTokenWalletPtr dest_handle ( (#{ dest }) ) ; _ }} . 
 refine {{ dest_handle ( Grams ( (#{ grams }) . get () ) , (!{ msg_flags }) ) . accept ( (#{ tokens }) , answer_addr , uint128 ( 0 ) ) ; _ }} . 
 refine {{ _total_granted_ += (#{ tokens }) ; _ }} . 
 
 
 Defined . 
 
 
 
 
 Definition mint ( tokens : ( XUInteger128 ) ) : UExpression XBool FALSE . 
 	 	 	 refine {{ check_owner_ () ; _ }} . 
 	 	 refine {{ tvm.accept () ; _ }} . 
 	 	 refine {{ if ( Internal ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ { auto (!{ value_gr }) = int_value () ; _ }} . 
 	 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) }} . 
 	 refine {{ _total_supply_ += (#{ tokens }) ; _ }} . 
 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 refine {{ return bool_t TRUE ; _ }} . 
 
 Defined . 
 
 
 
 
 Definition requestTotalGranted : UExpression XUInteger128 FALSE . 
 	 	 	 refine {{ new 'value_gr : ( auto ) @ "value_gr" := {} ; _ }} . 
 	 	 refine {{ { value_gr } := int_value () ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ return_ _total_granted_ }} . 
 Defined . 
 
 
 
 
 Definition getName : UExpression XString FALSE . 
 	 	 	 refine {{ return_ _name_ }} . 
 Defined . 
 
 
 
 
 Definition getSymbol : UExpression XString FALSE . 
 	 	 	 refine {{ return_ _symbol_ }} . 
 Defined . 
 
 
 
 
 Definition getDecimals : UExpression XUInteger8 FALSE . 
 	 	 	 refine {{ return_ _decimals_ }} . 
 Defined . 
 
 
 
 
 Definition getRootKey : UExpression XUInteger256 FALSE . 
 	 	 	 refine {{ return_ _root_public_key_ }} . 
 Defined . 
 
 
 
 
 Definition getTotalSupply : UExpression XUInteger128 FALSE . 
 	 	 	 refine {{ return_ _total_supply_ }} . 
 Defined . 
 
 
 
 
 Definition getTotalGranted : UExpression XUInteger128 FALSE . 
 	 	 	 refine {{ return_ _total_granted_ }} . 
 Defined . 
 
 
 
 
 Definition hasWalletCode : UExpression XBool FALSE . 
 	 	 	 refine {{ return bool_t { ~ ~ _wallet_code_ } }} . 
 Defined . 
 
 
 
 
 Definition getWalletCode : UExpression XCell FALSE . 
 	 	 	 refine {{ return_ _wallet_code_ ^^ get () }} . 
 Defined . 
 
 
 
 
 Definition getWalletAddress ( pubkey : ( XUInteger256 ) ) ( owner : ( XAddress ) ) : UExpression XAddress FALSE . 
 	 	 	 refine {{ return_ calc_wallet_init_ ( (#{ pubkey }) , (#{ owner }) ) . second }} . 
 Defined . 
 
 
 
 
 Definition _on_bounced ( cell : ( (LRecord ) ) ( msg_body : ( XSlice ) ) : UExpression XUInteger TRUE . 
 	 	 	 refine {{ tvm.accept () ; _ }} . 
 	 	 refine {{ new 'Args : ( usingLRecord ) @ "Args" := {} ; _ }} . 
 	 	 refine {{ { Args } := args_struct_t ; _ }} . 
 	 	 refine {{ parser p ( (#{ msg_body }) ) ; _ }} . 
 	 	 refine {{ require_ ( ( p ^^ ldi ( 32 ) == - 1 ) , error_code::wrong_bounced_header ) ; _ }} . 
 	 	 refine {{ opt_hdr : ( auto ) @ "opt_hdr" ; _ }} . 
 	 	 refine {{ =p : ( auto ) @ "=p" ; _ }} . 
 	 	 refine {{ [ opt_hdr , =p ] := parse_continue < abiv2::internal_msg_header_with_answer_id > ( p ) ; _ }} . 
 	 	 refine {{ require_ ( ( opt_hdr && opt_hdr - > function_id == id_v < &ITONTokenWallet::accept > ) , error_code::wrong_bounced_header ) ; _ }} . 
 	 	 refine {{ new 'args : ( auto ) @ "args" := {} ; _ }} . 
 	 	 refine {{ { args } := parse ( p , error_code::wrong_bounced_args ) ; _ }} . 
 	 	 refine {{ new 'bounced_val : ( auto ) @ "bounced_val" := {} ; _ }} . 
 	 	 refine {{ { bounced_val } := (!{ args }) ^^ auto:tokens ; _ }} . 
 	 	 refine {{ hdr : ( auto ) @ "hdr" ; _ }} . 
 	 	 refine {{ persist : ( auto ) @ "persist" ; _ }} . 
 	 	 refine {{ [ hdr , persist ] := load_persistent_data < IRootTokenContract , root_replay_protection_t , DRootTokenContract > () ; _ }} . 
 	 	 refine {{ require_ ( ( (!{ bounced_val }) <= persist ^^ _total_granted_ ) , error_code::wrong_bounced_args ) ; _ }} . 
 	 	 refine {{ persist ^^ _total_granted_ - = (!{ bounced_val }) ; _ }} . 
 	 	 refine {{ save_persistent_data < IRootTokenContract , root_replay_protection_t > ( hdr , persist ) ; _ }} . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 
 
 
 Definition getWalletCodeHash : UExpression XUInteger256 FALSE . 
 	 	 	 refine {{ return uint256 { __builtin_tvm_hashcu ( _wallet_code_ . get () ) } }} . 
 Defined . 
 
 
 
 
 Definition _fallback ( cell : ( (LRecord ) ) : UExpression XUInteger FALSE . 
 	 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 
 
 
 Definition optional_owner ( owner : ( XAddress ) ) : UExpression XMaybe XAddress FALSE . 
 	 	 	 refine {{ return_ Std :: get < addr_std > ( (#{ owner }) () ) . address ? std::optional ( (#{ owner }) ) : std::optional () }} . 
 Defined . 
 
 
 
 
 Definition workchain_id : UExpression XUInteger8 FALSE . 
 	 	 	 refine {{ return_ Std :: get < addr_std > ( Address { tvm.address () } () ) . workchain_id_ }} . 
 Defined . 
 
 
 
 
 Definition calc_wallet_init ( pubkey : ( XUInteger256 ) ) ( owner_addr : ( XAddress ) ) : UExpression ( StateInitLRecord * XAddress ) FALSE . 
 	 	 	 refine {{ new 'wallet_data : ( DTONTokenWalletLRecord ) @ "wallet_data" := {} ; _ }} . 
 	 	 refine {{ { wallet_data } := prepare_wallet_data ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ pubkey }) , Address { tvm.address () } , optional_owner_ ( (#{ owner_addr }) ) , _wallet_code_ ^^ get () , workchain_id_ () ) ; _ }} . 
 	 	 refine {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
 	 	 refine {{ dest_addr : ( auto ) @ "dest_addr" ; _ }} . 
 	 	 refine {{ [ wallet_init , dest_addr ] := prepare_wallet_state_init_and_addr ( (!{ wallet_data }) ) ; _ }} . 
 	 	 refine {{ new 'dest : ( XAddress ) @ "dest" := {} ; _ }} . 
 	 	 refine {{ { dest } := Address :: make_std ( workchain_id_ () , dest_addr ) ; _ }} . 
 	 	 refine {{ return_ [ wallet_init , (!{ dest }) ] }} . 
 Defined . 
 
 
 
 
 Definition is_internal_owner : UExpression XBool FALSE . 
 	 	 	 refine {{ return_ _owner_address_ ^^ has_value () }} . 
 Defined . 
 
 
 
 
 Definition check_internal_owner : UExpression PhantomType TRUE . 
 	 	 	 refine {{ require_ ( ( is_internal_owner_ () ) , error_code::internal_owner_disabled ) ; _ }} . 
 	 	 refine {{ require_ ( ( *owner_address_ == int_sender () ) , error_code::message_sender_is_not_my_owner ) }} . 
 Defined . 
 
 
 
 
 Definition check_external_owner ( allow_pubkey_owner_in_internal_node : ( XBool ) ) : UExpression PhantomType TRUE . 
 	 	 	 refine {{ require_ ( ( (#{ allow_pubkey_owner_in_internal_node }) || ~ is_internal_owner_ () ) , error_code::internal_owner_enabled ) ; _ }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _root_public_key_ ) , error_code::message_sender_is_not_my_owner ) }} . 
 Defined . 
 
 
 
 
 Definition check_owner ( FALSE : ( =LRecord ) ) : UExpression PhantomType FALSE . 
 	 	 	 refine {{ if ( Internal ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ check_internal_owner_ () }} . 
 	 	 refine {{ check_external_owner_ ( allow_pubkey_owner_in_internal_node ) ; _ }} . 
 
 
 Defined . 
 
 
 
 
 Definition prepare_root_state_init_and_addr ( root_code : ( XCell ) ) ( root_data : ( DRootTokenContractLRecord ) ) : UExpression ( StateInitLRecord * XUInteger256 ) FALSE . 
 	 	 	 refine {{ new 'root_data_cl : ( XCell ) @ "root_data_cl" := {} ; _ }} . 
 	 	 refine {{ { root_data_cl } := prepare_persistent_data ( root_replay_protection_t::init () , (#{ root_data }) ) ; _ }} . 
 	 	 refine {{ new 'root_init : ( StateInitLRecord ) @ "root_init" := 	 	 
 	 	 	 [ {} , {} , (#{ root_code }) , (!{ root_data_cl }) , {} ] ; _ }} . 
 	 	 refine {{ new 'root_init_cl : ( XCell ) @ "root_init_cl" := {} ; _ }} . 
 	 	 refine {{ { root_init_cl } := build ( (!{ root_init }) ) . make_cell () ; _ }} . 
 	 	 refine {{ return_ [ (!{ root_init }) , tvm_hash ( (!{ root_init_cl }) ) ] }} . 
 Defined . 
 
 
 
 
 .


End FuncsInternal.
End Funcs.








