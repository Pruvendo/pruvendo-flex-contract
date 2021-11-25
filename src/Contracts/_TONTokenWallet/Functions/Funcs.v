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
Require Import Contracts.Price.Ledger.
Require Import Contracts.Price.Functions.FuncSig.
Require Import Contracts.Price.Functions.FuncNotations.
Require Contracts.Price.Interface.

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



 Definition transfer_left { R a1 a2 a3 a4 a5 }  ( answer_addr : URValue ( XAddress ) a1 ) ( to : URValue ( XAddress ) a2 ) ( tokens : URValue ( XInteger128 ) a3 ) ( grams : URValue ( XInteger128 ) a4 ) ( return_ownership : URValue ( XBool ) a5 ) : UExpression R ( orb ( orb ( orb ( orb a5 a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) transfer 
 answer_addr to tokens grams return_ownership ) . 
 
 Notation " 'transfer_' '(' answer_addr to tokens grams return_ownership ')' " := 
 ( transfer_left 
 answer_addr to tokens grams return_ownership ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , to custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , return_ownership custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferWithNotify_left { R a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( XAddress ) a1 ) ( to : URValue ( XAddress ) a2 ) ( tokens : URValue ( XInteger128 ) a3 ) ( grams : URValue ( XInteger128 ) a4 ) ( return_ownership : URValue ( XBool ) a5 ) ( payload : URValue ( XCell ) a6 ) : UExpression R ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) transferWithNotify 
 answer_addr to tokens grams return_ownership payload ) . 
 
 Notation " 'transferWithNotify_' '(' answer_addr to tokens grams return_ownership payload ')' " := 
 ( transferWithNotify_left 
 answer_addr to tokens grams return_ownership payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , to custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferToRecipient_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( XAddress ) a1 ) ( recipient_public_key : URValue ( XInteger256 ) a2 ) ( recipient_internal_owner : URValue ( XAddress ) a3 ) ( tokens : URValue ( XInteger128 ) a4 ) ( grams : URValue ( XInteger128 ) a5 ) ( deploy : URValue ( XBool ) a6 ) ( return_ownership : URValue ( XBool ) a7 ) : UExpression R ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) transferToRecipient 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership ) . 
 
 Notation " 'transferToRecipient_' '(' answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership ')' " := 
 ( transferToRecipient_left 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , recipient_public_key custom URValue at level 0 
 , recipient_internal_owner custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , deploy custom URValue at level 0 
 , return_ownership custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferToRecipientWithNotify_left { R a1 a2 a3 a4 a5 a6 a7 a8 }  ( answer_addr : URValue ( XAddress ) a1 ) ( recipient_public_key : URValue ( XInteger256 ) a2 ) ( recipient_internal_owner : URValue ( XAddress ) a3 ) ( tokens : URValue ( XInteger128 ) a4 ) ( grams : URValue ( XInteger128 ) a5 ) ( deploy : URValue ( XBool ) a6 ) ( return_ownership : URValue ( XBool ) a7 ) ( payload : URValue ( XCell ) a8 ) : UExpression R ( orb ( orb ( orb ( orb ( orb ( orb ( orb a8 a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ8 ) transferToRecipientWithNotify 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership payload ) . 
 
 Notation " 'transferToRecipientWithNotify_' '(' answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership payload ')' " := 
 ( transferToRecipientWithNotify_left 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , recipient_public_key custom URValue at level 0 
 , recipient_internal_owner custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , deploy custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 Definition requestBalance_right  : URValue XInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) requestBalance 
 ) . 
 
 Notation " 'requestBalance_' '(' ')' " := 
 ( requestBalance_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition accept_right { a1 a2 a3 }  ( tokens : URValue ( XInteger128 ) a1 ) ( answer_addr : URValue ( XAddress ) a2 ) ( keep_grams : URValue ( XInteger128 ) a3 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) accept 
 tokens answer_addr keep_grams ) . 
 
 Notation " 'accept_' '(' tokens answer_addr keep_grams ')' " := 
 ( accept_right 
 tokens answer_addr keep_grams ) 
 (in custom URValue at level 0 , tokens custom URValue at level 0 
 , answer_addr custom URValue at level 0 
 , keep_grams custom URValue at level 0 ) : ursus_scope . 
 
 Definition internalTransfer_left { R a1 a2 a3 a4 a5 a6 }  ( tokens : URValue ( XInteger128 ) a1 ) ( answer_addr : URValue ( XAddress ) a2 ) ( sender_pubkey : URValue ( XInteger256 ) a3 ) ( sender_owner : URValue ( XAddress ) a4 ) ( notify_receiver : URValue ( XBool ) a5 ) ( payload : URValue ( XCell ) a6 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) internalTransfer 
 tokens answer_addr sender_pubkey sender_owner notify_receiver payload ) . 
 
 Notation " 'internalTransfer_' '(' tokens answer_addr sender_pubkey sender_owner notify_receiver payload ')' " := 
 ( internalTransfer_left 
 tokens answer_addr sender_pubkey sender_owner notify_receiver payload ) 
 (in custom ULValue at level 0 , tokens custom URValue at level 0 
 , answer_addr custom URValue at level 0 
 , sender_pubkey custom URValue at level 0 
 , sender_owner custom URValue at level 0 
 , notify_receiver custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition destroy_left { R a1 }  ( dest : URValue ( XAddress ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) destroy 
 dest ) . 
 
 Notation " 'destroy_' '(' dest ')' " := 
 ( destroy_left 
 dest ) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 ) : ursus_scope . 
 
 Definition burn_left { R a1 a2 }  ( out_pubkey : URValue ( XInteger256 ) a1 ) ( out_internal_owner : URValue ( XAddress ) a2 ) : UExpression R ( orb a2 a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) burn 
 out_pubkey out_internal_owner ) . 
 
 Notation " 'burn_' '(' out_pubkey out_internal_owner ')' " := 
 ( burn_left 
 out_pubkey out_internal_owner ) 
 (in custom ULValue at level 0 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 ) : ursus_scope . 
 
 Definition lendOwnership_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( XAddress ) a1 ) ( grams : URValue ( XInteger128 ) a2 ) ( std_dest : URValue ( XInteger256 ) a3 ) ( lend_balance : URValue ( XInteger128 ) a4 ) ( lend_finish_time : URValue ( XInteger32 ) a5 ) ( deploy_init_cl : URValue ( XCell ) a6 ) ( payload : URValue ( XCell ) a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) lendOwnership 
 answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload ) . 
 
 Notation " 'lendOwnership_' '(' answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload ')' " := 
 ( lendOwnership_left 
 answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , grams custom URValue at level 0 
 , std_dest custom URValue at level 0 
 , lend_balance custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , deploy_init_cl custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition returnOwnership_left { R a1 }  ( tokens : URValue ( XInteger128 ) a1 ) : UExpression R a1 := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) returnOwnership 
 tokens ) . 
 
 Notation " 'returnOwnership_' '(' tokens ')' " := 
 ( returnOwnership_left 
 tokens ) 
 (in custom ULValue at level 0 , tokens custom URValue at level 0 ) : ursus_scope . 
 Definition getDetails_right  : URValue details_infoLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDetails 
 ) . 
 
 Notation " 'getDetails_' '(' ')' " := 
 ( getDetails_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getName_right  : URValue XString false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getName 
 ) . 
 
 Notation " 'getName_' '(' ')' " := 
 ( getName_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getSymbol_right  : URValue XString false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSymbol 
 ) . 
 
 Notation " 'getSymbol_' '(' ')' " := 
 ( getSymbol_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getDecimals_right  : URValue XInteger8 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDecimals 
 ) . 
 
 Notation " 'getDecimals_' '(' ')' " := 
 ( getDecimals_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getBalance_right  : URValue XInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBalance 
 ) . 
 
 Notation " 'getBalance_' '(' ')' " := 
 ( getBalance_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getRootKey_right  : URValue XInteger256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootKey 
 ) . 
 
 Notation " 'getRootKey_' '(' ')' " := 
 ( getRootKey_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getWalletKey_right  : URValue XInteger256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getWalletKey 
 ) . 
 
 Notation " 'getWalletKey_' '(' ')' " := 
 ( getWalletKey_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getRootAddress_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootAddress 
 ) . 
 
 Notation " 'getRootAddress_' '(' ')' " := 
 ( getRootAddress_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getOwnerAddress_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwnerAddress 
 ) . 
 
 Notation " 'getOwnerAddress_' '(' ')' " := 
 ( getOwnerAddress_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getCode_right  : URValue XCell false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getCode 
 ) . 
 
 Notation " 'getCode_' '(' ')' " := 
 ( getCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition allowance_right  : URValue allowance_infoLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) allowance 
 ) . 
 
 Notation " 'allowance_' '(' ')' " := 
 ( allowance_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition approve_left { R a1 a2 a3 }  ( spender : URValue ( XAddress ) a1 ) ( remainingTokens : URValue ( XInteger128 ) a2 ) ( tokens : URValue ( XInteger128 ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) approve 
 spender remainingTokens tokens ) . 
 
 Notation " 'approve_' '(' spender remainingTokens tokens ')' " := 
 ( approve_left 
 spender remainingTokens tokens ) 
 (in custom ULValue at level 0 , spender custom URValue at level 0 
 , remainingTokens custom URValue at level 0 
 , tokens custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferFrom_left { R a1 a2 a3 a4 a5 }  ( answer_addr : URValue ( XAddress ) a1 ) ( from : URValue ( XAddress ) a2 ) ( to : URValue ( XAddress ) a3 ) ( tokens : URValue ( XInteger128 ) a4 ) ( grams : URValue ( XInteger128 ) a5 ) : UExpression R ( orb ( orb ( orb ( orb a5 a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) transferFrom 
 answer_addr from to tokens grams ) . 
 
 Notation " 'transferFrom_' '(' answer_addr from to tokens grams ')' " := 
 ( transferFrom_left 
 answer_addr from to tokens grams ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , from custom URValue at level 0 
 , to custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferFromWithNotify_left { R a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( XAddress ) a1 ) ( from : URValue ( XAddress ) a2 ) ( to : URValue ( XAddress ) a3 ) ( tokens : URValue ( XInteger128 ) a4 ) ( grams : URValue ( XInteger128 ) a5 ) ( payload : URValue ( XCell ) a6 ) : UExpression R ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) transferFromWithNotify 
 answer_addr from to tokens grams payload ) . 
 
 Notation " 'transferFromWithNotify_' '(' answer_addr from to tokens grams payload ')' " := 
 ( transferFromWithNotify_left 
 answer_addr from to tokens grams payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , from custom URValue at level 0 
 , to custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition internalTransferFrom_left { R a1 a2 a3 a4 a5 }  ( answer_addr : URValue ( XAddress ) a1 ) ( to : URValue ( XAddress ) a2 ) ( tokens : URValue ( XInteger128 ) a3 ) ( notify_receiver : URValue ( XBool ) a4 ) ( payload : URValue ( XCell ) a5 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) internalTransferFrom 
 answer_addr to tokens notify_receiver payload ) . 
 
 Notation " 'internalTransferFrom_' '(' answer_addr to tokens notify_receiver payload ')' " := 
 ( internalTransferFrom_left 
 answer_addr to tokens notify_receiver payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , to custom URValue at level 0 
 , tokens custom URValue at level 0 
 , notify_receiver custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition disapprove_left { R }  : UExpression R := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) disapprove 
 ) . 
 
 Notation " 'disapprove_' '(' ')' " := 
 ( disapprove_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 Definition _on_bounced_right { a1 a2 }  ( msg : URValue ( XCell ) a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue XInteger true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _on_bounced 
 msg msg_body ) . 
 
 Notation " '_on_bounced_' '(' msg msg_body ')' " := 
 ( _on_bounced_right 
 msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 
 Definition _fallback_right { a1 a2 }  ( cell : URValue ( (LRecord ) a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue XInteger true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 cell msg_body ) . 
 
 Notation " '_fallback_' '(' cell msg_body ')' " := 
 ( _fallback_right 
 cell msg_body ) 
 (in custom URValue at level 0 , cell custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_impl_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( XAddress ) a1 ) ( to : URValue ( XAddress ) a2 ) ( tokens : URValue ( XInteger128 ) a3 ) ( grams : URValue ( XInteger128 ) a4 ) ( return_ownership : URValue ( XBool ) a5 ) ( send_notify : URValue ( XBool ) a6 ) ( payload : URValue ( XCell ) a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) transfer_impl 
 answer_addr to tokens grams return_ownership send_notify payload ) . 
 
 Notation " 'transfer_impl_' '(' answer_addr to tokens grams return_ownership send_notify payload ')' " := 
 ( transfer_impl_left 
 answer_addr to tokens grams return_ownership send_notify payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , to custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , send_notify custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_to_recipient_impl_left { R a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( answer_addr : URValue ( XAddress ) a1 ) ( recipient_public_key : URValue ( XInteger256 ) a2 ) ( recipient_internal_owner : URValue ( XAddress ) a3 ) ( tokens : URValue ( XInteger128 ) a4 ) ( grams : URValue ( XInteger128 ) a5 ) ( deploy : URValue ( XBool ) a6 ) ( return_ownership : URValue ( XBool ) a7 ) ( send_notify : URValue ( XBool ) a8 ) ( payload : URValue ( XCell ) a9 ) : UExpression R ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) transfer_to_recipient_impl 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ) . 
 
 Notation " 'transfer_to_recipient_impl_' '(' answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ')' " := 
 ( transfer_to_recipient_impl_left 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , recipient_public_key custom URValue at level 0 
 , recipient_internal_owner custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , deploy custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , send_notify custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_from_impl_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( XAddress ) a1 ) ( from : URValue ( XAddress ) a2 ) ( to : URValue ( XAddress ) a3 ) ( tokens : URValue ( XInteger128 ) a4 ) ( grams : URValue ( XInteger128 ) a5 ) ( send_notify : URValue ( XBool ) a6 ) ( payload : URValue ( XCell ) a7 ) : UExpression R ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) transfer_from_impl 
 answer_addr from to tokens grams send_notify payload ) . 
 
 Notation " 'transfer_from_impl_' '(' answer_addr from to tokens grams send_notify payload ')' " := 
 ( transfer_from_impl_left 
 answer_addr from to tokens grams send_notify payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , from custom URValue at level 0 
 , to custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , send_notify custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 Definition get_owner_addr_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) get_owner_addr 
 ) . 
 
 Notation " 'get_owner_addr_' '(' ')' " := 
 ( get_owner_addr_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition fixup_answer_addr_right { a1 }  ( answer_addr : URValue ( XAddress ) a1 ) : URValue XAddress a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) fixup_answer_addr 
 answer_addr ) . 
 
 Notation " 'fixup_answer_addr_' '(' answer_addr ')' " := 
 ( fixup_answer_addr_right 
 answer_addr ) 
 (in custom URValue at level 0 , answer_addr custom URValue at level 0 ) : ursus_scope . 
 Definition check_transfer_requires_right { a1 a2 }  ( tokens : URValue ( XInteger128 ) a1 ) ( grams : URValue ( XInteger128 ) a2 ) : URValue XInteger128 true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_transfer_requires 
 tokens grams ) . 
 
 Notation " 'check_transfer_requires_' '(' tokens grams ')' " := 
 ( check_transfer_requires_right 
 tokens grams ) 
 (in custom URValue at level 0 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 Definition prepare_transfer_message_flags_right { a1 }  ( &grams : URValue ( XInteger128 ) a1 ) : URValue XInteger a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) prepare_transfer_message_flags 
 &grams ) . 
 
 Notation " 'prepare_transfer_message_flags_' '(' &grams ')' " := 
 ( prepare_transfer_message_flags_right 
 &grams ) 
 (in custom URValue at level 0 , &grams custom URValue at level 0 ) : ursus_scope . 
 
 Definition update_spent_balance_left { R a1 a2 }  ( tokens : URValue ( XInteger128 ) a1 ) ( return_ownership : URValue ( XBool ) a2 ) : UExpression R ( orb a2 a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) update_spent_balance 
 tokens return_ownership ) . 
 
 Notation " 'update_spent_balance_' '(' tokens return_ownership ')' " := 
 ( update_spent_balance_left 
 tokens return_ownership ) 
 (in custom ULValue at level 0 , tokens custom URValue at level 0 
 , return_ownership custom URValue at level 0 ) : ursus_scope . 
 Definition optional_owner_right { a1 }  ( owner : URValue ( XAddress ) a1 ) : URValue XMaybe XAddress a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) optional_owner 
 owner ) . 
 
 Notation " 'optional_owner_' '(' owner ')' " := 
 ( optional_owner_right 
 owner ) 
 (in custom URValue at level 0 , owner custom URValue at level 0 ) : ursus_scope . 
 Definition calc_wallet_init_hash_right { a1 a2 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( internal_owner : URValue ( XAddress ) a2 ) : URValue ( StateInitLRecord * XInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_wallet_init_hash 
 pubkey internal_owner ) . 
 
 Notation " 'calc_wallet_init_hash_' '(' pubkey internal_owner ')' " := 
 ( calc_wallet_init_hash_right 
 pubkey internal_owner ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope . 
 Definition expected_sender_address_right { a1 a2 }  ( sender_public_key : URValue ( XInteger256 ) a1 ) ( sender_owner : URValue ( XAddress ) a2 ) : URValue XInteger256 ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) expected_sender_address 
 sender_public_key sender_owner ) . 
 
 Notation " 'expected_sender_address_' '(' sender_public_key sender_owner ')' " := 
 ( expected_sender_address_right 
 sender_public_key sender_owner ) 
 (in custom URValue at level 0 , sender_public_key custom URValue at level 0 
 , sender_owner custom URValue at level 0 ) : ursus_scope . 
 Definition calc_wallet_init_right { a1 a2 }  ( pubkey : URValue ( XInteger256 ) a1 ) ( internal_owner : URValue ( XAddress ) a2 ) : URValue ( StateInitLRecord * XAddress ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_wallet_init 
 pubkey internal_owner ) . 
 
 Notation " 'calc_wallet_init_' '(' pubkey internal_owner ')' " := 
 ( calc_wallet_init_right 
 pubkey internal_owner ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope . 
 Definition filter_lend_ownerhip_map_right  : URValue ( lend_ownership_mapLRecord * XInteger128 ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) filter_lend_ownerhip_map 
 ) . 
 
 Notation " 'filter_lend_ownerhip_map_' '(' ')' " := 
 ( filter_lend_ownerhip_map_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition filter_lend_ownerhip_array_right  : URValue ( lend_ownership_arrayLRecord * XInteger128 ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) filter_lend_ownerhip_array 
 ) . 
 
 Notation " 'filter_lend_ownerhip_array_' '(' ')' " := 
 ( filter_lend_ownerhip_array_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition is_internal_owner_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) is_internal_owner 
 ) . 
 
 Notation " 'is_internal_owner_' '(' ')' " := 
 ( is_internal_owner_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition check_internal_owner_right { a1 a2 }  ( original_owner_only : URValue ( XBool ) a1 ) ( allowed_for_original_owner_in_lend_state : URValue ( XBool ) a2 ) : URValue XInteger128 true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_internal_owner 
 original_owner_only allowed_for_original_owner_in_lend_state ) . 
 
 Notation " 'check_internal_owner_' '(' original_owner_only allowed_for_original_owner_in_lend_state ')' " := 
 ( check_internal_owner_right 
 original_owner_only allowed_for_original_owner_in_lend_state ) 
 (in custom URValue at level 0 , original_owner_only custom URValue at level 0 
 , allowed_for_original_owner_in_lend_state custom URValue at level 0 ) : ursus_scope . 
 Definition check_external_owner_right  : URValue XInteger128 true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_external_owner 
 ) . 
 
 Notation " 'check_external_owner_' '(' ')' " := 
 ( check_external_owner_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition check_owner_right { a1 a2 }  ( original_owner_only : URValue ( XBool ) a1 ) ( allowed_in_lend_state : URValue ( XBool ) a2 ) : URValue XInteger128 ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_owner 
 original_owner_only allowed_in_lend_state ) . 
 
 Notation " 'check_owner_' '(' original_owner_only allowed_in_lend_state ')' " := 
 ( check_owner_right 
 original_owner_only allowed_in_lend_state ) 
 (in custom URValue at level 0 , original_owner_only custom URValue at level 0 
 , allowed_in_lend_state custom URValue at level 0 ) : ursus_scope . 
 Definition prepare_root_state_init_and_addr_right { a1 a2 }  ( root_code : URValue ( XCell ) a1 ) ( root_data : URValue ( DRootTokenContractLRecord ) a2 ) : URValue ( StateInitLRecord * XInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_root_state_init_and_addr 
 root_code root_data ) . 
 
 Notation " 'prepare_root_state_init_and_addr_' '(' root_code root_data ')' " := 
 ( prepare_root_state_init_and_addr_right 
 root_code root_data ) 
 (in custom URValue at level 0 , root_code custom URValue at level 0 
 , root_data custom URValue at level 0 ) : ursus_scope . 



End FuncsInternal.
End Funcs.








