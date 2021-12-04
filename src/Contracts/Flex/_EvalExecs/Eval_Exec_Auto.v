Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
Require Import FinProof.StateMonad21.
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.


Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.
(* Require Import UMLang.ExecGenerator.
 *)
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.
Require Import Project.CommonNotations.
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.Flex.Ledger.
Require Import Contracts.Flex.Functions.FuncSig.
Require Import Contracts.Flex.Functions.FuncNotations.
Require Import Contracts.Flex.Functions.Funcs.
Require Contracts.Flex.Interface.

(* Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.
 *)

Module EvalExecAuto (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .


Module Export FuncsModule := Funcs co dc.

Import FuncsInternal.
Import co.
 Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module Import TONTonkenWalletModuleForFlex := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .
 (* Export SpecModuleForFuncNotations(* ForFuncs *).CommonNotationsModule. *)
 
(*   Module Import xxx := SpecModuleForFuncNotations.LedgerModuleForFuncSig.
 *)
(* Module Import generator := execGenerator XTypesModule StateMonadModule xxx.
 
  *)
(* Import UrsusNotations. *)
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
(* Local Open Scope struct_scope. *)
(* Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope. *)


(*move somewhere*)
(* Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.
 *)
(* (* ---------------- move to Flex/TemplateEvalExec --------------*)
Definition LocalStateDefault := (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil))),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)))),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil))),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil))))),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil))),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil))))%xprod
: LocalStateLRecord.
 
 Opaque LocalStateDefault. *)
(*   Import URSUS_. *)

Require Import FinProof.StateMonad21.
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.
Ltac generate_proof gen :=
  let e := fresh "e" in
  let H := fresh "H" in
  let gen_nf := eval hnf in gen in
  generate_both gen_nf e H; cycle -1;
  (only 1: (exists e; subst e; reflexivity));
  eexists; reflexivity.

  Definition rejectXchgPairImpl 
  ( pubkey :  uint256 ) 
  ( xchg_pair_listing_requests :  xchg_pairs_map ) 
  ( listing_cfg :  ListingConfigLRecord ): 
  UExpression xchg_pairs_map true . 
          refine {{ new 'opt_req_info : ( optional XchgPairListingRequestLRecord ) @ "opt_req_info" := 
                  (#{xchg_pair_listing_requests}) -> extract (#{pubkey}) ; { _ } }} .  
         refine {{ require_ ( !{ opt_req_info } ,  error_code::xchg_pair_not_requested  ) ; { _ } }} . 
         refine {{ new 'req_info : ( XchgPairListingRequestLRecord ) @ "req_info" := 
                    (!{opt_req_info}) -> get () ; { _ } }} . 
          refine {{ new 'remaining_funds : uint128 @ "remaining_funds" := 
            ( (!{req_info}) ↑ XchgPairListingRequest.client_funds )
                   - ( (#{listing_cfg}) ↑ ListingConfig.reject_pair_cost ) ; { _ } }} .  
   refine {{ IListingAnswerPtr [[  !{req_info} ↑ XchgPairListingRequest.client_addr ]]
            with [$ !{remaining_funds} ⇒ { Messsage_ι_value } $]  ⤳ .onXchgPairRejected ( #{pubkey} ) ; {_} }}.   
         refine {{ return_ #{xchg_pair_listing_requests} }} . 
   Defined . 
Opaque uhmap_fetch.
Section rejectXchgPairImpl.
Definition rejectXchgPairImpl_exec_P (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ): 
{l' | l' = exec_state (Uinterpreter (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg )) l}.
  generate_proof (exec_expression l (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg )).
Defined.
Definition rejectXchgPairImpl_auto_exec_ (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord )
: Ledger.
intros. destruct (rejectXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests listing_cfg).
exact x. (* 
 term_of (rejectXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests listing_cfg ). *)
Defined.

Definition rejectXchgPairImpl_auto_exec (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord )
: Ledger.
intros.
let t1 := (eval unfold rejectXchgPairImpl_auto_exec_ in (rejectXchgPairImpl_auto_exec_ l pubkey xchg_pair_listing_requests listing_cfg)) in 
let t2 := eval unfold rejectXchgPairImpl_exec_P in t1 in exact t2.
Defined.
Print rejectXchgPairImpl_auto_exec.
Eval unfold rejectXchgPairImpl_auto_exec_ in rejectXchgPairImpl_auto_exec_ l pubkey xchg_pair_listing_requests listing_cfg.
intros. destruct (rejectXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests listing_cfg).
exact x. (* 
 term_of (rejectXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests listing_cfg ). *)
Defined.

Theorem rejectXchgPairImpl_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ) :
  rejectXchgPairImpl_auto_exec l pubkey xchg_pair_listing_requests listing_cfg =
  exec_state (Uinterpreter (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)) l.
Proof.
  intros. proof_of (rejectXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests listing_cfg).
Qed.



Ltac generate_proof gen :=
  let e := fresh "e" in
  let H := fresh "H" in
  let gen_nf := eval hnf in gen in
  generate_both gen_nf e H; cycle -1;
  (only 1: (exists e; subst e; reflexivity));
  eexists; reflexivity.

  Definition rejectXchgPairImpl 
  ( pubkey :  uint256 ) 
  ( xchg_pair_listing_requests :  xchg_pairs_map ) 
  ( listing_cfg :  ListingConfigLRecord ) : 
  UExpression xchg_pairs_map true . 
         refine {{ new 'opt_req_info : ( optional XchgPairListingRequestLRecord ) @ "opt_req_info" := 
                  (#{xchg_pair_listing_requests}) -> extract (#{pubkey}) ; { _ } }} . 
         refine {{ require_ ( !{ opt_req_info } ,  error_code::xchg_pair_not_requested  ) ; { _ } }} . 
         refine {{ new 'req_info : ( XchgPairListingRequestLRecord ) @ "req_info" := 
                    (!{opt_req_info}) -> get () ; { _ } }} . 
         refine {{ new 'remaining_funds : uint128 @ "remaining_funds" := 
            ( (!{req_info}) ↑ XchgPairListingRequest.client_funds )
                   - ( (#{listing_cfg}) ↑ ListingConfig.reject_pair_cost ) ; { _ } }} . 
(*   refine {{ IListingAnswerPtr [[  !{req_info} ↑ XchgPairListingRequest.client_addr ]]
            with [$ !{remaining_funds} ⇒ { Messsage_ι_value } $]  ⤳ .onXchgPairRejected ( #{pubkey} ) ; {_} }}.  *) 
         refine {{ return_ #{xchg_pair_listing_requests} }} . 
   Defined . 

Section rejectXchgPairImpl.
Definition rejectXchgPairImpl_exec_P (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ): 
{l' | l' = exec_state (Uinterpreter (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)) l}.
  generate_proof (exec_expression l (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)).
Defined.
Definition rejectXchgPairImpl_auto_exec (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ): Ledger.
intros. term_of (rejectXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests listing_cfg).
Defined.
Theorem rejectXchgPairImpl_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ) :
  rejectXchgPairImpl_auto_exec l pubkey xchg_pair_listing_requests listing_cfg =
  exec_state (Uinterpreter (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)) l.
Proof.
  intros. proof_of (rejectXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests listing_cfg).
Qed.


About new_lvalue.
(* ----------------------------------------- *)
Section Constructor.
Definition constructor_exec_P (l : Ledger) 
( deployer_pubkey :  ( uint256 ) )
( ownership_description :  ( XString ) )
( owner_address :  ( optional address ) )
( tons_cfg :  ( TonsConfigLRecord ) )
( deals_limit :  ( uint8 ) )
( listing_cfg :  ( ListingConfigLRecord ) ): 
{l' | l' = exec_state (Uinterpreter (constructor deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg)) l}.
(* unfold constructor. repeat auto_build_P. Unset Printing Notations. About URScalar. About sRReader.
all :lazymatch goal with
  | |- {t : ?T | t = toValue (eval_state (sRReader (URScalar ?v) ) ?l)} =>
    lazymatch type of v with
    | _ => exists v; apply R_scalar_eval_false_P_helper
    end
  end.
  exists deployer_pubkey. apply R_scalar_eval_false_P_helper. *)
  generate_proof (exec_expression l (constructor deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg)).
Defined.
Definition constructor_auto_exec (l : Ledger) 
( deployer_pubkey :  ( uint256 ) )
( ownership_description :  ( XString ) )
( owner_address :  ( optional address ) )
( tons_cfg :  ( TonsConfigLRecord ) )
( deals_limit :  ( uint8 ) )
( listing_cfg :  ( ListingConfigLRecord ) ): Ledger.
intros. term_of (constructor_exec_P l deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg).
Defined.
Theorem constructor_exec_proof_next (l : Ledger) 
( deployer_pubkey :  ( uint256 ) )
( ownership_description :  ( XString ) )
( owner_address :  ( optional address ) )
( tons_cfg :  ( TonsConfigLRecord ) )
( deals_limit :  ( uint8 ) )
( listing_cfg :  ( ListingConfigLRecord ) ) :
  constructor_auto_exec l deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg =
  exec_state (Uinterpreter (constructor deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg)) l.
Proof.
  intros. proof_of (constructor_exec_P l deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg).
Qed.
(* no eval*)
Print  constructor_auto_exec.
End Constructor.
(* ----------------------------------------- *)
Section setSpecificCode.
(* !!! 
no translate
*)
End setSpecificCode.
(* ----------------------------------------- *)
Section setPairCode.
Definition setPairCode_exec_P (l : Ledger) ( code :  TvmCells.cell  ): 
{l' | l' = exec_state (Uinterpreter (setPairCode code)) l}.
  generate_proof (exec_expression l (setPairCode code)).
Defined.
Definition setPairCode_auto_exec (l : Ledger) ( code :  TvmCells.cell  ): Ledger.
intros. term_of (setPairCode_exec_P l code).
Defined.
Theorem setPairCode_exec_proof_next (l : Ledger) ( code :  TvmCells.cell  ) :
  setPairCode_auto_exec l code =
  exec_state (Uinterpreter (setPairCode code)) l.
Proof.
  intros. proof_of (setPairCode_exec_P l code).
Qed.
(* no eval*)
End setPairCode.
(* ----------------------------------------- *)
Section setXchgPairCode.
Definition setXchgPairCode_exec_P (l : Ledger) ( code :  TvmCells.cell  ): 
{l' | l' = exec_state (Uinterpreter (setXchgPairCode code)) l}.
  generate_proof (exec_expression l (setXchgPairCode code)).
Defined.
Definition setXchgPairCode_auto_exec (l : Ledger) ( code :  TvmCells.cell  ): Ledger.
intros. term_of (setXchgPairCode_exec_P l code).
Defined.
Theorem setXchgPairCode_exec_proof_next (l : Ledger) ( code :  TvmCells.cell  ) :
  setXchgPairCode_auto_exec l code =
  exec_state (Uinterpreter (setXchgPairCode code)) l.
Proof.
  intros. proof_of (setXchgPairCode_exec_P l code).
Qed.
(* no eval*)
End setXchgPairCode.
(* ----------------------------------------- *)
Section setWrapperCode.
Definition setWrapperCode_exec_P (l : Ledger) ( code :  TvmCells.cell  ): 
{l' | l' = exec_state (Uinterpreter (setWrapperCode code)) l}.
  generate_proof (exec_expression l (setWrapperCode code)).
Defined.
Definition setWrapperCode_auto_exec (l : Ledger) ( code :  TvmCells.cell  ): Ledger.
intros. term_of (setWrapperCode_exec_P l code).
Defined.
Theorem setWrapperCode_exec_proof_next (l : Ledger) ( code :  TvmCells.cell  ) :
  setWrapperCode_auto_exec l code =
  exec_state (Uinterpreter (setWrapperCode code)) l.
Proof.
  intros. proof_of (setWrapperCode_exec_P l code).
Qed.
(* no eval*)
End setWrapperCode.
(* ----------------------------------------- *)
Section setPriceCode.
Definition setPriceCode_exec_P (l : Ledger) ( code :  TvmCells.cell  ): 
{l' | l' = exec_state (Uinterpreter (setPriceCode code)) l}.
  generate_proof (exec_expression l (setPriceCode code)).
Defined.
Definition setPriceCode_auto_exec (l : Ledger) ( code :  TvmCells.cell  ): Ledger.
intros. term_of (setPriceCode_exec_P l code).
Defined.
Theorem setPriceCode_exec_proof_next (l : Ledger) ( code :  TvmCells.cell  ) :
  setPriceCode_auto_exec l code =
  exec_state (Uinterpreter (setPriceCode code)) l.
Proof.
  intros. proof_of (setPriceCode_exec_P l code).
Qed.
(* no eval*)
End setPriceCode.
(* ----------------------------------------- *)
Section setXchgPriceCode.
Definition setXchgPriceCode_exec_P (l : Ledger) ( code :  TvmCells.cell  ): 
{l' | l' = exec_state (Uinterpreter (setXchgPriceCode code)) l}.
  generate_proof (exec_expression l (setXchgPriceCode code)).
Defined.
Definition setXchgPriceCode_auto_exec (l : Ledger) ( code :  TvmCells.cell  ): Ledger.
intros. term_of (setXchgPriceCode_exec_P l code).
Defined.
Theorem setXchgPriceCode_exec_proof_next (l : Ledger) ( code :  TvmCells.cell  ) :
  setXchgPriceCode_auto_exec l code =
  exec_state (Uinterpreter (setXchgPriceCode code)) l.
Proof.
  intros. proof_of (setXchgPriceCode_exec_P l code).
Qed.
(* no eval*)
End setXchgPriceCode.
(* ----------------------------------------- *)
Section setExtWalletCode.
Definition setExtWalletCode_exec_P (l : Ledger) ( code :  TvmCells.cell  ): 
{l' | l' = exec_state (Uinterpreter (setExtWalletCode code)) l}.
  generate_proof (exec_expression l (setExtWalletCode code)).
Defined.
Definition setExtWalletCode_auto_exec (l : Ledger) ( code :  TvmCells.cell  ): Ledger.
intros. term_of (setExtWalletCode_exec_P l code).
Defined.
Theorem setExtWalletCode_exec_proof_next (l : Ledger) ( code :  TvmCells.cell  ) :
  setExtWalletCode_auto_exec l code =
  exec_state (Uinterpreter (setExtWalletCode code)) l.
Proof.
  intros. proof_of (setExtWalletCode_exec_P l code).
Qed.
(* no eval*)
End setExtWalletCode.
(* ----------------------------------------- *)
Section setFlexWalletCode.
Definition setFlexWalletCode_exec_P (l : Ledger) ( code :  TvmCells.cell  ): 
{l' | l' = exec_state (Uinterpreter (setFlexWalletCode code)) l}.
  generate_proof (exec_expression l (setFlexWalletCode code)).
Defined.
Definition setFlexWalletCode_auto_exec (l : Ledger) ( code :  TvmCells.cell  ): Ledger.
intros. term_of (setFlexWalletCode_exec_P l code).
Defined.
Theorem setFlexWalletCode_exec_proof_next (l : Ledger) ( code :  TvmCells.cell  ) :
  setFlexWalletCode_auto_exec l code =
  exec_state (Uinterpreter (setFlexWalletCode code)) l.
Proof.
  intros. proof_of (setFlexWalletCode_exec_P l code).
Qed.
(* no eval*) 
End setFlexWalletCode.
(* ----------------------------------------- *)
Section check_owner.
Definition check_owner_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (check_owner )) l}.
unfold check_owner. repeat auto_build_P. all : eexists; reflexivity.
(* About new_lvalue.
lazymatch goal with
| |- {t | t = eval_state (@new_lvalue ?X ?Hloc ?Hdef ?s) ?l} =>
  exists (ULIndex (URScalar (s, @new_local_index X Hloc Hdef s l))
    (@local_state_lheap X Hloc));
  apply (@NL_new_lvalue_eval_P_helper X Hloc Hdef)
end.
NL_new_lvalue_eval_P.
  generate_proof (exec_expression l (check_owner )). *)
Defined.
Definition check_owner_auto_exec (l : Ledger) : Ledger.
intros. term_of (check_owner_exec_P l ).
Defined.
Theorem check_owner_exec_proof_next (l : Ledger)  :
  check_owner_auto_exec l  =
  exec_state (Uinterpreter (check_owner )) l.
Proof.
  intros. proof_of (check_owner_exec_P l ).
Qed.
(* no eval*)
End check_owner.
(* ----------------------------------------- *)
Section transfer.
Definition transfer_exec_P (l : Ledger) ( tto : address ) ( crystals :  uint128 ): 
{l' | l' = exec_state (Uinterpreter (transfer tto crystals)) l}.
  generate_proof (exec_expression l (transfer tto crystals)).
Defined.
Definition transfer_auto_exec (l : Ledger) ( tto : address ) ( crystals :  uint128 ): Ledger.
intros. term_of (transfer_exec_P l tto crystals).
Defined.
Theorem transfer_exec_proof_next (l : Ledger) ( tto : address ) ( crystals :  uint128 ) :
  transfer_auto_exec l tto crystals =
  exec_state (Uinterpreter (transfer tto crystals)) l.
Proof.
  intros. proof_of (transfer_exec_P l tto crystals).
Qed.
(* no eval *)
End transfer.
(* ----------------------------------------- *)
Section prepare_trading_pair_state_init_and_addr.
Definition prepare_trading_pair_state_init_and_addr_exec_P (l : Ledger) ( pair_data :  TradingPairClassTypesModule.DTradingPairLRecord ) 
( pair_code :  TvmCells.cell ): 
{l' | l' = exec_state (Uinterpreter (prepare_trading_pair_state_init_and_addr pair_data pair_code)) l}.
  unfold prepare_trading_pair_state_init_and_addr. repeat auto_build_P. all : eexists; reflexivity. 
  (* generate_proof (exec_expression l (prepare_trading_pair_state_init_and_addr pair_data pair_code)). *)
Defined.
Definition prepare_trading_pair_state_init_and_addr_auto_exec (l : Ledger) ( pair_data :  TradingPairClassTypesModule.DTradingPairLRecord ) 
( pair_code :  TvmCells.cell ): Ledger.
intros. term_of (prepare_trading_pair_state_init_and_addr_exec_P l pair_data pair_code).
Defined.
Theorem prepare_trading_pair_state_init_and_addr_exec_proof_next (l : Ledger) ( pair_data :  TradingPairClassTypesModule.DTradingPairLRecord ) 
( pair_code :  TvmCells.cell) :
  prepare_trading_pair_state_init_and_addr_auto_exec l pair_data pair_code =
  exec_state (Uinterpreter (prepare_trading_pair_state_init_and_addr pair_data pair_code)) l.
Proof. 
Opaque builder_build_.  intros.
destruct (prepare_trading_pair_state_init_and_addr_exec_P l pair_data pair_code) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (prepare_trading_pair_state_init_and_addr_exec_P l pair_data pair_code) in e').
unfold prepare_trading_pair_state_init_and_addr_exec_P.
  reflexivity.
  rewrite E. reflexivity.
  (* 
 proof_of (prepare_trading_pair_state_init_and_addr_exec_P l pair_data pair_code). *)
Qed.
Definition prepare_trading_pair_state_init_and_addr_eval_P (l : Ledger) ( pair_data :  TradingPairClassTypesModule.DTradingPairLRecord ) 
( pair_code :  TvmCells.cell): 
{v | v = toValue (eval_state (Uinterpreter (prepare_trading_pair_state_init_and_addr pair_data pair_code)) l)}.
unfold prepare_trading_pair_state_init_and_addr. repeat auto_build_P. all : eexists; reflexivity.
Defined.
Definition prepare_trading_pair_state_init_and_addr_auto_eval (l : Ledger) ( pair_data :  TradingPairClassTypesModule.DTradingPairLRecord ) 
( pair_code :  TvmCells.cell): ( StateInitLRecord # uint256 ).
intros. term_of (prepare_trading_pair_state_init_and_addr_eval_P l pair_data pair_code).
Defined.
Print prepare_trading_pair_state_init_and_addr_auto_eval.
Theorem prepare_trading_pair_state_init_and_addr_eval_proof_next (l : Ledger) ( pair_data :  TradingPairClassTypesModule.DTradingPairLRecord ) 
( pair_code :  TvmCells.cell) :
  prepare_trading_pair_state_init_and_addr_auto_eval l pair_data pair_code =
  toValue (eval_state (Uinterpreter (prepare_trading_pair_state_init_and_addr pair_data pair_code)) l).
Proof.
  intros. 
  unfold prepare_trading_pair_state_init_and_addr. 
  reflexivity.
  (* rewrite E. reflexivity. *)
  (* proof_of (prepare_trading_pair_state_init_and_addr_eval_P l pair_data pair_code). *)
Qed.
End prepare_trading_pair_state_init_and_addr.
(* ----------------------------------------- *)

Section prepare_trading_pair.
Definition prepare_trading_pair_exec_P (l : Ledger) ( flex : address ) 
                                 ( tip3_root : address ) 
                                 ( pair_code : TvmCells.cell): 
{l' | l' = exec_state (Uinterpreter (prepare_trading_pair flex tip3_root pair_code)) l}.
(* unfold prepare_trading_pair. repeat auto_build_P. all : eexists; reflexivity. *)
  generate_proof (exec_expression l (prepare_trading_pair flex tip3_root pair_code)).
Defined.
Definition prepare_trading_pair_auto_exec (l : Ledger) ( flex : address ) 
                                 ( tip3_root : address ) 
                                 ( pair_code : TvmCells.cell): Ledger.
intros. term_of (prepare_trading_pair_exec_P l flex tip3_root pair_code).
Defined.
Theorem prepare_trading_pair_exec_proof_next (l : Ledger) ( flex : address ) 
                                 ( tip3_root : address ) 
                                 ( pair_code : TvmCells.cell) :
  prepare_trading_pair_auto_exec l flex tip3_root pair_code =
  exec_state (Uinterpreter (prepare_trading_pair flex tip3_root pair_code)) l.
Proof.
  intros. proof_of (prepare_trading_pair_exec_P l flex tip3_root pair_code).
Qed.
Definition prepare_trading_pair_eval_P (l : Ledger) ( flex : address ) 
                                 ( tip3_root : address ) 
                                 ( pair_code : TvmCells.cell): 
{v | v = toValue (eval_state (Uinterpreter (prepare_trading_pair flex tip3_root pair_code)) l)}.
  generate_proof (eval_expression l (prepare_trading_pair flex tip3_root pair_code)).
Defined.
Definition prepare_trading_pair_auto_eval (l : Ledger) ( flex : address ) 
                                 ( tip3_root : address ) 
                                 ( pair_code : TvmCells.cell): ( StateInitLRecord * uint256 ).
intros. term_of (prepare_trading_pair_eval_P l flex tip3_root pair_code).
Defined.
Theorem prepare_trading_pair_eval_proof_next (l : Ledger) ( flex : address ) 
                                 ( tip3_root : address ) 
                                 ( pair_code : TvmCells.cell) :
  prepare_trading_pair_auto_eval l flex tip3_root pair_code =
  toValue (eval_state (Uinterpreter (prepare_trading_pair flex tip3_root pair_code)) l).
Proof.
  intros. proof_of_norm (prepare_trading_pair_eval_P l flex tip3_root pair_code).
Qed.
End prepare_trading_pair.
(* ----------------------------------------- *)
Section registerTradingPair.
Definition registerTradingPair_exec_P (l : Ledger) 
( pubkey :  ( uint256 ) ) ( tip3_root :  ( address ) ) ( min_amount :  ( uint128 ) ) ( notify_addr :  ( address ) ): 
{l' | l' = exec_state (Uinterpreter (registerTradingPair pubkey tip3_root min_amount notify_addr)) l}.
  generate_proof (exec_expression l (registerTradingPair pubkey tip3_root min_amount notify_addr)).
Defined.
Definition registerTradingPair_auto_exec (l : Ledger)
( pubkey :  ( uint256 ) ) ( tip3_root :  ( address ) ) ( min_amount :  ( uint128 ) ) ( notify_addr :  ( address ) ): Ledger.
intros. term_of (registerTradingPair_exec_P l pubkey tip3_root min_amount notify_addr).
Defined.
Theorem registerTradingPair_exec_proof_next (l : Ledger)
 ( pubkey :  ( uint256 ) ) ( tip3_root :  ( address ) ) ( min_amount :  ( uint128 ) ) ( notify_addr :  ( address ) ) :
  registerTradingPair_auto_exec l pubkey tip3_root min_amount notify_addr =
  exec_state (Uinterpreter (registerTradingPair pubkey tip3_root min_amount notify_addr)) l.
Proof.
  intros. proof_of (registerTradingPair_exec_P l pubkey tip3_root min_amount notify_addr).
Qed.
(* !!TODO eval true *)
Definition registerTradingPair_eval_P (l : Ledger) 
( pubkey :  ( uint256 ) ) ( tip3_root :  ( address ) ) ( min_amount :  ( uint128 ) ) ( notify_addr :  ( address ) ): 
{v | v =  (eval_state (Uinterpreter (registerTradingPair pubkey tip3_root min_amount notify_addr)) l)}.
  generate_proof (eval_expression l (registerTradingPair pubkey tip3_root min_amount notify_addr)).
Defined.
Definition registerTradingPair_auto_eval (l : Ledger)
( pubkey :  ( uint256 ) ) ( tip3_root :  ( address ) ) ( min_amount :  ( uint128 ) ) ( notify_addr :  ( address ) ): ControlResult address true.
intros. term_of (registerTradingPair_eval_P l pubkey tip3_root min_amount notify_addr).
Defined.
Theorem registerTradingPair_eval_proof_next (l : Ledger)
 ( pubkey :  ( uint256 ) ) ( tip3_root :  ( address ) ) ( min_amount :  ( uint128 ) ) ( notify_addr :  ( address ) ) :
  registerTradingPair_auto_eval l pubkey tip3_root min_amount notify_addr =
   (eval_state (Uinterpreter (registerTradingPair pubkey tip3_root min_amount notify_addr)) l).
Proof.
  intros. proof_of (registerTradingPair_eval_P l pubkey tip3_root min_amount notify_addr).
Qed.
End registerTradingPair.
(* ----------------------------------------- *)
(* Section approveTradingPairImpl.
Definition approveTradingPairImpl_exec_P (l : Ledger) ( pubkey : uint256 )
                                  ( trading_pair_listing_requests : trading_pairs_map ) 
                                  ( pair_code : TvmCells.cell) 
                                  ( workchain_id : int ) 
                                  ( listing_cfg : ListingConfigLRecord ): 
{l' | l' = exec_state (Uinterpreter (approveTradingPairImpl pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg  )) l}.
  generate_proof (exec_expression l (approveTradingPairImpl pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg  )).
Defined.
Definition approveTradingPairImpl_auto_exec (l : Ledger) ( pubkey : uint256 )
                                  ( trading_pair_listing_requests : trading_pairs_map ) 
                                  ( pair_code : TvmCells.cell) 
                                  ( workchain_id : int ) 
                                  ( listing_cfg : ListingConfigLRecord ): Ledger.
intros. term_of (approveTradingPairImpl_exec_P l pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg  ).
Defined.
Theorem approveTradingPairImpl_exec_proof_next (l : Ledger) ( pubkey : uint256 )
                                  ( trading_pair_listing_requests : trading_pairs_map ) 
                                  ( pair_code : TvmCells.cell) 
                                  ( workchain_id : int ) 
                                  ( listing_cfg : ListingConfigLRecord ) :
  approveTradingPairImpl_auto_exec l pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg   =
  exec_state (Uinterpreter (approveTradingPairImpl pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg  )) l.
Proof.
  intros. proof_of (approveTradingPairImpl_exec_P l pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg  ).
Qed. *)
(* !TODO eval true*)
(* Definition approveTradingPairImpl_eval_P (l : Ledger) ( pubkey : uint256 )
                                  ( trading_pair_listing_requests : trading_pairs_map ) 
                                  ( pair_code : TvmCells.cell) 
                                  ( workchain_id : int ) 
                                  ( listing_cfg : ListingConfigLRecord ): 
{v | v =  (eval_state (Uinterpreter (approveTradingPairImpl pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg)) l)}.
  generate_proof (eval_expression l (approveTradingPairImpl pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg)).
Defined.
Definition approveTradingPairImpl_auto_eval (l : Ledger) ( pubkey : uint256 )
                                  ( trading_pair_listing_requests : trading_pairs_map ) 
                                  ( pair_code : TvmCells.cell) 
                                  ( workchain_id : int ) 
                                  ( listing_cfg : ListingConfigLRecord ): (ControlResult ( address * (trading_pairs_map ) ) true).
intros. term_of (approveTradingPairImpl_eval_P l pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg).
Defined.
Theorem approveTradingPairImpl_eval_proof_next (l : Ledger) ( pubkey : uint256 )
                                  ( trading_pair_listing_requests : trading_pairs_map ) 
                                  ( pair_code : TvmCells.cell) 
                                  ( workchain_id : int ) 
                                  ( listing_cfg : ListingConfigLRecord ) :
  approveTradingPairImpl_auto_eval l pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg =
   (eval_state (Uinterpreter (approveTradingPairImpl pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg)) l).
Proof.
  intros. proof_of (approveTradingPairImpl_eval_P l pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg).
Qed.

End approveTradingPairImpl. *)
(* ----------------------------------------- *)
(* Section approveTradingPair.
Definition approveTradingPair_exec_P (l : Ledger) ( pubkey :  uint256 ): 
{l' | l' = exec_state (Uinterpreter (approveTradingPair pubkey)) l}.
  generate_proof (exec_expression l (approveTradingPair pubkey)).
Defined.
Definition approveTradingPair_auto_exec (l : Ledger) ( pubkey :  uint256 ): Ledger.
intros. term_of (approveTradingPair_exec_P l pubkey).
Defined.
Theorem approveTradingPair_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  approveTradingPair_auto_exec l pubkey =
  exec_state (Uinterpreter (approveTradingPair pubkey)) l.
Proof.
  intros. proof_of (approveTradingPair_exec_P l pubkey).
Qed.
(* 
!TODO eval true *)
Definition approveTradingPair_eval_P (l : Ledger) ( pubkey :  uint256 ): 
{v | v =  (eval_state (Uinterpreter (approveTradingPair pubkey)) l)}.
  generate_proof (eval_expression l (approveTradingPair pubkey)).
Defined.
Definition approveTradingPair_auto_eval (l : Ledger) ( pubkey :  uint256 ): ControlResult address true.
intros. term_of (approveTradingPair_eval_P l pubkey).
Defined.
Theorem approveTradingPair_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  approveTradingPair_auto_eval l pubkey =
   (eval_state (Uinterpreter (approveTradingPair pubkey)) l).
Proof.
  intros. proof_of (approveTradingPair_eval_P l pubkey).
Qed.
End approveTradingPair. *)
(* ----------------------------------------- *)
Section rejectTradingPairImpl.
Definition rejectTradingPairImpl_exec_P (l : Ledger) ( pubkey : uint256 ) 
                                 ( trading_pair_listing_requests : trading_pairs_map ) 
                                 ( listing_cfg :  ListingConfigLRecord ): 
{l' | l' = exec_state (Uinterpreter (rejectTradingPairImpl pubkey trading_pair_listing_requests listing_cfg)) l}.
  generate_proof (exec_expression l (rejectTradingPairImpl pubkey trading_pair_listing_requests listing_cfg)).
Defined.
Definition rejectTradingPairImpl_auto_exec (l : Ledger) ( pubkey : uint256 ) 
                                 ( trading_pair_listing_requests : trading_pairs_map ) 
                                 ( listing_cfg :  ListingConfigLRecord ): Ledger.
intros. term_of (rejectTradingPairImpl_exec_P l pubkey trading_pair_listing_requests listing_cfg).
Defined.
Theorem rejectTradingPairImpl_exec_proof_next (l : Ledger) ( pubkey : uint256 ) 
                                 ( trading_pair_listing_requests : trading_pairs_map ) 
                                 ( listing_cfg :  ListingConfigLRecord ) :
  rejectTradingPairImpl_auto_exec l pubkey trading_pair_listing_requests listing_cfg =
  exec_state (Uinterpreter (rejectTradingPairImpl pubkey trading_pair_listing_requests listing_cfg)) l.
Proof.
  intros. proof_of (rejectTradingPairImpl_exec_P l pubkey trading_pair_listing_requests listing_cfg).
Qed.
(*  
TODO eval true *)
Definition rejectTradingPairImpl_eval_P (l : Ledger) ( pubkey : uint256 ) 
                                 ( trading_pair_listing_requests : trading_pairs_map ) 
                                 ( listing_cfg :  ListingConfigLRecord ): 
{v | v =  (eval_state (Uinterpreter (rejectTradingPairImpl pubkey trading_pair_listing_requests listing_cfg)) l)}.
  generate_proof (eval_expression l (rejectTradingPairImpl pubkey trading_pair_listing_requests listing_cfg)).
Defined.
Definition rejectTradingPairImpl_auto_eval (l : Ledger) ( pubkey : uint256 ) 
                                 ( trading_pair_listing_requests : trading_pairs_map ) 
                                 ( listing_cfg :  ListingConfigLRecord ): ControlResult (trading_pairs_map ) true.
intros. term_of (rejectTradingPairImpl_eval_P l pubkey trading_pair_listing_requests listing_cfg).
Defined.
Theorem rejectTradingPairImpl_eval_proof_next (l : Ledger) ( pubkey : uint256 ) 
                                 ( trading_pair_listing_requests : trading_pairs_map ) 
                                 ( listing_cfg :  ListingConfigLRecord ) :
  rejectTradingPairImpl_auto_eval l pubkey trading_pair_listing_requests listing_cfg =
   (eval_state (Uinterpreter (rejectTradingPairImpl pubkey trading_pair_listing_requests listing_cfg)) l).
Proof.
  intros. proof_of (rejectTradingPairImpl_eval_P l pubkey trading_pair_listing_requests listing_cfg).
Qed.

End rejectTradingPairImpl.
(* ----------------------------------------- *)
Section rejectTradingPair.
Definition rejectTradingPair_exec_P (l : Ledger) ( pubkey :  uint256 ): 
{l' | l' = exec_state (Uinterpreter (rejectTradingPair pubkey)) l}.
  generate_proof (exec_expression l (rejectTradingPair pubkey)).
Defined.
Definition rejectTradingPair_auto_exec (l : Ledger) ( pubkey :  uint256 ): Ledger.
intros. term_of (rejectTradingPair_exec_P l pubkey).
Defined.
Theorem rejectTradingPair_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  rejectTradingPair_auto_exec l pubkey =
  exec_state (Uinterpreter (rejectTradingPair pubkey)) l.
Proof.
  intros. proof_of (rejectTradingPair_exec_P l pubkey).
Qed.
(*
TODO eval true *)
Definition rejectTradingPair_eval_P (l : Ledger) ( pubkey :  uint256 ): 
{v | v =  (eval_state (Uinterpreter (rejectTradingPair pubkey)) l)}.
  generate_proof (eval_expression l (rejectTradingPair pubkey)).
Defined.
Definition rejectTradingPair_auto_eval (l : Ledger) ( pubkey :  uint256 ): ControlResult XBool true.
intros. term_of (rejectTradingPair_eval_P l pubkey).
Defined.
Theorem rejectTradingPair_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  rejectTradingPair_auto_eval l pubkey =
   (eval_state (Uinterpreter (rejectTradingPair pubkey)) l).
Proof.
  intros. proof_of (rejectTradingPair_eval_P l pubkey).
Qed.

End rejectTradingPair.
(* ----------------------------------------- *)
Section prepare_xchg_pair_state_init_and_addr.
Definition prepare_xchg_pair_state_init_and_addr_exec_P (l : Ledger) ( pair_data :  XchgPairClassTypesModule.DXchgPairLRecord ) 
                                                 ( pair_code :  TvmCells.cell): 
{l' | l' = exec_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l}.
  generate_proof (exec_expression l (prepare_xchg_pair_state_init_and_addr pair_data pair_code)).
Defined.
Definition prepare_xchg_pair_state_init_and_addr_auto_exec (l : Ledger) ( pair_data :  XchgPairClassTypesModule.DXchgPairLRecord ) 
                                                 ( pair_code :  TvmCells.cell): Ledger.
intros. term_of (prepare_xchg_pair_state_init_and_addr_exec_P l pair_data pair_code).
Defined.
Theorem prepare_xchg_pair_state_init_and_addr_exec_proof_next (l : Ledger) ( pair_data :  XchgPairClassTypesModule.DXchgPairLRecord ) 
                                                 ( pair_code :  TvmCells.cell) :
  prepare_xchg_pair_state_init_and_addr_auto_exec l pair_data pair_code =
  exec_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l.
Proof.
  intros. proof_of (prepare_xchg_pair_state_init_and_addr_exec_P l pair_data pair_code).
Qed.
Definition prepare_xchg_pair_state_init_and_addr_eval_P (l : Ledger) ( pair_data :  XchgPairClassTypesModule.DXchgPairLRecord ) 
                                                 ( pair_code :  TvmCells.cell): 
{v | v = toValue (eval_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l)}.
  generate_proof (eval_expression l (prepare_xchg_pair_state_init_and_addr pair_data pair_code)).
Defined.
Definition prepare_xchg_pair_state_init_and_addr_auto_eval (l : Ledger) ( pair_data :  XchgPairClassTypesModule.DXchgPairLRecord ) 
                                                 ( pair_code :  TvmCells.cell): ( StateInitLRecord # uint256 ).
intros. term_of (prepare_xchg_pair_state_init_and_addr_eval_P l pair_data pair_code).
Defined.
Theorem prepare_xchg_pair_state_init_and_addr_eval_proof_next (l : Ledger) ( pair_data :  XchgPairClassTypesModule.DXchgPairLRecord ) 
                                                 ( pair_code :  TvmCells.cell) :
  prepare_xchg_pair_state_init_and_addr_auto_eval l pair_data pair_code =
  toValue (eval_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l).
Proof.
  intros. proof_of (prepare_xchg_pair_state_init_and_addr_eval_P l pair_data pair_code).
Qed.
End prepare_xchg_pair_state_init_and_addr.

(* ----------------------------------------- *)
Section approveXchgPairImpl.
Definition approveXchgPairImpl_exec_P (l : Ledger) ( pubkey :  uint256 ) ( xchg_pair_listing_requests :  xchg_pairs_map ) 
                               ( xchg_pair_code :  TvmCells.cell) ( workchain_id :  int ) ( listing_cfg :  ListingConfigLRecord ): 
{l' | l' = exec_state (Uinterpreter (approveXchgPairImpl pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg)) l}.
  generate_proof (exec_expression l (approveXchgPairImpl pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg)).
Defined.
Definition approveXchgPairImpl_auto_exec (l : Ledger) ( pubkey :  uint256 ) ( xchg_pair_listing_requests :  xchg_pairs_map ) 
                               ( xchg_pair_code :  TvmCells.cell) ( workchain_id :  int ) ( listing_cfg :  ListingConfigLRecord ): Ledger.
intros. term_of (approveXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg).
Defined.
Theorem approveXchgPairImpl_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) ( xchg_pair_listing_requests :  xchg_pairs_map ) 
                               ( xchg_pair_code :  TvmCells.cell) ( workchain_id :  int ) ( listing_cfg :  ListingConfigLRecord ) :
  approveXchgPairImpl_auto_exec l pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg =
  exec_state (Uinterpreter (approveXchgPairImpl pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg)) l.
Proof.
  intros. proof_of (approveXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg).
Qed.
(*
TODO eval true *)
Definition approveXchgPairImpl_eval_P (l : Ledger) ( pubkey :  uint256 ) ( xchg_pair_listing_requests :  xchg_pairs_map ) 
                               ( xchg_pair_code :  TvmCells.cell) ( workchain_id :  int ) ( listing_cfg :  ListingConfigLRecord ): 
{v | v =  (eval_state (Uinterpreter (approveXchgPairImpl pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg)) l)}.
  generate_proof (eval_expression l (approveXchgPairImpl pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg)).
Defined.
Definition approveXchgPairImpl_auto_eval (l : Ledger) ( pubkey :  uint256 ) ( xchg_pair_listing_requests :  xchg_pairs_map ) 
                               ( xchg_pair_code :  TvmCells.cell) ( workchain_id :  int ) ( listing_cfg :  ListingConfigLRecord ): ControlResult ( address # xchg_pairs_map ) true.
intros. term_of (approveXchgPairImpl_eval_P l pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg).
Defined.
Theorem approveXchgPairImpl_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) ( xchg_pair_listing_requests :  xchg_pairs_map ) 
                               ( xchg_pair_code :  TvmCells.cell) ( workchain_id :  int ) ( listing_cfg :  ListingConfigLRecord ) :
  approveXchgPairImpl_auto_eval l pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg =
   (eval_state (Uinterpreter (approveXchgPairImpl pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg)) l).
Proof.
  intros. proof_of (approveXchgPairImpl_eval_P l pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg).
Qed.

End approveXchgPairImpl.
(* ----------------------------------------- *)
Section rejectXchgPairImpl.
Definition rejectXchgPairImpl_exec_P (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ): 
{l' | l' = exec_state (Uinterpreter (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)) l}.
  generate_proof (exec_expression l (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)).
Defined.
Definition rejectXchgPairImpl_auto_exec (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ): Ledger.
intros. term_of (rejectXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests listing_cfg).
Defined.
Theorem rejectXchgPairImpl_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ) :
  rejectXchgPairImpl_auto_exec l pubkey xchg_pair_listing_requests listing_cfg =
  exec_state (Uinterpreter (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)) l.
Proof.
  intros. proof_of (rejectXchgPairImpl_exec_P l pubkey xchg_pair_listing_requests listing_cfg).
Qed.
(*
TODO eval true *)
Definition rejectXchgPairImpl_eval_P (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ): 
{v | v =  (eval_state (Uinterpreter (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)) l)}.
  generate_proof (eval_expression l (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)).
Defined.
Definition rejectXchgPairImpl_auto_eval (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ): ControlResult xchg_pairs_map true.
intros. term_of (rejectXchgPairImpl_eval_P l pubkey xchg_pair_listing_requests listing_cfg).
Defined.
Theorem rejectXchgPairImpl_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ) :
  rejectXchgPairImpl_auto_eval l pubkey xchg_pair_listing_requests listing_cfg =
   (eval_state (Uinterpreter (rejectXchgPairImpl pubkey xchg_pair_listing_requests listing_cfg)) l).
Proof.
  intros. proof_of (rejectXchgPairImpl_eval_P l pubkey xchg_pair_listing_requests listing_cfg).
Qed.
End rejectXchgPairImpl.
(* ----------------------------------------- *)
Section prepare_wrapper_state_init_and_addr.
Definition prepare_wrapper_state_init_and_addr_exec_P (l : Ledger) ( wrapper_code :  TvmCells.cell) 
( wrapper_data :  ( WrapperClassTypesModule.DWrapperLRecord ) ): 
{l' | l' = exec_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l}.
  generate_proof (exec_expression l (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)).
Defined.
Definition prepare_wrapper_state_init_and_addr_auto_exec (l : Ledger) ( wrapper_code :  TvmCells.cell) 
( wrapper_data :  ( WrapperClassTypesModule.DWrapperLRecord ) ): Ledger.
intros. term_of (prepare_wrapper_state_init_and_addr_exec_P l wrapper_code wrapper_data).
Defined.
Theorem prepare_wrapper_state_init_and_addr_exec_proof_next (l : Ledger) ( wrapper_code :  TvmCells.cell) 
( wrapper_data :  ( WrapperClassTypesModule.DWrapperLRecord ) ) :
  prepare_wrapper_state_init_and_addr_auto_exec l wrapper_code wrapper_data =
  exec_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l.
Proof.
  intros. proof_of (prepare_wrapper_state_init_and_addr_exec_P l wrapper_code wrapper_data).
Qed.
Definition prepare_wrapper_state_init_and_addr_eval_P (l : Ledger) ( wrapper_code :  TvmCells.cell) 
( wrapper_data :  ( WrapperClassTypesModule.DWrapperLRecord ) ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l)}.
  generate_proof (eval_expression l (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)).
Defined.
Definition prepare_wrapper_state_init_and_addr_auto_eval (l : Ledger) ( wrapper_code :  TvmCells.cell) 
( wrapper_data :  ( WrapperClassTypesModule.DWrapperLRecord ) ): ( StateInitLRecord * uint256 ).
intros. term_of (prepare_wrapper_state_init_and_addr_eval_P l wrapper_code wrapper_data).
Defined.
Theorem prepare_wrapper_state_init_and_addr_eval_proof_next (l : Ledger) ( wrapper_code :  TvmCells.cell) 
( wrapper_data :  ( WrapperClassTypesModule.DWrapperLRecord ) ) :
  prepare_wrapper_state_init_and_addr_auto_eval l wrapper_code wrapper_data =
  toValue (eval_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l).
Proof.
  intros. proof_of (prepare_wrapper_state_init_and_addr_eval_P l wrapper_code wrapper_data).
Qed.
End prepare_wrapper_state_init_and_addr.
(* ----------------------------------------- *)
Section prepare_external_wallet_state_init_and_addr.
Definition prepare_external_wallet_state_init_and_addr_exec_P (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) ) 
( decimals :  uint8 ) 
( root_public_key :  uint256 ) 
( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int ) : 
{l' | l' = exec_state (Uinterpreter (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l}.
  generate_proof (exec_expression l (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_external_wallet_state_init_and_addr_auto_exec (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) ) 
( decimals :  uint8 ) 
( root_public_key :  uint256 ) 
( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int ) : Ledger.
intros. term_of (prepare_external_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_external_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) ) 
( decimals :  uint8 ) 
( root_public_key :  uint256 ) 
( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int )  :
  prepare_external_wallet_state_init_and_addr_auto_exec l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  exec_state (Uinterpreter (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l.
Proof.
  intros. proof_of (prepare_external_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.
Definition prepare_external_wallet_state_init_and_addr_eval_P (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) ) 
( decimals :  uint8 ) 
( root_public_key :  uint256 ) 
( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int ) : 
{v | v = toValue (eval_state (Uinterpreter (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l)}.
  generate_proof (eval_expression l (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_external_wallet_state_init_and_addr_auto_eval (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) ) 
( decimals :  uint8 ) 
( root_public_key :  uint256 ) 
( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int ) : ( StateInitLRecord # uint256 ).
intros. term_of (prepare_external_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_external_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) ) 
( decimals :  uint8 ) 
( root_public_key :  uint256 ) 
( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int )  :
  prepare_external_wallet_state_init_and_addr_auto_eval l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  toValue (eval_state (Uinterpreter (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l).
Proof.
  intros. proof_of (prepare_external_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.
End prepare_external_wallet_state_init_and_addr.

(* ----------------------------------------- *)
Section approveWrapperImpl.

Definition approveWrapperImpl_exec_P (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  ( wrappers_map ) ) 
( wrapper_code :  TvmCells.cell) 
( ext_wallet_code :  TvmCells.cell) 
( flex_wallet_code :  TvmCells.cell) 
( workchain_id :  int ) 
( listing_cfg :  ListingConfigLRecord ): 
{l' | l' = exec_state (Uinterpreter (approveWrapperImpl pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg)) l}.
  generate_proof (exec_expression l (approveWrapperImpl pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg)).
Defined.
Definition approveWrapperImpl_auto_exec (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  ( wrappers_map ) ) 
( wrapper_code :  TvmCells.cell) 
( ext_wallet_code :  TvmCells.cell) 
( flex_wallet_code :  TvmCells.cell) 
( workchain_id :  int ) 
( listing_cfg :  ListingConfigLRecord ): Ledger.
intros. term_of (approveWrapperImpl_exec_P l pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg).
Defined.
Theorem approveWrapperImpl_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  ( wrappers_map ) ) 
( wrapper_code :  TvmCells.cell) 
( ext_wallet_code :  TvmCells.cell) 
( flex_wallet_code :  TvmCells.cell) 
( workchain_id :  int ) 
( listing_cfg :  ListingConfigLRecord ) :
  approveWrapperImpl_auto_exec l pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg =
  exec_state (Uinterpreter (approveWrapperImpl pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg)) l.
Proof.
  intros. (*!!!*)proof_of (approveWrapperImpl_exec_P l pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg).
Qed. 
(*
TODO eval true *)
Definition approveWrapperImpl_eval_P (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  ( wrappers_map ) ) 
( wrapper_code :  TvmCells.cell) 
( ext_wallet_code :  TvmCells.cell) 
( flex_wallet_code :  TvmCells.cell) 
( workchain_id :  int ) 
( listing_cfg :  ListingConfigLRecord ): 
{v | v =  (eval_state (Uinterpreter (approveWrapperImpl pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg)) l)}.
  generate_proof (eval_expression l (approveWrapperImpl pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg)).
Defined.
Definition approveWrapperImpl_auto_eval (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  ( wrappers_map ) ) 
( wrapper_code :  TvmCells.cell) 
( ext_wallet_code :  TvmCells.cell) 
( flex_wallet_code :  TvmCells.cell) 
( workchain_id :  int ) 
( listing_cfg :  ListingConfigLRecord ): ControlResult ( address # ( wrappers_map ) ) true.
intros. term_of (approveWrapperImpl_eval_P l pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg).
Defined.
Theorem approveWrapperImpl_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  ( wrappers_map ) ) 
( wrapper_code :  TvmCells.cell) 
( ext_wallet_code :  TvmCells.cell) 
( flex_wallet_code :  TvmCells.cell) 
( workchain_id :  int ) 
( listing_cfg :  ListingConfigLRecord ) :
  approveWrapperImpl_auto_eval l pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg =
   (eval_state (Uinterpreter (approveWrapperImpl pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg)) l).
Proof.
  intros. proof_of (approveWrapperImpl_eval_P l pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg).
Qed.

End approveWrapperImpl.
(* ----------------------------------------- *)
Section rejectWrapperImpl.
Definition rejectWrapperImpl_exec_P (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  (wrappers_map ) ) 
( listing_cfg :  ListingConfigLRecord ): 
{l' | l' = exec_state (Uinterpreter (rejectWrapperImpl pubkey wrapper_listing_requests listing_cfg)) l}.
  generate_proof (exec_expression l (rejectWrapperImpl pubkey wrapper_listing_requests listing_cfg)).
Defined.
Definition rejectWrapperImpl_auto_exec (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  (wrappers_map ) ) 
( listing_cfg :  ListingConfigLRecord ): Ledger.
intros. term_of (rejectWrapperImpl_exec_P l pubkey wrapper_listing_requests listing_cfg).
Defined.
Theorem rejectWrapperImpl_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  (wrappers_map ) ) 
( listing_cfg :  ListingConfigLRecord ) :
  rejectWrapperImpl_auto_exec l pubkey wrapper_listing_requests listing_cfg =
  exec_state (Uinterpreter (rejectWrapperImpl pubkey wrapper_listing_requests listing_cfg)) l.
Proof.
  intros. proof_of (rejectWrapperImpl_exec_P l pubkey wrapper_listing_requests listing_cfg).
Qed.
(*
TODO eval true *)
Definition rejectWrapperImpl_eval_P (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  (wrappers_map ) ) 
( listing_cfg :  ListingConfigLRecord ): 
{v | v =  (eval_state (Uinterpreter (rejectWrapperImpl pubkey wrapper_listing_requests listing_cfg)) l)}.
  generate_proof (eval_expression l (rejectWrapperImpl pubkey wrapper_listing_requests listing_cfg)).
Defined.
Definition rejectWrapperImpl_auto_eval (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  (wrappers_map ) ) 
( listing_cfg :  ListingConfigLRecord ): ControlResult (wrappers_map ) true.
intros. term_of (rejectWrapperImpl_eval_P l pubkey wrapper_listing_requests listing_cfg).
Defined.
Theorem rejectWrapperImpl_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) 
( wrapper_listing_requests :  (wrappers_map ) ) 
( listing_cfg :  ListingConfigLRecord ) :
  rejectWrapperImpl_auto_eval l pubkey wrapper_listing_requests listing_cfg =
   (eval_state (Uinterpreter (rejectWrapperImpl pubkey wrapper_listing_requests listing_cfg)) l).
Proof.
  intros. proof_of (rejectWrapperImpl_eval_P l pubkey wrapper_listing_requests listing_cfg).
Qed.
End rejectWrapperImpl.
(* ----------------------------------------- *)
Section registerXchgPair.
Definition registerXchgPair_exec_P (l : Ledger) ( pubkey :  uint256 ) ( tip3_major_root : address ) ( tip3_minor_root : address ) ( min_amount :  uint128 ) ( notify_addr : address ): 
{l' | l' = exec_state (Uinterpreter (registerXchgPair pubkey tip3_major_root tip3_minor_root min_amount notify_addr)) l}.
  generate_proof (exec_expression l (registerXchgPair pubkey tip3_major_root tip3_minor_root min_amount notify_addr)).
Defined.
Definition registerXchgPair_auto_exec (l : Ledger) ( pubkey :  uint256 ) ( tip3_major_root : address ) ( tip3_minor_root : address ) ( min_amount :  uint128 ) ( notify_addr : address ): Ledger.
intros. term_of (registerXchgPair_exec_P l pubkey tip3_major_root tip3_minor_root min_amount notify_addr).
Defined.
Theorem registerXchgPair_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) ( tip3_major_root : address ) ( tip3_minor_root : address ) ( min_amount :  uint128 ) ( notify_addr : address ) :
  registerXchgPair_auto_exec l pubkey tip3_major_root tip3_minor_root min_amount notify_addr =
  exec_state (Uinterpreter (registerXchgPair pubkey tip3_major_root tip3_minor_root min_amount notify_addr)) l.
Proof.
  intros. proof_of (registerXchgPair_exec_P l pubkey tip3_major_root tip3_minor_root min_amount notify_addr).
Qed.
(*
TODO eval true *)
Definition registerXchgPair_eval_P (l : Ledger) ( pubkey :  uint256 ) ( tip3_major_root : address ) ( tip3_minor_root : address ) ( min_amount :  uint128 ) ( notify_addr : address ): 
{v | v =  (eval_state (Uinterpreter (registerXchgPair pubkey tip3_major_root tip3_minor_root min_amount notify_addr)) l)}.
  generate_proof (eval_expression l (registerXchgPair pubkey tip3_major_root tip3_minor_root min_amount notify_addr)).
Defined.
Definition registerXchgPair_auto_eval (l : Ledger) ( pubkey :  uint256 ) ( tip3_major_root : address ) ( tip3_minor_root : address ) ( min_amount :  uint128 ) ( notify_addr : address ): ControlResult address true.
intros. term_of (registerXchgPair_eval_P l pubkey tip3_major_root tip3_minor_root min_amount notify_addr).
Defined.
Theorem registerXchgPair_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) ( tip3_major_root : address ) ( tip3_minor_root : address ) ( min_amount :  uint128 ) ( notify_addr : address ) :
  registerXchgPair_auto_eval l pubkey tip3_major_root tip3_minor_root min_amount notify_addr =
   (eval_state (Uinterpreter (registerXchgPair pubkey tip3_major_root tip3_minor_root min_amount notify_addr)) l).
Proof.
  intros. proof_of (registerXchgPair_eval_P l pubkey tip3_major_root tip3_minor_root min_amount notify_addr).
Qed.

End registerXchgPair.
(* ----------------------------------------- *)
Section approveXchgPair.
Definition approveXchgPair_exec_P (l : Ledger) ( pubkey :  uint256 ): 
{l' | l' = exec_state (Uinterpreter (approveXchgPair pubkey)) l}.
  generate_proof (exec_expression l (approveXchgPair pubkey)).
Defined.
Definition approveXchgPair_auto_exec (l : Ledger) ( pubkey :  uint256 ): Ledger.
intros. term_of (approveXchgPair_exec_P l pubkey).
Defined.
Theorem approveXchgPair_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  approveXchgPair_auto_exec l pubkey =
  exec_state (Uinterpreter (approveXchgPair pubkey)) l.
Proof.
  intros. proof_of (approveXchgPair_exec_P l pubkey).
Qed.
(*
TODO eval true *)
Definition approveXchgPair_eval_P (l : Ledger) ( pubkey :  uint256 ): 
{v | v =  (eval_state (Uinterpreter (approveXchgPair pubkey)) l)}.
  generate_proof (eval_expression l (approveXchgPair pubkey)).
Defined.
Definition approveXchgPair_auto_eval (l : Ledger) ( pubkey :  uint256 ):  ControlResult address true.
intros. term_of (approveXchgPair_eval_P l pubkey).
Defined.
Theorem approveXchgPair_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  approveXchgPair_auto_eval l pubkey =
   (eval_state (Uinterpreter (approveXchgPair pubkey)) l).
Proof.
  intros. proof_of (approveXchgPair_eval_P l pubkey).
Qed.

End approveXchgPair.
(* ----------------------------------------- *)
Section rejectXchgPair.
Definition rejectXchgPair_exec_P (l : Ledger) ( pubkey : uint256 ): 
{l' | l' = exec_state (Uinterpreter (rejectXchgPair pubkey)) l}.
  generate_proof (exec_expression l (rejectXchgPair pubkey)).
Defined.
Definition rejectXchgPair_auto_exec (l : Ledger) ( pubkey : uint256 ): Ledger.
intros. term_of (rejectXchgPair_exec_P l pubkey).
Defined.
Theorem rejectXchgPair_exec_proof_next (l : Ledger) ( pubkey : uint256 ) :
  rejectXchgPair_auto_exec l pubkey =
  exec_state (Uinterpreter (rejectXchgPair pubkey)) l.
Proof.
  intros. proof_of (rejectXchgPair_exec_P l pubkey).
Qed.
(*
TODO eval true *)
Definition rejectXchgPair_eval_P (l : Ledger) ( pubkey : uint256 ): 
{v | v =  (eval_state (Uinterpreter (rejectXchgPair pubkey)) l)}.
  generate_proof (eval_expression l (rejectXchgPair pubkey)).
Defined.
Definition rejectXchgPair_auto_eval (l : Ledger) ( pubkey : uint256 ):  ControlResult XBool true.
intros. term_of (rejectXchgPair_eval_P l pubkey).
Defined.
Theorem rejectXchgPair_eval_proof_next (l : Ledger) ( pubkey : uint256 ) :
  rejectXchgPair_auto_eval l pubkey =
   (eval_state (Uinterpreter (rejectXchgPair pubkey)) l).
Proof.
  intros. proof_of (rejectXchgPair_eval_P l pubkey).
Qed.
End rejectXchgPair.
(* ----------------------------------------- *)
Section registerWrapper.
Definition registerWrapper_exec_P (l : Ledger) ( pubkey :  uint256 ) ( tip3cfg :  ( Tip3ConfigLRecord ) ): 
{l' | l' = exec_state (Uinterpreter (registerWrapper pubkey tip3cfg)) l}.
  generate_proof (exec_expression l (registerWrapper pubkey tip3cfg)).
Defined.
Definition registerWrapper_auto_exec (l : Ledger) ( pubkey :  uint256 ) ( tip3cfg :  ( Tip3ConfigLRecord ) ): Ledger.
intros. term_of (registerWrapper_exec_P l pubkey tip3cfg).
Defined.
Theorem registerWrapper_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) ( tip3cfg :  ( Tip3ConfigLRecord ) ) :
  registerWrapper_auto_exec l pubkey tip3cfg =
  exec_state (Uinterpreter (registerWrapper pubkey tip3cfg)) l.
Proof.
  intros. proof_of (registerWrapper_exec_P l pubkey tip3cfg).
Qed.
(*
TODO eval true *)
Definition registerWrapper_eval_P (l : Ledger) ( pubkey :  uint256 ) ( tip3cfg :  ( Tip3ConfigLRecord ) ): 
{v | v =  (eval_state (Uinterpreter (registerWrapper pubkey tip3cfg)) l)}.
  generate_proof (eval_expression l (registerWrapper pubkey tip3cfg)).
Defined.
Definition registerWrapper_auto_eval (l : Ledger) ( pubkey :  uint256 ) ( tip3cfg :  ( Tip3ConfigLRecord ) ): ControlResult address true.
intros. term_of (registerWrapper_eval_P l pubkey tip3cfg).
Defined.
Theorem registerWrapper_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) ( tip3cfg :  ( Tip3ConfigLRecord ) ) :
  registerWrapper_auto_eval l pubkey tip3cfg =
   (eval_state (Uinterpreter (registerWrapper pubkey tip3cfg)) l).
Proof.
  intros. proof_of (registerWrapper_eval_P l pubkey tip3cfg).
Qed.
End registerWrapper.
(* ----------------------------------------- *)
Section approveWrapper.
Definition approveWrapper_exec_P (l : Ledger) ( pubkey :  uint256 ): 
{l' | l' = exec_state (Uinterpreter (approveWrapper pubkey)) l}.
  generate_proof (exec_expression l (approveWrapper pubkey)).
Defined.
Definition approveWrapper_auto_exec (l : Ledger) ( pubkey :  uint256 ): Ledger.
intros. term_of (approveWrapper_exec_P l pubkey).
Defined.
Theorem approveWrapper_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  approveWrapper_auto_exec l pubkey =
  exec_state (Uinterpreter (approveWrapper pubkey)) l.
Proof.
  intros. proof_of (approveWrapper_exec_P l pubkey).
Qed.
(*
TODO eval true *)
Definition approveWrapper_eval_P (l : Ledger) ( pubkey :  uint256 ): 
{v | v =  (eval_state (Uinterpreter (approveWrapper pubkey)) l)}.
  generate_proof (eval_expression l (approveWrapper pubkey)).
Defined.
Definition approveWrapper_auto_eval (l : Ledger) ( pubkey :  uint256 ): ControlResult address true.
intros. term_of (approveWrapper_eval_P l pubkey).
Defined.
Theorem approveWrapper_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  approveWrapper_auto_eval l pubkey =
   (eval_state (Uinterpreter (approveWrapper pubkey)) l).
Proof.
  intros. proof_of (approveWrapper_eval_P l pubkey).
Qed.
End approveWrapper.
(* ----------------------------------------- *)
Section rejectWrapper.
Definition rejectWrapper_exec_P (l : Ledger) ( pubkey :  uint256 ): 
{l' | l' = exec_state (Uinterpreter (rejectWrapper pubkey)) l}.
  generate_proof (exec_expression l (rejectWrapper pubkey)).
Defined.
Definition rejectWrapper_auto_exec (l : Ledger) ( pubkey :  uint256 ): Ledger.
intros. term_of (rejectWrapper_exec_P l pubkey).
Defined.
Theorem rejectWrapper_exec_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  rejectWrapper_auto_exec l pubkey =
  exec_state (Uinterpreter (rejectWrapper pubkey)) l.
Proof.
  intros. proof_of (rejectWrapper_exec_P l pubkey).
Qed.
(*
TODO eval true *)
Definition rejectWrapper_eval_P (l : Ledger) ( pubkey :  uint256 ): 
{v | v =  (eval_state (Uinterpreter (rejectWrapper pubkey)) l)}.
  generate_proof (eval_expression l (rejectWrapper pubkey)).
Defined.
Definition rejectWrapper_auto_eval (l : Ledger) ( pubkey :  uint256 ): ControlResult XBool true.
intros. term_of (rejectWrapper_eval_P l pubkey).
Defined.
Theorem rejectWrapper_eval_proof_next (l : Ledger) ( pubkey :  uint256 ) :
  rejectWrapper_auto_eval l pubkey =
   (eval_state (Uinterpreter (rejectWrapper pubkey)) l).
Proof.
  intros. proof_of (rejectWrapper_eval_P l pubkey).
Qed.

End rejectWrapper.
(* ----------------------------------------- *)
Section isFullyInitialized.
Lemma isFullyInitialized_exec : forall 
(s s0 : ContractLRecord)  (v : VMStateLRecord)  (m m0 : MessagesAndEventsLRecord) (l : LocalStateLRecord),
let ll : Ledger  := (s, (s0, (v, (m, (m0, (LocalStateDefault , l))))))%xprod in 
exec_state (Uinterpreter (isFullyInitialized  )) ll =  ll.
Proof.
    auto.
Qed.
Definition isFullyInitialized_eval_P (l : Ledger) : 
{v | v = toValue (eval_state (Uinterpreter (isFullyInitialized )) l)}.
  generate_proof (eval_expression l (isFullyInitialized )).
Defined.
Definition isFullyInitialized_auto_eval (l : Ledger) : XBool.
intros. term_of (isFullyInitialized_eval_P l ).
Defined.
Theorem isFullyInitialized_eval_proof_next (l : Ledger)  :
  isFullyInitialized_auto_eval l  =
  toValue (eval_state (Uinterpreter (isFullyInitialized )) l).
Proof.
  intros. proof_of (isFullyInitialized_eval_P l ).
Qed.

End isFullyInitialized.
(* ----------------------------------------- *)
Section prepare_flex_state_init_and_addr.
Definition prepare_flex_state_init_and_addr_exec_P (l : Ledger) ( flex_data :  (ContractLRecord ) ) 
                                             ( flex_code :  TvmCells.cell): 
{l' | l' = exec_state (Uinterpreter (prepare_flex_state_init_and_addr flex_data flex_code)) l}.
  generate_proof (exec_expression l (prepare_flex_state_init_and_addr flex_data flex_code)).
Defined.
Definition prepare_flex_state_init_and_addr_auto_exec (l : Ledger) ( flex_data :  (ContractLRecord ) ) 
                                             ( flex_code :  TvmCells.cell): Ledger.
intros. term_of (prepare_flex_state_init_and_addr_exec_P l flex_data flex_code).
Defined.
Theorem prepare_flex_state_init_and_addr_exec_proof_next (l : Ledger) ( flex_data :  (ContractLRecord ) ) 
                                             ( flex_code :  TvmCells.cell) :
  prepare_flex_state_init_and_addr_auto_exec l flex_data flex_code =
  exec_state (Uinterpreter (prepare_flex_state_init_and_addr flex_data flex_code)) l.
Proof.
  intros. proof_of (prepare_flex_state_init_and_addr_exec_P l flex_data flex_code).
Qed.
Definition prepare_flex_state_init_and_addr_eval_P (l : Ledger) ( flex_data :  (ContractLRecord ) ) 
                                             ( flex_code :  TvmCells.cell): 
{v | v = toValue (eval_state (Uinterpreter (prepare_flex_state_init_and_addr flex_data flex_code)) l)}.
  generate_proof (eval_expression l (prepare_flex_state_init_and_addr flex_data flex_code)).
Defined.
Definition prepare_flex_state_init_and_addr_auto_eval (l : Ledger) ( flex_data :  (ContractLRecord ) ) 
                                             ( flex_code :  TvmCells.cell): ( StateInitLRecord * uint256 ).
intros. term_of (prepare_flex_state_init_and_addr_eval_P l flex_data flex_code).
Defined.
Theorem prepare_flex_state_init_and_addr_eval_proof_next (l : Ledger) ( flex_data :  (ContractLRecord ) ) 
                                             ( flex_code :  TvmCells.cell) :
  prepare_flex_state_init_and_addr_auto_eval l flex_data flex_code =
  toValue (eval_state (Uinterpreter (prepare_flex_state_init_and_addr flex_data flex_code)) l).
Proof.
  intros. proof_of (prepare_flex_state_init_and_addr_eval_P l flex_data flex_code).
Qed.
End prepare_flex_state_init_and_addr.
(* ----------------------------------------- *)
Section prepare_internal_wallet_state_init_and_addr.
Definition prepare_internal_wallet_state_init_and_addr_exec_P (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  uint8 )
 ( root_public_key :  uint256 )
 ( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int ) : 
{l' | l' = exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l}.
  generate_proof (exec_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_exec (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  uint8 )
 ( root_public_key :  uint256 )
 ( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int ) : Ledger.
intros. term_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  uint8 )
 ( root_public_key :  uint256 )
 ( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int )  :
  prepare_internal_wallet_state_init_and_addr_auto_exec l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l.
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.
Definition prepare_internal_wallet_state_init_and_addr_eval_P (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  uint8 )
 ( root_public_key :  uint256 )
 ( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int ) : 
{v | v = toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l)}.
  generate_proof (eval_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_eval (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  uint8 )
 ( root_public_key :  uint256 )
 ( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int ) : ( StateInitLRecord * uint256 ).
intros. term_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  uint8 )
 ( root_public_key :  uint256 )
 ( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  TvmCells.cell) 
( workchain_id :  int )  :
  prepare_internal_wallet_state_init_and_addr_auto_eval l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l).
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.
End prepare_internal_wallet_state_init_and_addr.
End EvalExecAuto.
