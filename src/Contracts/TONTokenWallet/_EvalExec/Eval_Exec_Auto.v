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
Require Import UMLang.ExecGenerator.

Require Import UrsusTVM.Cpp.TvmCells.
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonTypes.
Require Import Project.CommonConstSig.
Require Import Project.CommonNotations.

Require Import TONTokenWallet.Ledger.
Require Import TONTokenWallet.ClassTypesNotations.
Require Import TONTokenWallet.ClassTypes.
Require Import TONTokenWallet.Functions.FuncSig.
Require Import TONTokenWallet.Functions.FuncNotations.
Require Import TONTokenWallet.Functions.Funcs.



Require TONTokenWallet.Interface.

(* Require Import TradingPair.ClassTypes.
Require Import XchgPair.ClassTypes.
Require Import Wrapper.ClassTypes.
Require Import TONTokenWallet.ClassTypes.
Require Import Wrapper.ClassTypesNotations. *)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.

Module EvalExecAuto (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .

Module Export FuncsModule := Funcs co dc.

Import FuncsInternal.

Import co.

(* Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

Module TradingPairClassTypes := TradingPair.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module XchgPairClassTypes := XchgPair.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module WrapperClassTypesModule := Wrapper.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module TONTokenWalletClassTypesModule := TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule.
 *)
(* Module Import TONTokenWalletModuleForTON := Contracts.TONTokenWallet.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import WrapperModuleForTON := Wrapper.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
 *)

(*  Module Import xxx := SpecModuleForFuncNotations.LedgerModuleForFuncSig.
 Module Import generator := execGenerator XTypesModule StateMonadModule xxx.
 *)
(* Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
  *)
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Ltac generate_proof gen :=
  let e := fresh "e" in
  let H := fresh "H" in
  let gen_nf := eval hnf in gen in
  generate_both gen_nf e H; cycle -1;
  (only 1: (exists e; subst e; reflexivity));
  eexists; reflexivity.

Ltac proof_of t :=
  let e := fresh "e" in
  let H := fresh "H" in
  let E := fresh "E" in
  destruct t as [e H] eqn:E; rewrite <- H; replace e with
  (let (e', _) := t in e');
  try reflexivity ;try (rewrite E; reflexivity).

(* Если proof_of падает, то меняем его на proof_of_norm
Если зависает, то меняем на destruct (funcname_exec_P l  arg arg) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (funcname_exec_P l  arg arg) in e').
unfold filter_lend_ownerhip_map_exec_P.
  reflexivity.
  rewrite E.
  reflexivity.

Если зависает term_of 
let t1 := (eval unfold funcname_exec_P in
(let (e, _) := funcname_exec_P l args in e)) in exact t1.
*)

Section filter_lend_ownerhip_map.
Definition filter_lend_ownerhip_map_exec_P (l : Ledger): 
{l' | l' = exec_state (Uinterpreter (filter_lend_ownerhip_map )) l}.
  generate_proof (exec_expression l (filter_lend_ownerhip_map )).
Defined.
Definition filter_lend_ownerhip_map_auto_exec (l : Ledger) : Ledger.
intros. term_of (filter_lend_ownerhip_map_exec_P l ).
Defined.
Theorem filter_lend_ownerhip_map_exec_proof_next (l : Ledger) :
filter_lend_ownerhip_map_auto_exec l  =
  exec_state (Uinterpreter (filter_lend_ownerhip_map )) l.
Proof.
  intros.
  destruct (filter_lend_ownerhip_map_exec_P l  ) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (filter_lend_ownerhip_map_exec_P l  ) in e').
unfold filter_lend_ownerhip_map_exec_P.
  reflexivity.
  rewrite E.
  reflexivity.
  (* proof_of (filter_lend_ownerhip_map_exec_P l ). *)
Qed.

(* For inside *)

(* Definition filter_lend_ownerhip_map_eval_P (l : Ledger) : 
{v | v = toValue (eval_state (Uinterpreter (filter_lend_ownerhip_map )) l)}.
  generate_proof (eval_expression l (filter_lend_ownerhip_map )).
Defined.
Definition filter_lend_ownerhip_map_auto_eval (l : Ledger) : (lend_ownership_map) # uint128.
intros. term_of (filter_lend_ownerhip_map_eval_P l ).
Defined.
Theorem filter_lend_ownerhip_map_eval_proof_next (l : Ledger) :
filter_lend_ownerhip_map_auto_eval l  =
  toValue (eval_state (Uinterpreter (filter_lend_ownerhip_map )) l).
Proof.
  intros. 
  destruct (filter_lend_ownerhip_map_eval_P l) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (filter_lend_ownerhip_map_eval_P l) in e').
unfold filter_lend_ownerhip_map_eval_P;
reflexivity.
  rewrite E. reflexivity.
  proof_of (filter_lend_ownerhip_map_eval_P l ).
Qed. *)



End filter_lend_ownerhip_map.

Section is_internal_owner.
Definition is_internal_owner_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (is_internal_owner )) l}.
  generate_proof (exec_expression l (is_internal_owner )).
Defined.
Definition is_internal_owner_auto_exec (l : Ledger) : Ledger.
intros. term_of (is_internal_owner_exec_P l ).
Defined.
Theorem is_internal_owner_exec_proof_next (l : Ledger)  :
is_internal_owner_auto_exec l  =
  exec_state (Uinterpreter (is_internal_owner )) l.
Proof.
  intros. proof_of (is_internal_owner_exec_P l ).
Qed.



Definition is_internal_owner_eval_P (l : Ledger) : 
{v | v = toValue (eval_state (Uinterpreter (is_internal_owner )) l)}.
  generate_proof (eval_expression l (is_internal_owner )).
Defined.
Definition is_internal_owner_auto_eval (l : Ledger) : boolean.
intros. term_of (is_internal_owner_eval_P l ).
Defined.
Theorem is_internal_owner_eval_proof_next (l : Ledger)  :
is_internal_owner_auto_eval l  =
  toValue (eval_state (Uinterpreter (is_internal_owner )) l).
Proof.
  intros. proof_of (is_internal_owner_eval_P l ).
Qed.

End is_internal_owner.


Section check_internal_owner.
Definition check_internal_owner_exec_P (l : Ledger) ( original_owner_only :  boolean )
( allowed_for_original_owner_in_lend_state :  boolean )
: 
{l' | l' = exec_state (Uinterpreter (check_internal_owner original_owner_only allowed_for_original_owner_in_lend_state)) l}.
  generate_proof (exec_expression l (check_internal_owner original_owner_only allowed_for_original_owner_in_lend_state)).
Defined.
Definition check_internal_owner_auto_exec (l : Ledger) ( original_owner_only :  boolean )
( allowed_for_original_owner_in_lend_state :  boolean ): Ledger.
intros. term_of (check_internal_owner_exec_P l original_owner_only allowed_for_original_owner_in_lend_state).
Defined.
Theorem check_internal_owner_exec_proof_next (l : Ledger) ( original_owner_only :  boolean )
( allowed_for_original_owner_in_lend_state :  boolean ) :
  check_internal_owner_auto_exec l original_owner_only allowed_for_original_owner_in_lend_state =
  exec_state (Uinterpreter (check_internal_owner original_owner_only allowed_for_original_owner_in_lend_state)) l.
Proof.
  intros.
  destruct (check_internal_owner_exec_P l original_owner_only allowed_for_original_owner_in_lend_state) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (check_internal_owner_exec_P l original_owner_only allowed_for_original_owner_in_lend_state) in e').
unfold check_internal_owner_exec_P;
reflexivity.
  rewrite E. reflexivity.
  (* proof_of (check_internal_owner_exec_P l original_owner_only allowed_for_original_owner_in_lend_state). *)
Qed.



Definition check_internal_owner_eval_P (l : Ledger) ( original_owner_only :  boolean )
( allowed_for_original_owner_in_lend_state :  boolean ): 
{v | v =  (eval_state (Uinterpreter (check_internal_owner original_owner_only allowed_for_original_owner_in_lend_state)) l)}.
  generate_proof (eval_expression l (check_internal_owner original_owner_only allowed_for_original_owner_in_lend_state)).
Defined.
Definition check_internal_owner_auto_eval (l : Ledger) ( original_owner_only :  boolean )
( allowed_for_original_owner_in_lend_state :  boolean ): (ControlResult uint128 true).
intros. term_of (check_internal_owner_eval_P l original_owner_only allowed_for_original_owner_in_lend_state).
Defined.
Theorem check_internal_owner_eval_proof_next (l : Ledger) ( original_owner_only :  boolean )
( allowed_for_original_owner_in_lend_state :  boolean ) :
  check_internal_owner_auto_eval l original_owner_only allowed_for_original_owner_in_lend_state =
   (eval_state (Uinterpreter (check_internal_owner original_owner_only allowed_for_original_owner_in_lend_state)) l).
Proof.
  intros. proof_of (check_internal_owner_eval_P l original_owner_only allowed_for_original_owner_in_lend_state).
Qed.


End check_internal_owner.

Section check_external_owner.
Definition check_external_owner_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (check_external_owner )) l}.
  generate_proof (exec_expression l (check_external_owner )).
Defined.
Definition check_external_owner_auto_exec (l : Ledger) : Ledger.
intros. term_of (check_external_owner_exec_P l ).
Defined.
Theorem check_external_owner_exec_proof_next (l : Ledger)  :
  check_external_owner_auto_exec l  =
  exec_state (Uinterpreter (check_external_owner )) l.
Proof.
  intros. proof_of (check_external_owner_exec_P l ).
Qed.



Definition check_external_owner_eval_P (l : Ledger) : 
{v | v =  (eval_state (Uinterpreter (check_external_owner )) l)}.
  generate_proof (eval_expression l (check_external_owner )).
Defined.
Definition check_external_owner_auto_eval (l : Ledger) : (ControlResult uint128 true).
intros. term_of (check_external_owner_eval_P l ).
Defined.
Theorem check_external_owner_eval_proof_next (l : Ledger)  :
  check_external_owner_auto_eval l  =
   (eval_state (Uinterpreter (check_external_owner )) l).
Proof.
  intros. proof_of (check_external_owner_eval_P l ).
Qed.



End check_external_owner.

Section check_owner.
Definition check_owner_exec_P (l : Ledger) ( original_owner_only :  XBool  )
( allowed_in_lend_state :  XBool  ): 
{l' | l' = exec_state (Uinterpreter (check_owner original_owner_only allowed_in_lend_state)) l}.
  generate_proof (exec_expression l (check_owner original_owner_only allowed_in_lend_state)).
Defined.
Definition check_owner_auto_exec (l : Ledger) ( original_owner_only :  XBool  )
( allowed_in_lend_state :  XBool  ): Ledger.
intros. term_of (check_owner_exec_P l original_owner_only allowed_in_lend_state).
Defined.
Theorem check_owner_exec_proof_next (l : Ledger) ( original_owner_only :  XBool  )
( allowed_in_lend_state :  XBool  ) :
  check_owner_auto_exec l original_owner_only allowed_in_lend_state =
  exec_state (Uinterpreter (check_owner original_owner_only allowed_in_lend_state)) l.
Proof.
  intros. proof_of (check_owner_exec_P l original_owner_only allowed_in_lend_state).
Qed.



Definition check_owner_eval_P (l : Ledger) ( original_owner_only :  XBool  )
( allowed_in_lend_state :  XBool  ): 
{v | v =  (eval_state (Uinterpreter (check_owner original_owner_only allowed_in_lend_state)) l)}.
  generate_proof (eval_expression l (check_owner original_owner_only allowed_in_lend_state)).
Defined.
Definition check_owner_auto_eval (l : Ledger) ( original_owner_only :  XBool  )
( allowed_in_lend_state :  XBool  ): (ControlResult uint128 true).
intros. term_of (check_owner_eval_P l original_owner_only allowed_in_lend_state).
Defined.
Theorem check_owner_eval_proof_next (l : Ledger) ( original_owner_only :  XBool  )
( allowed_in_lend_state :  XBool  ) :
  check_owner_auto_eval l original_owner_only allowed_in_lend_state =
   (eval_state (Uinterpreter (check_owner original_owner_only allowed_in_lend_state)) l).
Proof.
  intros. proof_of (check_owner_eval_P l original_owner_only allowed_in_lend_state).
Qed.

End check_owner.

Section check_transfer_requires.
Definition check_transfer_requires_exec_P (l : Ledger) ( tokens : uint128 ) ( grams : uint128 ): 
{l' | l' = exec_state (Uinterpreter (check_transfer_requires tokens grams)) l}.
  generate_proof (exec_expression l (check_transfer_requires tokens grams)).
Defined.
Definition check_transfer_requires_auto_exec (l : Ledger) ( tokens : uint128 ) ( grams : uint128 ): Ledger.
intros. term_of (check_transfer_requires_exec_P l tokens grams).
Defined.
Theorem check_transfer_requires_exec_proof_next (l : Ledger) ( tokens : uint128 ) ( grams : uint128 ) :
  check_transfer_requires_auto_exec l tokens grams =
  exec_state (Uinterpreter (check_transfer_requires tokens grams)) l.
Proof.
  intros. proof_of (check_transfer_requires_exec_P l tokens grams).
Qed.

Definition check_transfer_requires_eval_P (l : Ledger) ( tokens : uint128 ) ( grams : uint128 ): 
{v | v =  (eval_state (Uinterpreter (check_transfer_requires tokens grams)) l)}.
  generate_proof (eval_expression l (check_transfer_requires tokens grams)).
Defined.
Definition check_transfer_requires_auto_eval (l : Ledger) ( tokens : uint128 ) ( grams : uint128 ): (ControlResult uint128 true).
intros. term_of (check_transfer_requires_eval_P l tokens grams).
Defined.
Theorem check_transfer_requires_eval_proof_next (l : Ledger) ( tokens : uint128 ) ( grams : uint128 ) :
  check_transfer_requires_auto_eval l tokens grams =
   (eval_state (Uinterpreter (check_transfer_requires tokens grams)) l).
Proof.
  intros. proof_of (check_transfer_requires_eval_P l tokens grams).
Qed.

End check_transfer_requires.

Section fixup_answer_addr.
Definition fixup_answer_addr_exec_P (l : Ledger) ( answer_addr : ( address ) ): 
{l' | l' = exec_state (Uinterpreter (fixup_answer_addr answer_addr)) l}.
  generate_proof (exec_expression l (fixup_answer_addr answer_addr)).
Defined.
Definition fixup_answer_addr_auto_exec (l : Ledger) ( answer_addr : ( address ) ): Ledger.
intros. term_of (fixup_answer_addr_exec_P l answer_addr).
Defined.
Theorem fixup_answer_addr_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) :
  fixup_answer_addr_auto_exec l answer_addr =
  exec_state (Uinterpreter (fixup_answer_addr answer_addr)) l.
Proof.
  intros. proof_of (fixup_answer_addr_exec_P l answer_addr).
Qed.



Definition fixup_answer_addr_eval_P (l : Ledger) ( answer_addr : ( address ) ): 
{v | v =  (eval_state (Uinterpreter (fixup_answer_addr answer_addr)) l)}.
  generate_proof (eval_expression l (fixup_answer_addr answer_addr)).
Defined.
Definition fixup_answer_addr_auto_eval (l : Ledger) ( answer_addr : ( address ) ): (ControlResult address true).
intros. term_of (fixup_answer_addr_eval_P l answer_addr).
Defined.
Theorem fixup_answer_addr_eval_proof_next (l : Ledger) ( answer_addr : ( address ) ) :
fixup_answer_addr_auto_eval l answer_addr =
   (eval_state (Uinterpreter (fixup_answer_addr answer_addr)) l).
Proof.
  intros. proof_of (fixup_answer_addr_eval_P l answer_addr).
Qed.


End fixup_answer_addr.

Section prepare_transfer_message_flags.
Definition prepare_transfer_message_flags_exec_P (l : Ledger) (  grams : ULValue uint128 ): 
{l' | l' = exec_state (Uinterpreter (prepare_transfer_message_flags grams)) l}.
  generate_proof (exec_expression l (prepare_transfer_message_flags grams)).
Defined.
Definition prepare_transfer_message_flags_auto_exec (l : Ledger) (  grams : ULValue uint128 ): Ledger.
intros. term_of (prepare_transfer_message_flags_exec_P l grams).
Defined.
Theorem prepare_transfer_message_flags_exec_proof_next (l : Ledger) (  grams : ULValue uint128 ) :
  prepare_transfer_message_flags_auto_exec l grams =
  exec_state (Uinterpreter (prepare_transfer_message_flags grams)) l.
Proof.
  intros. proof_of (prepare_transfer_message_flags_exec_P l grams).
Qed.



Definition prepare_transfer_message_flags_eval_P (l : Ledger) (  grams : ULValue uint128 ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_transfer_message_flags grams)) l)}.
  generate_proof (eval_expression l (prepare_transfer_message_flags grams)).
Defined.
Definition prepare_transfer_message_flags_auto_eval (l : Ledger) (  grams : ULValue uint128 ): XUInteger.
intros. term_of (prepare_transfer_message_flags_eval_P l grams).
Defined.
Theorem prepare_transfer_message_flags_eval_proof_next (l : Ledger) (  grams : ULValue uint128 ) :
  prepare_transfer_message_flags_auto_eval l grams =
  toValue (eval_state (Uinterpreter (prepare_transfer_message_flags grams)) l).
Proof.
  intros. proof_of (prepare_transfer_message_flags_eval_P l grams).
Qed.



End prepare_transfer_message_flags.

Section update_spent_balance.
Definition update_spent_balance_exec_P (l : Ledger) ( tokens : uint128 ) ( return_ownership : ( XBool ) ): 
{l' | l' = exec_state (Uinterpreter (update_spent_balance tokens return_ownership)) l}.
  generate_proof (exec_expression l (update_spent_balance tokens return_ownership)).
Defined.
Definition update_spent_balance_auto_exec (l : Ledger) ( tokens : uint128 ) ( return_ownership : ( XBool ) ): Ledger.
intros. term_of (update_spent_balance_exec_P l tokens return_ownership).
Defined.
Theorem update_spent_balance_exec_proof_next (l : Ledger) ( tokens : uint128 ) ( return_ownership : ( XBool ) ) :
  update_spent_balance_auto_exec l tokens return_ownership =
  exec_state (Uinterpreter (update_spent_balance tokens return_ownership)) l.
Proof.
  intros. 
  destruct (update_spent_balance_exec_P l  tokens return_ownership) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (update_spent_balance_exec_P l  tokens return_ownership) in e').
unfold update_spent_balance_exec_P;
  reflexivity.
  rewrite E.
  reflexivity.
  (* proof_of (update_spent_balance_exec_P l tokens return_ownership). *)
Qed.


End update_spent_balance.

Section  transfer_impl.
Definition  transfer_impl_exec_P (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( return_ownership : ( XBool ) ) 
( send_notify : ( XBool ) ) 
( payload : ( cell ) ) : 
{l' | l' = exec_state (Uinterpreter ( transfer_impl answer_addr too tokens grams return_ownership send_notify  payload)) l}.
  generate_proof (exec_expression l ( transfer_impl answer_addr too tokens grams return_ownership send_notify  payload)).
Defined.
Definition  transfer_impl_auto_exec (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( return_ownership : ( XBool ) ) 
( send_notify : ( XBool ) ) 
( payload : ( cell ) ) : Ledger.
intros. term_of ( transfer_impl_exec_P l answer_addr too tokens grams return_ownership send_notify  payload).
Defined.
Theorem  transfer_impl_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( return_ownership : ( XBool ) ) 
( send_notify : ( XBool ) ) 
( payload : ( cell ) )  :
   transfer_impl_auto_exec l answer_addr too tokens grams return_ownership send_notify  payload =
  exec_state (Uinterpreter ( transfer_impl answer_addr too tokens grams return_ownership send_notify  payload)) l.
Proof.
  intros. proof_of ( transfer_impl_exec_P l answer_addr too tokens grams return_ownership send_notify  payload).
Qed.

Definition  transfer_impl_eval_P (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( return_ownership : ( XBool ) ) 
( send_notify : ( XBool ) ) 
( payload : ( cell ) ) : 
{v | v =  (eval_state (Uinterpreter ( transfer_impl answer_addr too tokens grams return_ownership send_notify  payload)) l)}.
  generate_proof (eval_expression l ( transfer_impl answer_addr too tokens grams return_ownership send_notify  payload)).
Defined.

End  transfer_impl.

Section transfer.
(* Definition transfer_exec_P (l : Ledger) ( answer_addr : ( address ) ) ( too : ( address ) ) ( tokens : uint128 ) ( grams : uint128 ) ( return_ownership : ( boolean ) ): 
{l' | l' = exec_state (Uinterpreter (transfer answer_addr too tokens grams return_ownership)) l}.
  generate_proof (exec_expression l (transfer answer_addr too tokens grams return_ownership)).
Defined.
Definition transfer_auto_exec (l : Ledger) ( answer_addr : ( address ) ) ( too : ( address ) ) ( tokens : uint128 ) ( grams : uint128 ) ( return_ownership : ( XBool ) ): Ledger.
intros. term_of (transfer_exec_P l answer_addr too tokens grams return_ownership).
Defined.
Theorem transfer_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) ( too : ( address ) ) ( tokens : uint128 ) ( grams : uint128 ) ( return_ownership : ( XBool ) ) :
  transfer_auto_exec l answer_addr too tokens grams return_ownership =
  exec_state (Uinterpreter (transfer answer_addr too tokens grams return_ownership)) l.
Proof.
  intros. proof_of (transfer_exec_P l answer_addr too tokens grams return_ownership).
Qed.
 *)
End transfer.

Section transferWithNotify.
Definition transferWithNotify_exec_P (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( return_ownership : ( XBool ) ) 
( payload : ( cell ) ) : 
{l' | l' = exec_state (Uinterpreter (transferWithNotify answer_addr too tokens grams return_ownership payload)) l}.
  generate_proof (exec_expression l (transferWithNotify answer_addr too tokens grams return_ownership payload)).
Defined.
Definition transferWithNotify_auto_exec (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( return_ownership : ( XBool ) ) 
( payload : ( cell ) ) : Ledger.
intros. term_of (transferWithNotify_exec_P l answer_addr too tokens grams return_ownership payload).
Defined.
Theorem transferWithNotify_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( return_ownership : ( XBool ) ) 
( payload : ( cell ) )  :
  transferWithNotify_auto_exec l answer_addr too tokens grams return_ownership payload =
  exec_state (Uinterpreter (transferWithNotify answer_addr too tokens grams return_ownership payload)) l.
Proof.
  intros. proof_of (transferWithNotify_exec_P l answer_addr too tokens grams return_ownership payload).
Qed.

End transferWithNotify.


Section prepare_wallet_data.
Definition prepare_wallet_data_exec_P (l : Ledger) ( name : ( XString ) ) 
( symbol : ( XString ) ) 
( decimals : ( XUInteger8 ) ) 
( root_public_key : ( XUInteger256 ) ) 
( wallet_public_key : ( XUInteger256 ) ) 
( root_address : ( address ) ) 
( owner_address : ( XMaybe address ) ) 
( code : ( cell ) ) 
( workchain_id : ( int ) ) : 
{l' | l' = exec_state (Uinterpreter (prepare_wallet_data name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )) l}.
  generate_proof (exec_expression l (prepare_wallet_data name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )).
Defined.
Definition prepare_wallet_data_auto_exec (l : Ledger) ( name : ( XString ) ) 
( symbol : ( XString ) ) 
( decimals : ( XUInteger8 ) ) 
( root_public_key : ( XUInteger256 ) ) 
( wallet_public_key : ( XUInteger256 ) ) 
( root_address : ( address ) ) 
( owner_address : ( XMaybe address ) ) 
( code : ( cell ) ) 
( workchain_id : ( int ) ) : Ledger.
intros. term_of (prepare_wallet_data_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ).
Defined.
Theorem prepare_wallet_data_exec_proof_next (l : Ledger) ( name : ( XString ) ) 
( symbol : ( XString ) ) 
( decimals : ( XUInteger8 ) ) 
( root_public_key : ( XUInteger256 ) ) 
( wallet_public_key : ( XUInteger256 ) ) 
( root_address : ( address ) ) 
( owner_address : ( XMaybe address ) ) 
( code : ( cell ) ) 
( workchain_id : ( int ) )  :
  prepare_wallet_data_auto_exec l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id  =
  exec_state (Uinterpreter (prepare_wallet_data name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )) l.
Proof.
  intros. proof_of (prepare_wallet_data_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ).
Qed.



Definition prepare_wallet_data_eval_P (l : Ledger) ( name : ( XString ) ) 
( symbol : ( XString ) ) 
( decimals : ( XUInteger8 ) ) 
( root_public_key : ( XUInteger256 ) ) 
( wallet_public_key : ( XUInteger256 ) ) 
( root_address : ( address ) ) 
( owner_address : ( XMaybe address ) ) 
( code : ( cell ) ) 
( workchain_id : ( int ) ) : 
{v | v = toValue (eval_state (Uinterpreter (prepare_wallet_data name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )) l)}.
  generate_proof (eval_expression l (prepare_wallet_data name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )).
Defined.
Definition prepare_wallet_data_auto_eval (l : Ledger) ( name : ( XString ) ) 
( symbol : ( XString ) ) 
( decimals : ( XUInteger8 ) ) 
( root_public_key : ( XUInteger256 ) ) 
( wallet_public_key : ( XUInteger256 ) ) 
( root_address : ( address ) ) 
( owner_address : ( XMaybe address ) ) 
( code : ( cell ) ) 
( workchain_id : ( int ) ) : DTONTokenWalletLRecord.
intros. term_of (prepare_wallet_data_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ).
Defined.
Theorem prepare_wallet_data_eval_proof_next (l : Ledger) ( name : ( XString ) ) 
( symbol : ( XString ) ) 
( decimals : ( XUInteger8 ) ) 
( root_public_key : ( XUInteger256 ) ) 
( wallet_public_key : ( XUInteger256 ) ) 
( root_address : ( address ) ) 
( owner_address : ( XMaybe address ) ) 
( code : ( cell ) ) 
( workchain_id : ( int ) )  :
  prepare_wallet_data_auto_eval l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id  =
  toValue (eval_state (Uinterpreter (prepare_wallet_data name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )) l).
Proof.
  intros. proof_of (prepare_wallet_data_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ).
Qed.



End prepare_wallet_data.


Section prepare_wallet_state_init_and_addr.
Definition prepare_wallet_state_init_and_addr_exec_P (l : Ledger) ( wallet_data : ( DTONTokenWalletLRecord ) ) : 
{l' | l' = exec_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l}.
  generate_proof (exec_expression l (prepare_wallet_state_init_and_addr wallet_data)).
Defined.
Definition prepare_wallet_state_init_and_addr_auto_exec (l : Ledger) ( wallet_data : ( DTONTokenWalletLRecord ) ) : Ledger.
intros. term_of (prepare_wallet_state_init_and_addr_exec_P l wallet_data).
Defined.
Theorem prepare_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( wallet_data : ( DTONTokenWalletLRecord ) )  :
  prepare_wallet_state_init_and_addr_auto_exec l wallet_data =
  exec_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l.
Proof.
  intros. proof_of (prepare_wallet_state_init_and_addr_exec_P l wallet_data).
Qed.



Definition prepare_wallet_state_init_and_addr_eval_P (l : Ledger) ( wallet_data : ( DTONTokenWalletLRecord ) ) : 
{v | v = toValue (eval_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l)}.
  generate_proof (eval_expression l (prepare_wallet_state_init_and_addr wallet_data)).
Defined.
Definition prepare_wallet_state_init_and_addr_auto_eval (l : Ledger) ( wallet_data : ( DTONTokenWalletLRecord ) ) : StateInitLRecord # XUInteger256.
intros. term_of (prepare_wallet_state_init_and_addr_eval_P l wallet_data).
Defined.
Theorem prepare_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( wallet_data : ( DTONTokenWalletLRecord ) )  :
  prepare_wallet_state_init_and_addr_auto_eval l wallet_data =
  toValue (eval_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l).
Proof.
  intros. proof_of (prepare_wallet_state_init_and_addr_eval_P l wallet_data).
Qed.



End prepare_wallet_state_init_and_addr.

Section optional_owner.
Definition optional_owner_exec_P (l : Ledger) ( owner : ( address ) ): 
{l' | l' = exec_state (Uinterpreter (optional_owner owner)) l}.
  generate_proof (exec_expression l (optional_owner owner)).
Defined.
Definition optional_owner_auto_exec (l : Ledger) ( owner : ( address ) ): Ledger.
intros. term_of (optional_owner_exec_P l owner).
Defined.
Theorem optional_owner_exec_proof_next (l : Ledger) ( owner : ( address ) ) :
  optional_owner_auto_exec l owner =
  exec_state (Uinterpreter (optional_owner owner)) l.
Proof.
  intros. proof_of (optional_owner_exec_P l owner).
Qed.



Definition optional_owner_eval_P (l : Ledger) ( owner : ( address ) ): 
{v | v = toValue (eval_state (Uinterpreter (optional_owner owner)) l)}.
  generate_proof (eval_expression l (optional_owner owner)).
Defined.
Definition optional_owner_auto_eval (l : Ledger) ( owner : ( address ) ): (XMaybe address).
intros. term_of (optional_owner_eval_P l owner).
Defined.
Theorem optional_owner_eval_proof_next (l : Ledger) ( owner : ( address ) ) :
  optional_owner_auto_eval l owner =
  toValue (eval_state (Uinterpreter (optional_owner owner)) l).
Proof.
  intros. proof_of (optional_owner_eval_P l owner).
Qed.



End optional_owner.

Section calc_wallet_init_hash.
Definition calc_wallet_init_hash_exec_P (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) ) : 
{l' | l' = exec_state (Uinterpreter (calc_wallet_init_hash pubkey internal_owner)) l}.
  generate_proof (exec_expression l (calc_wallet_init_hash pubkey internal_owner)).
Defined.
Definition calc_wallet_init_hash_auto_exec (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) ) : Ledger.
intros. term_of (calc_wallet_init_hash_exec_P l pubkey internal_owner).
Defined.
Theorem calc_wallet_init_hash_exec_proof_next (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) )  :
  calc_wallet_init_hash_auto_exec l pubkey internal_owner =
  exec_state (Uinterpreter (calc_wallet_init_hash pubkey internal_owner)) l.
Proof.
  intros. proof_of (calc_wallet_init_hash_exec_P l pubkey internal_owner).
Qed.



Definition calc_wallet_init_hash_eval_P (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) ) : 
{v | v = toValue (eval_state (Uinterpreter (calc_wallet_init_hash pubkey internal_owner)) l)}.
  generate_proof (eval_expression l (calc_wallet_init_hash pubkey internal_owner)).
Defined.
Definition calc_wallet_init_hash_auto_eval (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) ) : StateInitLRecord # XUInteger256.
intros. term_of (calc_wallet_init_hash_eval_P l pubkey internal_owner).
Defined.
Theorem calc_wallet_init_hash_eval_proof_next (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) )  :
  calc_wallet_init_hash_auto_eval l pubkey internal_owner =
  toValue (eval_state (Uinterpreter (calc_wallet_init_hash pubkey internal_owner)) l).
Proof.
  intros. proof_of (calc_wallet_init_hash_eval_P l pubkey internal_owner).
Qed.



End calc_wallet_init_hash.


Section expected_sender_address.
Definition expected_sender_address_exec_P (l : Ledger) ( sender_public_key : ( XUInteger256 ) ) 
( sender_owner : ( address ) ) : 
{l' | l' = exec_state (Uinterpreter (expected_sender_address sender_public_key sender_owner)) l}.
  generate_proof (exec_expression l (expected_sender_address sender_public_key sender_owner)).
Defined.
Definition expected_sender_address_auto_exec (l : Ledger) ( sender_public_key : ( XUInteger256 ) ) 
( sender_owner : ( address ) ) : Ledger.
intros. term_of (expected_sender_address_exec_P l sender_public_key sender_owner).
Defined.
Theorem expected_sender_address_exec_proof_next (l : Ledger) ( sender_public_key : ( XUInteger256 ) ) 
( sender_owner : ( address ) )  :
  expected_sender_address_auto_exec l sender_public_key sender_owner =
  exec_state (Uinterpreter (expected_sender_address sender_public_key sender_owner)) l.
Proof.
  intros. proof_of (expected_sender_address_exec_P l sender_public_key sender_owner).
Qed.



Definition expected_sender_address_eval_P (l : Ledger) ( sender_public_key : ( XUInteger256 ) ) 
( sender_owner : ( address ) ) : 
{v | v = toValue (eval_state (Uinterpreter (expected_sender_address sender_public_key sender_owner)) l)}.
  generate_proof (eval_expression l (expected_sender_address sender_public_key sender_owner)).
Defined.
Definition expected_sender_address_auto_eval (l : Ledger) ( sender_public_key : ( XUInteger256 ) ) 
( sender_owner : ( address ) ) : XUInteger256.
intros. term_of (expected_sender_address_eval_P l sender_public_key sender_owner).
Defined.
Theorem expected_sender_address_eval_proof_next (l : Ledger) ( sender_public_key : ( XUInteger256 ) ) 
( sender_owner : ( address ) )  :
  expected_sender_address_auto_eval l sender_public_key sender_owner =
  toValue (eval_state (Uinterpreter (expected_sender_address sender_public_key sender_owner)) l).
Proof.
  intros. proof_of (expected_sender_address_eval_P l sender_public_key sender_owner).
Qed.



End expected_sender_address.


Section calc_wallet_init.
Definition calc_wallet_init_exec_P (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) ) : 
{l' | l' = exec_state (Uinterpreter (calc_wallet_init pubkey internal_owner)) l}.
  generate_proof (exec_expression l (calc_wallet_init pubkey internal_owner)).
Defined.
Definition calc_wallet_init_auto_exec (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) ) : Ledger.
intros. term_of (calc_wallet_init_exec_P l pubkey internal_owner).
Defined.
Theorem calc_wallet_init_exec_proof_next (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) )  :
  calc_wallet_init_auto_exec l pubkey internal_owner =
  exec_state (Uinterpreter (calc_wallet_init pubkey internal_owner)) l.
Proof.
  intros. proof_of (calc_wallet_init_exec_P l pubkey internal_owner).
Qed.



Definition calc_wallet_init_eval_P (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) ) : 
{v | v = toValue (eval_state (Uinterpreter (calc_wallet_init pubkey internal_owner)) l)}.
  generate_proof (eval_expression l (calc_wallet_init pubkey internal_owner)).
Defined.
Definition calc_wallet_init_auto_eval (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) ) : StateInitLRecord # address.
intros. term_of (calc_wallet_init_eval_P l pubkey internal_owner).
Defined.
Theorem calc_wallet_init_eval_proof_next (l : Ledger) ( pubkey : ( XUInteger256 ) ) 
( internal_owner : ( address ) )  :
  calc_wallet_init_auto_eval l pubkey internal_owner =
  toValue (eval_state (Uinterpreter (calc_wallet_init pubkey internal_owner)) l).
Proof.
  intros. proof_of (calc_wallet_init_eval_P l pubkey internal_owner).
Qed.



End calc_wallet_init.

Section transfer_to_recipient_impl.
Definition transfer_to_recipient_impl_exec_P (l : Ledger) ( answer_addr : ( address ) ) 
( recipient_public_key : ( XUInteger256 ) ) 
( recipient_internal_owner : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( deploy : ( XBool ) ) 
( return_ownership : ( XBool ) ) 
( send_notify : ( XBool ) ) 
( payload : ( cell ) ) : 
{l' | l' = exec_state (Uinterpreter (transfer_to_recipient_impl answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload )) l}.
  generate_proof (exec_expression l (transfer_to_recipient_impl answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload )).
Defined.
Definition transfer_to_recipient_impl_auto_exec (l : Ledger) ( answer_addr : ( address ) ) 
( recipient_public_key : ( XUInteger256 ) ) 
( recipient_internal_owner : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( deploy : ( XBool ) ) 
( return_ownership : ( XBool ) ) 
( send_notify : ( XBool ) ) 
( payload : ( cell ) ) : Ledger.
intros. term_of (transfer_to_recipient_impl_exec_P l answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ).
Defined.
Theorem transfer_to_recipient_impl_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) 
( recipient_public_key : ( XUInteger256 ) ) 
( recipient_internal_owner : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( deploy : ( XBool ) ) 
( return_ownership : ( XBool ) ) 
( send_notify : ( XBool ) ) 
( payload : ( cell ) )  :
  transfer_to_recipient_impl_auto_exec l answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload  =
  exec_state (Uinterpreter (transfer_to_recipient_impl answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload )) l.
Proof.
  intros. proof_of (transfer_to_recipient_impl_exec_P l answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ).
Qed.



End transfer_to_recipient_impl.


Section transferToRecipient.
Definition transferToRecipient_exec_P (l : Ledger) ( answer_addr : ( address ) ) 
( recipient_public_key : ( XUInteger256 ) ) 
( recipient_internal_owner : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( deploy : ( XBool ) ) 
( return_ownership : ( XBool ) ) : 
{l' | l' = exec_state (Uinterpreter (transferToRecipient answer_addr recipient_public_key  recipient_internal_owner tokens grams deploy return_ownership)) l}.
  generate_proof (exec_expression l (transferToRecipient answer_addr recipient_public_key  recipient_internal_owner tokens grams deploy return_ownership)).
Defined.
Definition transferToRecipient_auto_exec (l : Ledger) ( answer_addr : ( address ) ) 
( recipient_public_key : ( XUInteger256 ) ) 
( recipient_internal_owner : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( deploy : ( XBool ) ) 
( return_ownership : ( XBool ) ) : Ledger.
intros. term_of (transferToRecipient_exec_P l answer_addr recipient_public_key  recipient_internal_owner tokens grams deploy return_ownership).
Defined.
Theorem transferToRecipient_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) 
( recipient_public_key : ( XUInteger256 ) ) 
( recipient_internal_owner : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) 
( deploy : ( XBool ) ) 
( return_ownership : ( XBool ) )  :
  transferToRecipient_auto_exec l answer_addr recipient_public_key  recipient_internal_owner tokens grams deploy return_ownership =
  exec_state (Uinterpreter (transferToRecipient answer_addr recipient_public_key  recipient_internal_owner tokens grams deploy return_ownership)) l.
Proof.
  intros. proof_of (transferToRecipient_exec_P l answer_addr recipient_public_key  recipient_internal_owner tokens grams deploy return_ownership).
Qed.


End transferToRecipient.

Section requestBalance.
Definition requestBalance_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (requestBalance )) l}.
  generate_proof (exec_expression l (requestBalance )).
Defined.
Definition requestBalance_auto_exec (l : Ledger) : Ledger.
intros. term_of (requestBalance_exec_P l ).
Defined.
Theorem requestBalance_exec_proof_next (l : Ledger)  :
  requestBalance_auto_exec l  =
  exec_state (Uinterpreter (requestBalance )) l.
Proof.
  intros. proof_of (requestBalance_exec_P l ).
Qed.



Definition requestBalance_eval_P (l : Ledger) : 
{v | v = toValue (eval_state (Uinterpreter (requestBalance )) l)}.
  generate_proof (eval_expression l (requestBalance )).
Defined.
Definition requestBalance_auto_eval (l : Ledger) : uint128.
intros. term_of (requestBalance_eval_P l ).
Defined.
Theorem requestBalance_eval_proof_next (l : Ledger)  :
  requestBalance_auto_eval l  =
  toValue (eval_state (Uinterpreter (requestBalance )) l).
Proof.
  intros. proof_of (requestBalance_eval_P l ).
Qed.



End requestBalance.

Section accept.
Definition accept_exec_P (l : Ledger) ( tokens : uint128 ) ( answer_addr : ( address ) ) ( keep_grams : uint128 ): 
{l' | l' = exec_state (Uinterpreter (accept tokens answer_addr keep_grams)) l}.
  generate_proof (exec_expression l (accept tokens answer_addr keep_grams)).
Defined.
Definition accept_auto_exec (l : Ledger) ( tokens : uint128 ) ( answer_addr : ( address ) ) ( keep_grams : uint128 ): Ledger.
intros. term_of (accept_exec_P l tokens answer_addr keep_grams).
Defined.
Theorem accept_exec_proof_next (l : Ledger) ( tokens : uint128 ) ( answer_addr : ( address ) ) ( keep_grams : uint128 ) :
  accept_auto_exec l tokens answer_addr keep_grams =
  exec_state (Uinterpreter (accept tokens answer_addr keep_grams)) l.
Proof.
  intros. proof_of (accept_exec_P l tokens answer_addr keep_grams).
Qed.

Definition accept_eval_P (l : Ledger) ( tokens : uint128 ) ( answer_addr : ( address ) ) ( keep_grams : uint128 ): 
{v | v =  (eval_state (Uinterpreter (accept tokens answer_addr keep_grams)) l)}.
  generate_proof (eval_expression l (accept tokens answer_addr keep_grams)).
Defined.
Definition accept_auto_eval (l : Ledger) ( tokens : uint128 ) ( answer_addr : ( address ) ) ( keep_grams : uint128 ): (ControlResult XBool true).
intros. term_of (accept_eval_P l tokens answer_addr keep_grams).
Defined.
Theorem accept_eval_proof_next (l : Ledger) ( tokens : uint128 ) ( answer_addr : ( address ) ) ( keep_grams : uint128 ) :
  accept_auto_eval l tokens answer_addr keep_grams =
   (eval_state (Uinterpreter (accept tokens answer_addr keep_grams)) l).
Proof.
  intros. proof_of (accept_eval_P l tokens answer_addr keep_grams).
Qed.


End accept.


Section internalTransfer.
Definition internalTransfer_exec_P (l : Ledger) ( tokens : uint128 ) 
( answer_addr : ( address ) ) 
( sender_pubkey : ( XUInteger256 ) ) 
( sender_owner : ( address ) ) 
( notify_receiver : ( XBool ) ) 
( payload : ( cell ) ) : 
{l' | l' = exec_state (Uinterpreter (internalTransfer tokens answer_addr sender_pubkey sender_owner notify_receiver payload )) l}.
  generate_proof (exec_expression l (internalTransfer tokens answer_addr sender_pubkey sender_owner notify_receiver payload )).
Defined.
Definition internalTransfer_auto_exec (l : Ledger) ( tokens : uint128 ) 
( answer_addr : ( address ) ) 
( sender_pubkey : ( XUInteger256 ) ) 
( sender_owner : ( address ) ) 
( notify_receiver : ( XBool ) ) 
( payload : ( cell ) ) : Ledger.
intros. term_of (internalTransfer_exec_P l tokens answer_addr sender_pubkey sender_owner notify_receiver payload ).
Defined.
Theorem internalTransfer_exec_proof_next (l : Ledger) ( tokens : uint128 ) 
( answer_addr : ( address ) ) 
( sender_pubkey : ( XUInteger256 ) ) 
( sender_owner : ( address ) ) 
( notify_receiver : ( XBool ) ) 
( payload : ( cell ) )  :
  internalTransfer_auto_exec l tokens answer_addr sender_pubkey sender_owner notify_receiver payload  =
  exec_state (Uinterpreter (internalTransfer tokens answer_addr sender_pubkey sender_owner notify_receiver payload )) l.
Proof.
  intros. proof_of (internalTransfer_exec_P l tokens answer_addr sender_pubkey sender_owner notify_receiver payload ).
Qed.



End internalTransfer.


Section lendOwnership.
Definition lendOwnership_exec_P (l : Ledger) ( answer_addr : ( address ) ) 
( grams : uint128 ) 
( std_dest : ( XUInteger256 ) ) 
( lend_balance : uint128 ) 
( lend_finish_time : ( XUInteger32 ) ) 
( deploy_init_cl : ( cell ) ) 
( payload : ( cell ) ) : 
{l' | l' = exec_state (Uinterpreter (lendOwnership answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload)) l}.
  generate_proof (exec_expression l (lendOwnership answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload)).
Defined.
Definition lendOwnership_auto_exec (l : Ledger) ( answer_addr : ( address ) ) 
( grams : uint128 ) 
( std_dest : ( XUInteger256 ) ) 
( lend_balance : uint128 ) 
( lend_finish_time : ( XUInteger32 ) ) 
( deploy_init_cl : ( cell ) ) 
( payload : ( cell ) ) : Ledger.
intros. term_of (lendOwnership_exec_P l answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload).
Defined.
Theorem lendOwnership_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) 
( grams : uint128 ) 
( std_dest : ( XUInteger256 ) ) 
( lend_balance : uint128 ) 
( lend_finish_time : ( XUInteger32 ) ) 
( deploy_init_cl : ( cell ) ) 
( payload : ( cell ) )  :
  lendOwnership_auto_exec l answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload =
  exec_state (Uinterpreter (lendOwnership answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload)) l.
Proof.
  intros. proof_of (lendOwnership_exec_P l answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload).
Qed.

End lendOwnership.



Section filter_lend_ownerhip_array.
Definition filter_lend_ownerhip_array_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (filter_lend_ownerhip_array )) l}.
  generate_proof (exec_expression l (filter_lend_ownerhip_array )).
Defined.
Definition filter_lend_ownerhip_array_auto_exec (l : Ledger) : Ledger.
intros. term_of (filter_lend_ownerhip_array_exec_P l ).
Defined.
Theorem filter_lend_ownerhip_array_exec_proof_next (l : Ledger)  :
  filter_lend_ownerhip_array_auto_exec l  =
  exec_state (Uinterpreter (filter_lend_ownerhip_array )) l.
Proof.
  intros. proof_of (filter_lend_ownerhip_array_exec_P l ).
Qed.



Definition filter_lend_ownerhip_array_eval_P (l : Ledger) : 
{v | v = toValue (eval_state (Uinterpreter (filter_lend_ownerhip_array )) l)}.
  generate_proof (eval_expression l (filter_lend_ownerhip_array )).
Defined.
Definition filter_lend_ownerhip_array_auto_eval (l : Ledger) : lend_ownership_array # uint128.
intros. term_of (filter_lend_ownerhip_array_eval_P l ).
Defined.
Theorem filter_lend_ownerhip_array_eval_proof_next (l : Ledger)  :
  filter_lend_ownerhip_array_auto_eval l  =
  toValue (eval_state (Uinterpreter (filter_lend_ownerhip_array )) l).
Proof.
  intros. proof_of (filter_lend_ownerhip_array_eval_P l ).
Qed.



End filter_lend_ownerhip_array.


Section returnOwnership.
Definition returnOwnership_exec_P (l : Ledger) ( tokens : uint128 ): 
{l' | l' = exec_state (Uinterpreter (returnOwnership tokens)) l}.
  generate_proof (exec_expression l (returnOwnership tokens)).
Defined.
Definition returnOwnership_auto_exec (l : Ledger) ( tokens : uint128 ): Ledger.
intros. term_of (returnOwnership_exec_P l tokens).
Defined.
Theorem returnOwnership_exec_proof_next (l : Ledger) ( tokens : uint128 ) :
  returnOwnership_auto_exec l tokens =
  exec_state (Uinterpreter (returnOwnership tokens)) l.
Proof.
  intros. proof_of (returnOwnership_exec_P l tokens).
Qed.



End returnOwnership.

Section approve.
Definition approve_exec_P (l : Ledger) ( spender : ( address ) ) ( remainingTokens : uint128 ) ( tokens : uint128 ): 
{l' | l' = exec_state (Uinterpreter (approve spender remainingTokens tokens )) l}.
  generate_proof (exec_expression l (approve spender remainingTokens tokens )).
Defined.
Definition approve_auto_exec (l : Ledger) ( spender : ( address ) ) ( remainingTokens : uint128 ) ( tokens : uint128 ): Ledger.
intros. term_of (approve_exec_P l spender remainingTokens tokens ).
Defined.
Theorem approve_exec_proof_next (l : Ledger) ( spender : ( address ) ) ( remainingTokens : uint128 ) ( tokens : uint128 ) :
  approve_auto_exec l spender remainingTokens tokens  =
  exec_state (Uinterpreter (approve spender remainingTokens tokens )) l.
Proof.
  intros. proof_of (approve_exec_P l spender remainingTokens tokens ).
Qed.


End approve.

Section transfer_from_impl.
Definition transfer_from_impl_exec_P (l : Ledger) ( answer_addr : ( address ) ) ( from : ( address ) ) ( too : ( address ) ) ( tokens : uint128 ) ( grams : uint128 ) ( send_notify : ( XBool ) ) ( payload : ( cell ) ): 
{l' | l' = exec_state (Uinterpreter (transfer_from_impl answer_addr from too tokens grams send_notify payload)) l}.
  generate_proof (exec_expression l (transfer_from_impl answer_addr from too tokens grams send_notify payload)).
Defined.
Definition transfer_from_impl_auto_exec (l : Ledger) ( answer_addr : ( address ) ) ( from : ( address ) ) ( too : ( address ) ) ( tokens : uint128 ) ( grams : uint128 ) ( send_notify : ( XBool ) ) ( payload : ( cell ) ): Ledger.
intros. term_of (transfer_from_impl_exec_P l answer_addr from too tokens grams send_notify payload).
Defined.
Theorem transfer_from_impl_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) ( from : ( address ) ) ( too : ( address ) ) ( tokens : uint128 ) ( grams : uint128 ) ( send_notify : ( XBool ) ) ( payload : ( cell ) ) :
  transfer_from_impl_auto_exec l answer_addr from too tokens grams send_notify payload =
  exec_state (Uinterpreter (transfer_from_impl answer_addr from too tokens grams send_notify payload)) l.
Proof.
  intros. proof_of (transfer_from_impl_exec_P l answer_addr from too tokens grams send_notify payload).
Qed.


End transfer_from_impl.


Section transferFrom.
Definition transferFrom_exec_P (l : Ledger) ( answer_addr : ( address ) ) 
( from : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) : 
{l' | l' = exec_state (Uinterpreter (transferFrom answer_addr from too tokens grams)) l}.
  generate_proof (exec_expression l (transferFrom answer_addr from too tokens grams)).
Defined.
Definition transferFrom_auto_exec (l : Ledger) ( answer_addr : ( address ) ) 
( from : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 ) : Ledger.
intros. term_of (transferFrom_exec_P l answer_addr from too tokens grams).
Defined.
Theorem transferFrom_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) 
( from : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : uint128 )  :
  transferFrom_auto_exec l answer_addr from too tokens grams =
  exec_state (Uinterpreter (transferFrom answer_addr from too tokens grams)) l.
Proof.
  intros. proof_of (transferFrom_exec_P l answer_addr from too tokens grams).
Qed.


End transferFrom.


Section transferFromWithNotify.
Definition transferFromWithNotify_exec_P (l : Ledger) ( answer_addr : ( address ) ) 
( from : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : ( uint128 ) ) 
( payload : ( cell ) ) : 
{l' | l' = exec_state (Uinterpreter (transferFromWithNotify answer_addr from too tokens grams payload)) l}.
  generate_proof (exec_expression l (transferFromWithNotify answer_addr from too tokens grams payload)).
Defined.
Definition transferFromWithNotify_auto_exec (l : Ledger) ( answer_addr : ( address ) ) 
( from : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : ( uint128 ) ) 
( payload : ( cell ) ) : Ledger.
intros. term_of (transferFromWithNotify_exec_P l answer_addr from too  tokens grams payload).
Defined.
Theorem transferFromWithNotify_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) 
( from : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( grams : ( uint128 ) ) 
( payload : ( cell ) )  :
  transferFromWithNotify_auto_exec l answer_addr from too tokens grams payload =
  exec_state (Uinterpreter (transferFromWithNotify answer_addr from too tokens grams payload)) l.
Proof.
  intros. proof_of (transferFromWithNotify_exec_P l answer_addr from too tokens grams payload).
Qed.

End transferFromWithNotify.

Section internalTransferFrom.
Definition internalTransferFrom_exec_P (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( notify_receiver : ( XBool ) ) 
( payload : ( cell ) ) : 
{l' | l' = exec_state (Uinterpreter (internalTransferFrom answer_addr too tokens notify_receiver payload)) l}.
  generate_proof (exec_expression l (internalTransferFrom answer_addr too tokens notify_receiver payload)).
Defined.
Definition internalTransferFrom_auto_exec (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( notify_receiver : ( XBool ) ) 
( payload : ( cell ) ) : Ledger.
intros. term_of (internalTransferFrom_exec_P l answer_addr too tokens notify_receiver payload).
Defined.
Theorem internalTransferFrom_exec_proof_next (l : Ledger) ( answer_addr : ( address ) ) 
( too : ( address ) ) 
( tokens : uint128 ) 
( notify_receiver : ( XBool ) ) 
( payload : ( cell ) )  :
  internalTransferFrom_auto_exec l answer_addr too tokens notify_receiver payload =
  exec_state (Uinterpreter (internalTransferFrom answer_addr too tokens notify_receiver payload)) l.
Proof.
  intros. proof_of (internalTransferFrom_exec_P l answer_addr too tokens notify_receiver payload).
Qed.


End internalTransferFrom.

Section disapprove.
Definition disapprove_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (disapprove )) l}.
  generate_proof (exec_expression l (disapprove )).
Defined.
Definition disapprove_auto_exec (l : Ledger) : Ledger.
intros. term_of (disapprove_exec_P l ).
Defined.
Theorem disapprove_exec_proof_next (l : Ledger)  :
  disapprove_auto_exec l  =
  exec_state (Uinterpreter (disapprove )) l.
Proof.
  intros. proof_of (disapprove_exec_P l ).
Qed.


End disapprove.


Section _on_bounced.
Definition _on_bounced_exec_P (l : Ledger) ( msg : ( cell ) ) ( msg_body : ( XSlice ) ): 
{l' | l' = exec_state (Uinterpreter (_on_bounced msg msg_body)) l}.
  generate_proof (exec_expression l (_on_bounced msg msg_body)).
Defined.
Definition _on_bounced_auto_exec (l : Ledger) ( msg : ( cell ) ) ( msg_body : ( XSlice ) ): Ledger.
intros. term_of (_on_bounced_exec_P l msg msg_body).
Defined.
Theorem _on_bounced_exec_proof_next (l : Ledger) ( msg : ( cell ) ) ( msg_body : ( XSlice ) ) :
  _on_bounced_auto_exec l msg msg_body =
  exec_state (Uinterpreter (_on_bounced msg msg_body)) l.
Proof.
  intros. proof_of (_on_bounced_exec_P l msg msg_body).
Qed.



Definition _on_bounced_eval_P (l : Ledger) ( msg : ( cell ) ) ( msg_body : ( XSlice ) ): 
{v | v =  (eval_state (Uinterpreter (_on_bounced msg msg_body)) l)}.
  generate_proof (eval_expression l (_on_bounced msg msg_body)).
Defined.
Definition _on_bounced_auto_eval (l : Ledger) ( msg : ( cell ) ) ( msg_body : ( XSlice ) ): (ControlResult XUInteger true).
intros. term_of (_on_bounced_eval_P l msg msg_body).
Defined.
Theorem _on_bounced_eval_proof_next (l : Ledger) ( msg : ( cell ) ) ( msg_body : ( XSlice ) ) :
  _on_bounced_auto_eval l msg msg_body =
   (eval_state (Uinterpreter (_on_bounced msg msg_body)) l).
Proof.
  intros. proof_of (_on_bounced_eval_P l msg msg_body).
Qed.

End _on_bounced.


Section _fallback.
Definition _fallback_exec_P (l : Ledger)  (msg : cell ) ( msg_body : ( XSlice ) ): 
{l' | l' = exec_state (Uinterpreter (_fallback msg msg_body)) l}.
  generate_proof (exec_expression l (_fallback msg msg_body)).
Defined.
Definition _fallback_auto_exec (l : Ledger)  ( msg : cell ) ( msg_body : ( XSlice ) ): Ledger.
intros. term_of (_fallback_exec_P l msg msg_body).
Defined.
Theorem _fallback_exec_proof_next (l : Ledger)  ( msg : cell ) ( msg_body : ( XSlice ) ) :
  _fallback_auto_exec l msg msg_body =
  exec_state (Uinterpreter (_fallback msg msg_body)) l.
Proof.
  intros. proof_of (_fallback_exec_P l msg msg_body).
Qed.



Definition _fallback_eval_P (l : Ledger)  ( msg : cell ) ( msg_body : ( XSlice ) ): 
{v | v =  (eval_state (Uinterpreter (_fallback msg msg_body)) l)}.
  generate_proof (eval_expression l (_fallback msg msg_body)).
Defined.
Definition _fallback_auto_eval (l : Ledger)  (msg : cell ) ( msg_body : ( XSlice ) ): (ControlResult XUInteger true).
intros. term_of (_fallback_eval_P l msg msg_body).
Defined.
Theorem _fallback_eval_proof_next (l : Ledger)  (msg : cell ) ( msg_body : ( XSlice ) ) :
  _fallback_auto_eval l msg msg_body =
   (eval_state (Uinterpreter (_fallback msg msg_body)) l).
Proof.
  intros. proof_of (_fallback_eval_P l msg msg_body).
Qed.

End _fallback.


Section prepare_external_wallet_state_init_and_addr.
Definition prepare_external_wallet_state_init_and_addr_exec_P (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ): 
{l' | l' = exec_state (Uinterpreter (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l}.
  generate_proof (exec_expression l (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_external_wallet_state_init_and_addr_auto_exec (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ): Ledger.
intros. term_of (prepare_external_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_external_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ) :
  prepare_external_wallet_state_init_and_addr_auto_exec l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  exec_state (Uinterpreter (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l.
Proof.
  intros. proof_of (prepare_external_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.



Definition prepare_external_wallet_state_init_and_addr_eval_P (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l)}.
  generate_proof (eval_expression l (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_external_wallet_state_init_and_addr_auto_eval (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ): StateInitLRecord # XUInteger256.
intros. term_of (prepare_external_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_external_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ) :
  prepare_external_wallet_state_init_and_addr_auto_eval l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  toValue (eval_state (Uinterpreter (prepare_external_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l).
Proof.
  intros. proof_of (prepare_external_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.



End prepare_external_wallet_state_init_and_addr.


Section prepare_internal_wallet_state_init_and_addr.
Definition prepare_internal_wallet_state_init_and_addr_exec_P (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ): 
{l' | l' = exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l}.
  generate_proof (exec_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_exec (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ): Ledger.
intros. term_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ) :
  prepare_internal_wallet_state_init_and_addr_auto_exec l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l.
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.

Definition prepare_internal_wallet_state_init_and_addr_eval_P (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l)}.
  generate_proof (eval_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_eval (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ): StateInitLRecord # XUInteger256.
intros. term_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( XUInteger8 ) ) ( root_public_key : ( XUInteger256 ) ) ( wallet_public_key : ( XUInteger256 ) ) ( root_address : ( address ) ) ( owner_address : ( XMaybe address ) ) ( code : ( cell ) ) ( workchain_id : ( int ) ) :
  prepare_internal_wallet_state_init_and_addr_auto_eval l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l).
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.

End prepare_internal_wallet_state_init_and_addr.


