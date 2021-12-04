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

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.

Require Import Wrapper.Ledger.
Require Import Wrapper.Functions.FuncSig.
Require Import Wrapper.Functions.FuncNotations.
Require Import Wrapper.Interface.
Require Import Wrapper.Functions.Funcs.


Module EvalExecAuto (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .

Module Export FuncsModule := Funcs co dc.

Import co.
(* Module Import xxx := SpecModuleForFuncNotations.LedgerModuleForFuncSig.

Module Import generator := execGenerator XTypesModule StateMonadModule xxx.
 *)

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.
Local Open Scope ucpp_scope.
(* 
Import URSUS_. *)

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

Section getStateInit.

Definition getStateInit_exec_P (l : Ledger) ( msg : ULValue PhantomType ): 
{l' | l' = exec_state (Uinterpreter (getStateInit msg)) l}.
  generate_proof (exec_expression l (getStateInit msg)).
Defined.
Definition getStateInit_auto_exec (l : Ledger) ( msg : ULValue PhantomType ): Ledger.
intros. term_of (getStateInit_exec_P l msg).
Defined.
Theorem getStateInit_exec_proof_next (l : Ledger) ( msg : ULValue PhantomType ) :
  getStateInit_auto_exec l msg =
  exec_state (Uinterpreter (getStateInit msg)) l.
Proof.
  intros.  proof_of (getStateInit_exec_P l msg). 
   (* zavisaet esli destruct (getStateInit_exec_P l msg ) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (getStateInit_exec_P l msg ) in e').
unfold getStateInit_exec_P.
  reflexivity.
  (* rewrite E. reflexivity. *) *)
Qed.


Definition getStateInit_eval_P (l : Ledger) ( msg : ULValue PhantomType ): 
{v | v = toValue (eval_state (Uinterpreter (getStateInit msg)) l)}.
  generate_proof (eval_expression l (getStateInit msg)).
Defined.
Definition getStateInit_auto_eval (l : Ledger) ( msg : ULValue PhantomType ): StateInitLRecord.
intros. term_of (getStateInit_eval_P l msg).
Defined.
Theorem getStateInit_eval_proof_next (l : Ledger) ( msg : ULValue PhantomType ) :
  getStateInit_auto_eval l msg =
  toValue (eval_state (Uinterpreter (getStateInit msg)) l).
Proof.
  intros. 
(*   destruct (getStateInit_eval_P l msg ) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (getStateInit_eval_P l msg ) in e').
unfold getStateInit_eval_P.
  reflexivity. *)
  proof_of (getStateInit_eval_P l msg).
Qed.



End getStateInit.

Section init.
Definition init_exec_P (l : Ledger) ( external_wallet : address ): 
{l' | l' = exec_state (Uinterpreter (init external_wallet)) l}.
  generate_proof (exec_expression l (init external_wallet)).
Defined.
Definition init_auto_exec (l : Ledger) ( external_wallet : address ): Ledger.
intros. term_of (init_exec_P l external_wallet).
Defined.

Theorem init_exec_proof_next (l : Ledger) ( external_wallet : address ) :
  init_auto_exec l external_wallet =
  exec_state (Uinterpreter (init external_wallet)) l.
Proof.
  intros. proof_of (init_exec_P l external_wallet).
Qed.


Definition init_eval_P (l : Ledger) ( external_wallet : address ): 
{v | v =  (eval_state (Uinterpreter (init external_wallet)) l)}.
  generate_proof (eval_expression l (init external_wallet)).
Defined.
Definition init_auto_eval (l : Ledger) ( external_wallet : address ): (ControlResult boolean true).
intros. term_of (init_eval_P l external_wallet).
Defined.
Theorem init_eval_proof_next (l : Ledger) ( external_wallet : address ) :
  init_auto_eval l external_wallet =
   (eval_state (Uinterpreter (init external_wallet)) l).
Proof.
  intros. proof_of (init_eval_P l external_wallet).
Qed.



End init.

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
  intros.
  (* destruct (is_internal_owner_exec_P l  ) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (is_internal_owner_exec_P l  ) in e').
unfold is_internal_owner_exec_P.
  reflexivity. *)
   proof_of (is_internal_owner_exec_P l ).
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
  intros. 
  (* destruct (is_internal_owner_eval_P l  ) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (is_internal_owner_eval_P l  ) in e').
unfold is_internal_owner_eval_P.
reflexivity. *)
  proof_of (is_internal_owner_eval_P l ).
Qed.



End is_internal_owner.

Section check_internal_owner.
Definition check_internal_owner_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (check_internal_owner )) l}.
  generate_proof (exec_expression l (check_internal_owner )).
Defined.
Definition check_internal_owner_auto_exec (l : Ledger) : Ledger.
intros. term_of (check_internal_owner_exec_P l ).
Defined.
Theorem check_internal_owner_exec_proof_next (l : Ledger)  :
  check_internal_owner_auto_exec l  =
  exec_state (Uinterpreter (check_internal_owner )) l.
Proof.
  intros. proof_of (check_internal_owner_exec_P l ).
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


End check_external_owner.

Section check_owner.
Definition check_owner_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (check_owner )) l}.
  generate_proof (exec_expression l (check_owner )).
Defined.
Definition check_owner_auto_exec (l : Ledger) : Ledger.
intros. term_of (check_owner_exec_P l ).
Defined.
Theorem check_owner_exec_proof_next (l : Ledger)  :
  check_owner_auto_exec l  =
  exec_state (Uinterpreter (check_owner )) l.
Proof.
  intros. 
(*   destruct (check_owner_exec_P l  ) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (check_owner_exec_P l  ) in e').
unfold check_owner_exec_P.
reflexivity. *)
  proof_of (check_owner_exec_P l ).
Qed.

End check_owner.

Section setInternalWalletCode.
Definition setInternalWalletCode_exec_P (l : Ledger) ( wallet_code : cell ): 
{l' | l' = exec_state (Uinterpreter (setInternalWalletCode wallet_code)) l}.
  generate_proof (exec_expression l (setInternalWalletCode wallet_code)).
Defined.
Definition setInternalWalletCode_auto_exec (l : Ledger) ( wallet_code : cell): Ledger.
intros. term_of (setInternalWalletCode_exec_P l wallet_code).
Defined.
Theorem setInternalWalletCode_exec_proof_next (l : Ledger) ( wallet_code : cell) :
  setInternalWalletCode_auto_exec l wallet_code =
  exec_state (Uinterpreter (setInternalWalletCode wallet_code)) l.
Proof.
  intros. proof_of (setInternalWalletCode_exec_P l wallet_code).
Qed.

Definition setInternalWalletCode_eval_P (l : Ledger) ( wallet_code : cell): 
{v | v =  (eval_state (Uinterpreter (setInternalWalletCode wallet_code)) l)}.
  generate_proof (eval_expression l (setInternalWalletCode wallet_code)).
Defined.
Definition setInternalWalletCode_auto_eval (l : Ledger) ( wallet_code : cell): (ControlResult boolean true).
intros. term_of (setInternalWalletCode_eval_P l wallet_code).
Defined.
Theorem setInternalWalletCode_eval_proof_next (l : Ledger) ( wallet_code : cell) :
  setInternalWalletCode_auto_eval l wallet_code =
   (eval_state (Uinterpreter (setInternalWalletCode wallet_code)) l).
Proof.
  intros. proof_of (setInternalWalletCode_eval_P l wallet_code).
Qed.

End setInternalWalletCode.

Section prepare_internal_wallet_state_init_and_addr.
Definition prepare_internal_wallet_state_init_and_addr_exec_P (l : Ledger) ( name :  String ) ( symbol : String )
 													   ( decimals : uint8 ) ( root_public_key : uint256 )
 													   ( wallet_public_key : uint256 ) ( root_address : address ) 
													   ( owner_address : optional address ) ( code : cell) 
													   ( workchain_id : int ): 
{l' | l' = exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l}.
  generate_proof (exec_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_exec (l : Ledger) ( name :  String ) ( symbol : String )
 													   ( decimals : uint8 ) ( root_public_key : uint256 )
 													   ( wallet_public_key : uint256 ) ( root_address : address ) 
													   ( owner_address : optional address ) ( code : cell) 
													   ( workchain_id : int ): Ledger.
intros. term_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( name :  String ) ( symbol : String )
 													   ( decimals : uint8 ) ( root_public_key : uint256 )
 													   ( wallet_public_key : uint256 ) ( root_address : address ) 
													   ( owner_address : optional address ) ( code : cell) 
													   ( workchain_id : int ) :
  prepare_internal_wallet_state_init_and_addr_auto_exec l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l.
Proof.
  intros. 
  destruct (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (prepare_internal_wallet_state_init_and_addr_exec_P l  name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id) in e').
unfold prepare_internal_wallet_state_init_and_addr_exec_P.
reflexivity.
  rewrite E. reflexivity.
  (* proof_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id). *)
Qed.




Definition prepare_internal_wallet_state_init_and_addr_eval_P (l : Ledger) ( name :  String ) ( symbol : String )
 													   ( decimals : uint8 ) ( root_public_key : uint256 )
 													   ( wallet_public_key : uint256 ) ( root_address : address ) 
													   ( owner_address : optional address ) ( code : cell) 
													   ( workchain_id : int ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l)}.
  generate_proof (eval_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_eval (l : Ledger) ( name :  String ) ( symbol : String )
 													   ( decimals : uint8 ) ( root_public_key : uint256 )
 													   ( wallet_public_key : uint256 ) ( root_address : address ) 
													   ( owner_address : optional address ) ( code : cell) 
													   ( workchain_id : int ): StateInitLRecord # uint256.
intros. term_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( name :  String ) ( symbol : String )
 													   ( decimals : uint8 ) ( root_public_key : uint256 )
 													   ( wallet_public_key : uint256 ) ( root_address : address ) 
													   ( owner_address : optional address ) ( code : cell) 
													   ( workchain_id : int ) :
  prepare_internal_wallet_state_init_and_addr_auto_eval l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l).
Proof.
  intros. 
  destruct (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (prepare_internal_wallet_state_init_and_addr_eval_P l  name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id) in e').
unfold prepare_internal_wallet_state_init_and_addr_eval_P;
reflexivity.
  rewrite E. reflexivity.
(*   proof_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id). *)
Qed.



End prepare_internal_wallet_state_init_and_addr.


Section optional_owner.
Definition optional_owner_exec_P (l : Ledger) ( owner : address ): 
{l' | l' = exec_state (Uinterpreter (optional_owner owner)) l}.
  generate_proof (exec_expression l (optional_owner owner)).
Defined.
Definition optional_owner_auto_exec (l : Ledger) ( owner : address ): Ledger.
intros. term_of (optional_owner_exec_P l owner).
Defined.
Theorem optional_owner_exec_proof_next (l : Ledger) ( owner : address ) :
  optional_owner_auto_exec l owner =
  exec_state (Uinterpreter (optional_owner owner)) l.
Proof.
  intros. proof_of (optional_owner_exec_P l owner).
Qed.

Definition optional_owner_eval_P (l : Ledger) ( owner : address ): 
{v | v = toValue (eval_state (Uinterpreter (optional_owner owner)) l)}.
  generate_proof (eval_expression l (optional_owner owner)).
Defined.
Definition optional_owner_auto_eval (l : Ledger) ( owner : address ): (optional address).
intros. term_of (optional_owner_eval_P l owner).
Defined.
Theorem optional_owner_eval_proof_next (l : Ledger) ( owner : address ) :
  optional_owner_auto_eval l owner =
  toValue (eval_state (Uinterpreter (optional_owner owner)) l).
Proof.
  intros. proof_of (optional_owner_eval_P l owner).
Qed.

End optional_owner.

Section calc_internal_wallet_init.
Definition calc_internal_wallet_init_exec_P (l : Ledger) ( pubkey :uint256 ) ( owner_addr : address ): 
{l' | l' = exec_state (Uinterpreter (calc_internal_wallet_init pubkey owner_addr)) l}.
  generate_proof (exec_expression l (calc_internal_wallet_init pubkey owner_addr)).
Defined.
Definition calc_internal_wallet_init_auto_exec (l : Ledger) ( pubkey :uint256 ) ( owner_addr : address ): Ledger.
intros. term_of (calc_internal_wallet_init_exec_P l pubkey owner_addr).
Defined.
Theorem calc_internal_wallet_init_exec_proof_next (l : Ledger) ( pubkey :uint256 ) ( owner_addr : address ) :
  calc_internal_wallet_init_auto_exec l pubkey owner_addr =
  exec_state (Uinterpreter (calc_internal_wallet_init pubkey owner_addr)) l.
Proof.
  intros. proof_of (calc_internal_wallet_init_exec_P l pubkey owner_addr).
Qed.



Definition calc_internal_wallet_init_eval_P (l : Ledger) ( pubkey :uint256 ) ( owner_addr : address ): 
{v | v =  (eval_state (Uinterpreter (calc_internal_wallet_init pubkey owner_addr)) l)}.
  generate_proof (eval_expression l (calc_internal_wallet_init pubkey owner_addr)).
Defined.
Definition calc_internal_wallet_init_auto_eval (l : Ledger) ( pubkey :uint256 ) ( owner_addr : address ): (ControlResult (StateInitLRecord # address) true).
intros. term_of (calc_internal_wallet_init_eval_P l pubkey owner_addr).
Defined.
Theorem calc_internal_wallet_init_eval_proof_next (l : Ledger) ( pubkey :uint256 ) ( owner_addr : address ) :
  calc_internal_wallet_init_auto_eval l pubkey owner_addr =
   (eval_state (Uinterpreter (calc_internal_wallet_init pubkey owner_addr)) l).
Proof.
  intros. proof_of_norm (calc_internal_wallet_init_eval_P l pubkey owner_addr). (* NORM *)
Qed.



End calc_internal_wallet_init.

Section deployEmptyWallet.
Definition deployEmptyWallet_exec_P (l : Ledger) ( pubkey : uint256 ) 
 						     ( internal_owner : address ) 
							 ( grams : uint128 ): 
{l' | l' = exec_state (Uinterpreter (deployEmptyWallet pubkey internal_owner grams)) l}.
  generate_proof (exec_expression l (deployEmptyWallet pubkey internal_owner grams)).
Defined.
Definition deployEmptyWallet_auto_exec (l : Ledger) ( pubkey : uint256 ) 
 						     ( internal_owner : address ) 
							 ( grams : uint128 ): Ledger.
intros. term_of (deployEmptyWallet_exec_P l pubkey internal_owner grams).
Defined.
Theorem deployEmptyWallet_exec_proof_next (l : Ledger) ( pubkey : uint256 ) 
 						     ( internal_owner : address ) 
							 ( grams : uint128 ) :
  deployEmptyWallet_auto_exec l pubkey internal_owner grams =
  exec_state (Uinterpreter (deployEmptyWallet pubkey internal_owner grams)) l.
Proof.
  intros. proof_of (deployEmptyWallet_exec_P l pubkey internal_owner grams).
Qed.

Definition deployEmptyWallet_eval_P (l : Ledger) ( pubkey : uint256 ) 
 						     ( internal_owner : address ) 
							 ( grams : uint128 ): 
{v | v =  (eval_state (Uinterpreter (deployEmptyWallet pubkey internal_owner grams)) l)}.
  generate_proof (eval_expression l (deployEmptyWallet pubkey internal_owner grams)).
Defined.
Definition deployEmptyWallet_auto_eval (l : Ledger) ( pubkey : uint256 ) 
 						     ( internal_owner : address ) 
							 ( grams : uint128 ): (ControlResult address true).
intros. term_of (deployEmptyWallet_eval_P l pubkey internal_owner grams).
Defined.
Theorem deployEmptyWallet_eval_proof_next (l : Ledger) ( pubkey : uint256 ) 
 						     ( internal_owner : address ) 
							 ( grams : uint128 ) :
  deployEmptyWallet_auto_eval l pubkey internal_owner grams =
   (eval_state (Uinterpreter (deployEmptyWallet pubkey internal_owner grams)) l).
Proof.
  intros. proof_of_norm (deployEmptyWallet_eval_P l pubkey internal_owner grams).
Qed.

End deployEmptyWallet.

Section expected_internal_address.
Definition expected_internal_address_exec_P (l : Ledger) ( sender_public_key :uint256 ) ( sender_owner_addr : address ): 
{l' | l' = exec_state (Uinterpreter (expected_internal_address sender_public_key sender_owner_addr)) l}.
  generate_proof (exec_expression l (expected_internal_address sender_public_key sender_owner_addr)).
Defined.
Definition expected_internal_address_auto_exec (l : Ledger) ( sender_public_key :uint256 ) ( sender_owner_addr : address ): Ledger.
intros. term_of (expected_internal_address_exec_P l sender_public_key sender_owner_addr).
Defined.
Theorem expected_internal_address_exec_proof_next (l : Ledger) ( sender_public_key :uint256 ) ( sender_owner_addr : address ) :
  expected_internal_address_auto_exec l sender_public_key sender_owner_addr =
  exec_state (Uinterpreter (expected_internal_address sender_public_key sender_owner_addr)) l.
Proof.
  intros. proof_of (expected_internal_address_exec_P l sender_public_key sender_owner_addr).
Qed.

Definition expected_internal_address_eval_P (l : Ledger) ( sender_public_key :uint256 ) ( sender_owner_addr : address ): 
{v | v = toValue (eval_state (Uinterpreter (expected_internal_address sender_public_key sender_owner_addr)) l)}.
  generate_proof (eval_expression l (expected_internal_address sender_public_key sender_owner_addr)).
Defined.
Definition expected_internal_address_auto_eval (l : Ledger) ( sender_public_key :uint256 ) ( sender_owner_addr : address ): address.
intros. term_of (expected_internal_address_eval_P l sender_public_key sender_owner_addr).
Defined.
Theorem expected_internal_address_eval_proof_next (l : Ledger) ( sender_public_key :uint256 ) ( sender_owner_addr : address ) :
  expected_internal_address_auto_eval l sender_public_key sender_owner_addr =
  toValue (eval_state (Uinterpreter (expected_internal_address sender_public_key sender_owner_addr)) l).
Proof.
  intros. proof_of (expected_internal_address_eval_P l sender_public_key sender_owner_addr).
Qed.

End expected_internal_address.

Section onTip3Transfer.
Definition onTip3Transfer_exec_P (l : Ledger) ( answer_addr : address ) 
						  ( balance : uint128 ) 
						  ( new_tokens : uint128 ) 
						  ( sender_pubkey :uint256 ) 
						  ( sender_owner : address ) 
						  ( payload : cell): 
{l' | l' = exec_state (Uinterpreter (onTip3Transfer answer_addr balance new_tokens sender_pubkey sender_owner payload)) l}.
  generate_proof (exec_expression l (onTip3Transfer answer_addr balance new_tokens sender_pubkey sender_owner payload)).
Defined.
Definition onTip3Transfer_auto_exec (l : Ledger) ( answer_addr : address ) 
						  ( balance : uint128 ) 
						  ( new_tokens : uint128 ) 
						  ( sender_pubkey :uint256 ) 
						  ( sender_owner : address ) 
						  ( payload : cell): Ledger.
intros. 
let t1 := (eval unfold onTip3Transfer_exec_P in
(let (e, _) := onTip3Transfer_exec_P l answer_addr balance new_tokens sender_pubkey sender_owner payload in e)) in exact t1.
(* term_of (onTip3Transfer_exec_P l answer_addr balance new_tokens sender_pubkey sender_owner payload). *)
Defined.

(* DOLGO *)
Theorem onTip3Transfer_exec_proof_next (l : Ledger) ( answer_addr : address ) 
						  ( balance : uint128 ) 
						  ( new_tokens : uint128 ) 
						  ( sender_pubkey :uint256 ) 
						  ( sender_owner : address ) 
						  ( payload : cell) :
  onTip3Transfer_auto_exec l answer_addr balance new_tokens sender_pubkey sender_owner payload =
  exec_state (Uinterpreter (onTip3Transfer answer_addr balance new_tokens sender_pubkey sender_owner payload)) l.
Proof.
  intros. 
  destruct (onTip3Transfer_exec_P l answer_addr balance new_tokens sender_pubkey sender_owner payload) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (onTip3Transfer_exec_P l  answer_addr balance new_tokens sender_pubkey sender_owner payload) in e').
unfold onTip3Transfer_exec_P;
reflexivity.
  rewrite E. reflexivity.
  (* proof_of (onTip3Transfer_exec_P l answer_addr balance new_tokens sender_pubkey sender_owner payload). *)
Qed.

Definition onTip3Transfer_eval_P (l : Ledger) ( answer_addr : address ) 
						  ( balance : uint128 ) 
						  ( new_tokens : uint128 ) 
						  ( sender_pubkey :uint256 ) 
						  ( sender_owner : address ) 
						  ( payload : cell): 
{v | v =  (eval_state (Uinterpreter (onTip3Transfer answer_addr balance new_tokens sender_pubkey sender_owner payload)) l)}.
  generate_proof (eval_expression l (onTip3Transfer answer_addr balance new_tokens sender_pubkey sender_owner payload)).
Defined.
Definition onTip3Transfer_auto_eval (l : Ledger) ( answer_addr : address ) 
						  ( balance : uint128 ) 
						  ( new_tokens : uint128 ) 
						  ( sender_pubkey :uint256 ) 
						  ( sender_owner : address ) 
						  ( payload : cell): (ControlResult WrapperRetLRecord true).
intros. 
let t1 := (eval unfold onTip3Transfer_eval_P in
(let (e, _) := onTip3Transfer_eval_P l answer_addr balance new_tokens sender_pubkey sender_owner payload in e)) in exact t1.

(* term_of (onTip3Transfer_eval_P l answer_addr balance new_tokens sender_pubkey sender_owner payload). *)
Defined. (* DOLGO *)
Theorem onTip3Transfer_eval_proof_next (l : Ledger) ( answer_addr : address ) 
						  ( balance : uint128 ) 
						  ( new_tokens : uint128 ) 
						  ( sender_pubkey :uint256 ) 
						  ( sender_owner : address ) 
						  ( payload : cell) :
  onTip3Transfer_auto_eval l answer_addr balance new_tokens sender_pubkey sender_owner payload =
   (eval_state (Uinterpreter (onTip3Transfer answer_addr balance new_tokens sender_pubkey sender_owner payload)) l).
Proof.
  intros. 
  destruct (onTip3Transfer_eval_P l answer_addr balance new_tokens sender_pubkey sender_owner payload) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (onTip3Transfer_eval_P l  answer_addr balance new_tokens sender_pubkey sender_owner payload) in e').
unfold onTip3Transfer_eval_P;
reflexivity.
  rewrite E. reflexivity.
  (* proof_of (onTip3Transfer_eval_P l answer_addr balance new_tokens sender_pubkey sender_owner payload). *)
Qed.

End onTip3Transfer.

Section burn.
Definition burn_exec_P (l : Ledger) ( answer_addr : address ) ( sender_pubkey :uint256 ) 
			    ( sender_owner : address ) ( out_pubkey :uint256 ) 
				( out_internal_owner : address ) ( tokens : uint128 ): 
{l' | l' = exec_state (Uinterpreter (burn answer_addr sender_pubkey sender_owner out_pubkey out_internal_owner tokens)) l}.
  generate_proof (exec_expression l (burn answer_addr sender_pubkey sender_owner out_pubkey out_internal_owner tokens)).
Defined.
Definition burn_auto_exec (l : Ledger) ( answer_addr : address ) ( sender_pubkey :uint256 ) 
			    ( sender_owner : address ) ( out_pubkey :uint256 ) 
				( out_internal_owner : address ) ( tokens : uint128 ): Ledger.
intros. term_of (burn_exec_P l answer_addr sender_pubkey sender_owner out_pubkey out_internal_owner tokens).
Defined.
Theorem burn_exec_proof_next (l : Ledger) ( answer_addr : address ) ( sender_pubkey :uint256 ) 
			    ( sender_owner : address ) ( out_pubkey :uint256 ) 
				( out_internal_owner : address ) ( tokens : uint128 ) :
  burn_auto_exec l answer_addr sender_pubkey sender_owner out_pubkey out_internal_owner tokens =
  exec_state (Uinterpreter (burn answer_addr sender_pubkey sender_owner out_pubkey out_internal_owner tokens)) l.
Proof.
  intros. proof_of (burn_exec_P l answer_addr sender_pubkey sender_owner out_pubkey out_internal_owner tokens).
Qed.


End burn.


Section requestTotalGranted.
Definition requestTotalGranted_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (requestTotalGranted )) l}.
  generate_proof (exec_expression l (requestTotalGranted )).
Defined.
Definition requestTotalGranted_auto_exec (l : Ledger) : Ledger.
intros. term_of (requestTotalGranted_exec_P l ).
Defined.
Theorem requestTotalGranted_exec_proof_next (l : Ledger)  :
  requestTotalGranted_auto_exec l  =
  exec_state (Uinterpreter (requestTotalGranted )) l.
Proof.
  intros. proof_of (requestTotalGranted_exec_P l ).
Qed.

Definition requestTotalGranted_eval_P (l : Ledger) : 
{v | v = toValue (eval_state (Uinterpreter (requestTotalGranted )) l)}.
  generate_proof (eval_expression l (requestTotalGranted )).
Defined.
Definition requestTotalGranted_auto_eval (l : Ledger) : XUInteger128.
intros. term_of (requestTotalGranted_eval_P l ).
Defined.
Theorem requestTotalGranted_eval_proof_next (l : Ledger)  :
  requestTotalGranted_auto_eval l  =
  toValue (eval_state (Uinterpreter (requestTotalGranted )) l).
Proof.
  intros. proof_of (requestTotalGranted_eval_P l ).
Qed.

End requestTotalGranted.

Section _on_bounced.
Definition _on_bounced_exec_P (l : Ledger) ( a :  cell) ( msg_body : slice ): 
{l' | l' = exec_state (Uinterpreter (_on_bounced a msg_body)) l}.
  generate_proof (exec_expression l (_on_bounced a msg_body)).
Defined.
Definition _on_bounced_auto_exec (l : Ledger) ( a :  cell) ( msg_body : slice ): Ledger.
intros. term_of (_on_bounced_exec_P l a  msg_body).
Defined.
Theorem _on_bounced_exec_proof_next (l : Ledger) ( a :  cell) ( msg_body : slice ) :
  _on_bounced_auto_exec l a  msg_body =
  exec_state (Uinterpreter (_on_bounced a  msg_body)) l.
Proof.
  intros. proof_of (_on_bounced_exec_P l a  msg_body).
Qed.

Definition _on_bounced_eval_P (l : Ledger) ( a :  cell) ( msg_body : slice ): 
{v | v =  (eval_state (Uinterpreter (_on_bounced a  msg_body)) l)}.
  generate_proof (eval_expression l (_on_bounced a  msg_body)).
Defined.
Definition _on_bounced_auto_eval (l : Ledger) ( a :  cell) ( msg_body : slice ): (ControlResult XUInteger true).
intros. term_of (_on_bounced_eval_P l a  msg_body).
Defined.
Theorem _on_bounced_eval_proof_next (l : Ledger) ( a :  cell) ( msg_body : slice ) :
  _on_bounced_auto_eval l a  msg_body =
   (eval_state (Uinterpreter (_on_bounced a  msg_body)) l).
Proof.
  intros. proof_of (_on_bounced_eval_P l a  msg_body).
Qed.


End _on_bounced.

Section prepare_wrapper_state_init_and_addr.
Definition prepare_wrapper_state_init_and_addr_exec_P (l : Ledger) ( wrapper_code : cell) ( wrapper_data : ( DWrapperLRecord ) ): 
{l' | l' = exec_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l}.
  generate_proof (exec_expression l (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)).
Defined.
Definition prepare_wrapper_state_init_and_addr_auto_exec (l : Ledger) ( wrapper_code : cell) ( wrapper_data : ( DWrapperLRecord ) ): Ledger.
intros. term_of (prepare_wrapper_state_init_and_addr_exec_P l wrapper_code wrapper_data).
Defined.
Theorem prepare_wrapper_state_init_and_addr_exec_proof_next (l : Ledger) ( wrapper_code : cell) ( wrapper_data : ( DWrapperLRecord ) ) :
  prepare_wrapper_state_init_and_addr_auto_exec l wrapper_code wrapper_data =
  exec_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l.
Proof.
  intros. 
  destruct (prepare_wrapper_state_init_and_addr_exec_P l wrapper_code wrapper_data) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (prepare_wrapper_state_init_and_addr_exec_P l  wrapper_code wrapper_data) in e').
unfold prepare_wrapper_state_init_and_addr_exec_P;
reflexivity.
  rewrite E. reflexivity.
(*   proof_of (prepare_wrapper_state_init_and_addr_exec_P l wrapper_code wrapper_data). *)
Qed.



Definition prepare_wrapper_state_init_and_addr_eval_P (l : Ledger) ( wrapper_code : cell) ( wrapper_data : ( DWrapperLRecord ) ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l)}.
  generate_proof (eval_expression l (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)).
Defined.
Definition prepare_wrapper_state_init_and_addr_auto_eval (l : Ledger) ( wrapper_code : cell) ( wrapper_data : ( DWrapperLRecord ) ): StateInitLRecord # XUInteger256.
intros. term_of (prepare_wrapper_state_init_and_addr_eval_P l wrapper_code wrapper_data).
Defined.
Theorem prepare_wrapper_state_init_and_addr_eval_proof_next (l : Ledger) ( wrapper_code : cell) ( wrapper_data : ( DWrapperLRecord ) ) :
  prepare_wrapper_state_init_and_addr_auto_eval l wrapper_code wrapper_data =
  toValue (eval_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l).
Proof.
  intros. 
  destruct (prepare_wrapper_state_init_and_addr_eval_P l wrapper_code wrapper_data) as [e H] eqn:E. rewrite <- H. replace e with
  (let (e', _) := (prepare_wrapper_state_init_and_addr_eval_P l  wrapper_code wrapper_data) in e').
unfold prepare_wrapper_state_init_and_addr_eval_P;
reflexivity.
  rewrite E. reflexivity.
  (* proof_of (prepare_wrapper_state_init_and_addr_eval_P l wrapper_code wrapper_data). *)
Qed.



End prepare_wrapper_state_init_and_addr.