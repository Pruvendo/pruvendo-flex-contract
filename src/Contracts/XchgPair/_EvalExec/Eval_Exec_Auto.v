
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

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonAxioms.
Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.

(*Fully qualified name are mandatory in multi-contract environment*)
Require Import XchgPair.ClassTypes.
Require Import XchgPair.Ledger.
Require Import XchgPair.Functions.FuncSig.
Require Import XchgPair.Functions.FuncNotations.
Require Import XchgPair.Functions.Funcs.

(* Require Contracts.XchgPair.Interface. *)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.

Module EvalExecAuto (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .

Module Export FuncsModule := Funcs co dc.

Import FuncsInternal.

Import co.

(* Module Import xxx := SpecModuleForFuncNotations.LedgerModuleForFuncSig.

Module Import generator := execGenerator XTypesModule StateMonadModule xxx.

 *)
(* 
Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 *) 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

(* Import URSUS_.
 *)
Section onDeploy.

Definition onDeploy_exec_P (l : Ledger) (min_amount: uint128) (deploy_value: uint128) (notify_addr: address): 
{l' | l' = exec_state (Uinterpreter (onDeploy min_amount deploy_value notify_addr)) l}.
  generate_proof (exec_expression l (onDeploy min_amount deploy_value notify_addr)).
Defined.
Definition onDeploy_auto_exec (l : Ledger) (min_amount: uint128) (deploy_value: uint128) (notify_addr: address): Ledger.
intros. term_of (onDeploy_exec_P l min_amount deploy_value notify_addr).
Defined.
Theorem onDeploy_exec_proof_next (l : Ledger) (min_amount: uint128) (deploy_value: uint128) (notify_addr: address) :
  onDeploy_auto_exec l min_amount deploy_value notify_addr =
  exec_state (Uinterpreter (onDeploy min_amount deploy_value notify_addr)) l.
Proof.
  intros. proof_of (onDeploy_exec_P l min_amount deploy_value notify_addr).
Qed.

Definition onDeploy_eval_P (l : Ledger) (min_amount: uint128) (deploy_value: uint128) (notify_addr: address): 
{v | v =  (eval_state (Uinterpreter (onDeploy min_amount deploy_value notify_addr)) l)}.
  generate_proof (eval_expression l (onDeploy min_amount deploy_value notify_addr)).
Defined.
Definition onDeploy_auto_eval (l : Ledger) (min_amount: uint128) (deploy_value: uint128) (notify_addr: address): (ControlResult boolean true).
intros. term_of (onDeploy_eval_P l min_amount deploy_value notify_addr).
Defined.
Theorem onDeploy_eval_proof_next (l : Ledger) (min_amount: uint128) (deploy_value: uint128) (notify_addr: address) :
  onDeploy_auto_eval l min_amount deploy_value notify_addr =
   (eval_state (Uinterpreter (onDeploy min_amount deploy_value notify_addr)) l).
Proof.
  intros. proof_of (onDeploy_eval_P l min_amount deploy_value notify_addr).
Qed.

End onDeploy.


Section prepare_xchg_pair_state_init_and_addr.
Definition prepare_xchg_pair_state_init_and_addr_exec_P (l : Ledger) ( pair_data : ContractLRecord ) 
                                                 ( pair_code : TvmCells.cell ): 
{l' | l' = exec_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l}.
  generate_proof (exec_expression l (prepare_xchg_pair_state_init_and_addr pair_data pair_code)).
Defined.
Definition prepare_xchg_pair_state_init_and_addr_auto_exec (l : Ledger) ( pair_data : ContractLRecord ) 
                                                 ( pair_code : TvmCells.cell ): Ledger.
intros. term_of (prepare_xchg_pair_state_init_and_addr_exec_P l pair_data pair_code).
Defined.
Theorem prepare_xchg_pair_state_init_and_addr_exec_proof_next (l : Ledger) ( pair_data : ContractLRecord ) 
                                                 ( pair_code : TvmCells.cell ) :
  prepare_xchg_pair_state_init_and_addr_auto_exec l pair_data pair_code =
  exec_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l.
Proof.
  intros. proof_of (prepare_xchg_pair_state_init_and_addr_exec_P l pair_data pair_code).
Qed.



Definition prepare_xchg_pair_state_init_and_addr_eval_P (l : Ledger) ( pair_data : ContractLRecord ) 
                                                 ( pair_code : TvmCells.cell ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l)}.
generate_proof (eval_expression l (prepare_xchg_pair_state_init_and_addr pair_data pair_code)).
Defined.
Definition prepare_xchg_pair_state_init_and_addr_auto_eval (l : Ledger) ( pair_data : ContractLRecord ) 
                                                 ( pair_code : TvmCells.cell ): StateInitLRecord # uint256.
intros. term_of (prepare_xchg_pair_state_init_and_addr_eval_P l pair_data pair_code).
Defined.
Theorem prepare_xchg_pair_state_init_and_addr_eval_proof_next (l : Ledger) ( pair_data : ContractLRecord ) 
                                                 ( pair_code : TvmCells.cell ) :
  prepare_xchg_pair_state_init_and_addr_auto_eval l pair_data pair_code =
  toValue (eval_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l).
Proof.
   proof_of (prepare_xchg_pair_state_init_and_addr_eval_P l pair_data pair_code).
Qed.



End prepare_xchg_pair_state_init_and_addr.
