Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 


Require Import FinProof.Common. 
Require Import FinProof.StateMonad21.
Require Import FinProof.ProgrammingWith.

Require Import UMLang.ProofEnvironment2.
Require Import UMLang.SML_NG28.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Ledger.
Require Import FuncSig.
Require Import FuncNotations.

Require Import Funcs.

Module constructorEvalExec (dc : trainConstsTypesSig XTypesModule StateMonadModule).

Module Import trainContractFuncs := trainFuncs dc.

Import UrsusNotations.
Local Open Scope ursus_scope.

Module Import FuncExForEvalExec := FuncEx trainFuncsInternal.


Lemma constructor_exec: forall (l: Ledger) (depth: uint) , 
      exec_state (Uinterpreter {{ constructor_ ( #{depth} ) }} ) l = l.
Admitted.


Lemma constructor_eval: forall (l: Ledger) (depth: uint) , 
      eval_state (sRReader || constructor_ ( #{depth} ) || ) l = ControlValue true PhantomPoint.
Admitted.



End constructorEvalExec. 