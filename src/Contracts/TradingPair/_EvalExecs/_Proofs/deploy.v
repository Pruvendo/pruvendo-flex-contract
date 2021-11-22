Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import FinProof.Common. 
Require Import FinProof.StateMonad21.
Require Import FinProof.ProgrammingWith.

Require Import UMLang.ProofEnvironment2.
Require Import UMLang.SML_NG28.

Require Import UrsusTVM.tvmNotations.

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


Lemma deploy_exec: forall (l: Ledger) (value: XInteger) , 
      exec_state (Uinterpreter {{ deploy_ ( #{value} ) }} ) l = l.
Admitted.


Lemma deploy_eval: forall (l: Ledger) (value: XInteger) , 
      eval_state (sRReader || deploy_ ( #{value} ) || ) l = ControlValue false default.
Admitted.



End constructorEvalExec. 