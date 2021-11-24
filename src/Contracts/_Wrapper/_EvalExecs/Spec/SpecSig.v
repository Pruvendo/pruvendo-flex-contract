Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
Require Import FinProof.StateMonad21.

Require Import UMLang.ProofEnvironment2.
Require Import UMLang.SML_NG28.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Ledger.
Require Import FuncSig.
Require Import FuncNotations.

Module trainContractSpecModuleForSpec := trainContractSpec XTypesModule StateMonadModule.

Module trainEvalExec (dc : trainConstsTypesSig XTypesModule StateMonadModule).

Module Export trainFuncNotationsModule := trainFuncNotations XTypesModule StateMonadModule dc. 

Module Type trainEvalExecSig (tc: trainContractSpecSig) .
 
Module Import FuncExForSpec := FuncEx tc.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Locate "constructor_ ( _ )".

Axiom constructor_exec: forall (l: Ledger) (depth: uint) , 
      exec_state (Uinterpreter {{ constructor_ ( #{depth} ) }} ) l = l.


Axiom constructor_eval: forall (l: Ledger) (depth: uint) , 
      eval_state (sRReader || constructor_ ( #{depth} ) || ) l = ControlValue true PhantomPoint.


Axiom deploy_exec: forall (l: Ledger) (value: uint) , 
      exec_state (Uinterpreter {{ deploy_ ( #{value} ) }} ) l = l.

Axiom deploy_eval: forall (l: Ledger) (value: uint) , 
      eval_state (sRReader || deploy_ ( #{value} ) || ) l = ControlValue false default.

End trainEvalExecSig.

End trainEvalExec.