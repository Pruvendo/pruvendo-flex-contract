Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
Require Import FinProof.StateMonad21.

Require Import UMLang.ProofEnvironment2.
Require Import UMLang.SML_NG28.

Require Import UrsusTVM.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Contracts.Flex.Ledger.
Require Import Contracts.Flex.Functions.FuncSig.
Require Import Contracts.Flex.Functions.FuncNotations.

Module FlexSpecModuleForSpec := FlexSpec XTypesModule StateMonadModule.

Module FlexEvalExec (dc : ConstsTypesSig XTypesModule StateMonadModule).

Module Export FlexFuncNotationsModule := FlexFuncNotations XTypesModule StateMonadModule dc. 

Module Type FlexEvalExecSig (tc: FlexSpecSig) .
 
Module Import FuncExForSpec := Calls tc.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Locate "constructor_ ( _ )".

(* Axiom constructor_exec: forall (l: Ledger) (depth: XInteger) , 
      exec_state (Uinterpreter {{ constructor_ ( #{depth} ) }} ) l = l.


Axiom constructor_eval: forall (l: Ledger) (depth: XInteger) , 
      eval_state (sRReader || constructor_ ( #{depth} ) || ) l = ControlValue true PhantomPoint.


Axiom deploy_exec: forall (l: Ledger) (value: XInteger) , 
      exec_state (Uinterpreter {{ deploy_ ( #{value} ) }} ) l = l.

Axiom deploy_eval: forall (l: Ledger) (value: XInteger) , 
      eval_state (sRReader || deploy_ ( #{value} ) || ) l = ControlValue false default.
 *)
End FlexEvalExecSig.

End FlexEvalExec.