Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import List.
Import ListNotations.


Local Open Scope program_scope. 

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.StateMonad21. 
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.ProofEnvironment2.

Require Import trainContractTypes.
Require Import trainContractClass.
Require Import trainContractConsts.  
Require Import trainContractConstSig. 
(* Require Import trainContractVariables.
Require Import trainContractVars. *)
Require Import ZArith.
Require Import trainFuncNotations.

Module trainFuncExamples (* (xt: XTypesSig) 
               (sm: StateMonadSig)  *)
               (dc : trainConstsTypesSig XTypesModule StateMonadModule ).
 
Module Export trainFuncNotationsModule := trainFuncNotations XTypesModule StateMonadModule dc.
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.

Definition test_ref (a b: XBool): UExpression XInteger false :=
    {{
       a : XBool @ "a" ;
       b : XBool @ "b" ;
       {b} := !{a} ;
       record1.B := 0
    }}.

Definition test_ref_call {b} (x: URValue XBool b) (y: ULValue XBool) := 
   🏓 ursus_call_with_args (LedgerableWithArgs := λ2) test_ref 
   (SimpleLedgerableArg URValue {{ Λ "a" }} (local_right_copy x)) (RefLedgerableArg URValue {{ Λ "b" }} (local_left_copy y)) .

Notation " 'test_ref_' '(' x , y ')' " := ( URResult (test_ref_call x y))  
   (in custom URValue at level 0 , x custom URValue at level 0, y custom ULValue at level 0) : ursus_scope.

Notation " 'test_ref_' '(' x , y ')' " := ( FuncallExpression (test_ref_call x y))  
   (in custom ULValue at level 0 , x custom URValue at level 0, y custom ULValue at level 0) : ursus_scope.

Definition bar33 (b0 b1: XBool): UExpression XBool false :=
{{
   b0 : XBool @ "b0";
   b1 : XBool @ "b1";

   test_ref_ ( !{b0} , {b1} ) ;

   new 'b : XBool @ "b" := !{b1} ; record1.B := 0 ;
   return_ !{b}
}}.


Definition bar33_call (x y: URValue XBool false)  := 
   🏓 ursus_call_with_args (LedgerableWithArgs := λ2) bar33 
(SimpleLedgerableArg URValue {{ Λ "b0" }} x) (SimpleLedgerableArg URValue {{ Λ "b1" }} y) .


Notation " 'bar33_' '(' x , y ')' " := ( URResult (bar33_call x y))  
   (in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Notation " 'bar33_' '(' x , y ')' " := ( FuncallExpression (bar33_call x y))  
   (in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Lemma exec_bar33_correct: forall (a b: XBool) (l:Ledger), 
(*    let new_int_ls : XHMap (string*nat) XBool := (xHMapEmpty [("b0", 0%nat)] ← a) [("b1", 0%nat)] ← b in  *)
   let l1 := {$$ l ₁ with default ⇒ record1_ι_C $$} in
   exec_state ( Uinterpreter  {{ bar33_ ( #{a} , #{b} ) }} ) l  = 
   ( l ₁ , l ₂ , l ₃ , l ₄ , default, default).
Proof.
   intros.
   destruct l.
   repeat destruct p.
   compute.
   reflexivity.
Qed.      


Lemma eval_bar33_correct: forall (a b: XBool) (l:Ledger), 
   eval_state ( sRReader || bar33_ ( #{a} , #{b} ) || ) l = 
   ControlValue false a.
Proof.
   intros.
   destruct l.
   repeat destruct p.
   compute.
   reflexivity.
Qed.

End trainFuncExamples.