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

Require Import FLeXContractTypes.
Require Import classFlex.
Require Import FLeXConstSig.  
Require Import ZArith.
Require Import FLeXFuncNotations.
Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG25.

Module stdFuncProofs (* (xt: XTypesSig) 
               (sm: StateMonadSig)  *)
               (dc : FLeXConstsTypesSig XTypesModule StateMonadModule )  (cs : ClassSig XTypesModule).
Import cs.
Module Export FLeXFuncNotationsModule := FLeXFuncNotations XTypesModule StateMonadModule dc.
Import SMLNotations.
Local Open Scope sml_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.






Definition plusassign (a b: XInteger) : SMLExpression  XInteger false :=
    {{
        a : XInteger @ "a" ; b : XInteger @ "b" ;
       { a } := !{a} + !{b}
    }}.



Definition test_ref (a b: XBool): SMLExpression XInteger false :=
    {{
       a : XBool @ "a" ;
       b : XBool @ "b" ;
       {b} := !{a}
    }}.

Definition test_ref_call {b} (x: SMLRValue XBool b) (y: SMLLValue XBool) := 
   🏓 sml_call_with_args (LedgerableWithArgs := λ2) test_ref 
   (SimpleLedgerableArg SMLRValue {{ Λ "a" }} (local_right_copy x)) (RefLedgerableArg SMLRValue {{ Λ "b" }} (local_left_copy y)) .

Notation " 'test_ref_' '(' x , y ')' " := ( SMLRResult (test_ref_call x y))  
   (in custom SMLRValue at level 0 , x custom SMLRValue at level 0, y custom SMLLValue at level 0) : sml_scope.

Notation " 'test_ref_' '(' x , y ')' " := ( FuncallExpression (test_ref_call x y))  
   (in custom SMLLValue at level 0 , x custom SMLRValue at level 0, y custom SMLLValue at level 0) : sml_scope.

Definition bar33 (b0 b1: XBool): SMLExpression XBool false :=
{{
   b0 : XBool @ "b0";
   b1 : XBool @ "b1";

   test_ref_ ( !{b0} , {b1} ) ;

   new 'b : XBool @ "b" := !{b1} ;
   return_ !{b}
}}.


Definition bar33_call (x y: SMLRValue XBool false)  := 
   🏓 sml_call_with_args (LedgerableWithArgs := λ2) bar33 
(SimpleLedgerableArg SMLRValue {{ Λ "b0" }} x) (SimpleLedgerableArg SMLRValue {{ Λ "b1" }} y) .


Notation " 'bar33_' '(' x , y ')' " := ( SMLRResult (bar33_call x y))  
   (in custom SMLRValue at level 0 , x custom SMLRValue at level 0, y custom SMLRValue at level 0) : sml_scope.

Notation " 'bar33_' '(' x , y ')' " := ( FuncallExpression (bar33_call x y))  
   (in custom SMLLValue at level 0 , x custom SMLRValue at level 0, y custom SMLRValue at level 0) : sml_scope.

Lemma exec_bar33_correct: forall (a b: XBool) (l:Ledger), 
(*    let new_int_ls : XHMap (string*nat) XBool := (xHMapEmpty [("b0", 0%nat)] ← a) [("b1", 0%nat)] ← b in  *)
   let l1 := {$$ l ₁ with default ⇒ record1_ι_C $$} in
   exec_state ( SMLinterpreter  {{ bar33_ ( #{a} , #{b} ) }} ) l  = 
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

End FLeXFuncExamples.