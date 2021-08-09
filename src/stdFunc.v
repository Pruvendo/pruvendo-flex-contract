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
Require Import UMLang.ProofEnvironment2.

Require Import FLeXContractTypes.  
Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG25.

Module Type ClassSig' (xt : XTypesSig) <: ClassSig xt.
Include (ClassSig xt). (* ClassSig xt. *)
Import xt.
Parameter LocalStateField_XInteger : LocalStateField XInteger.
Parameter LocalStateField_XBool : LocalStateField XBool.
End ClassSig'.

(* Print Module Type ClassSig'. *)

Module stdFunc   (xt : XTypesSig) (sm : StateMonadSig) (cs : ClassSig' xt).
Import cs.
(* Module Import LedgerClass := LedgerClass XTypesModule StateMonadModule.  *)
(* Import SolidityNotationsClass. *)
Module Export URSUS := URSUS xt sm cs.
Import UrsusNotations.

Module Export SolidityNotationsModule := SolidityNotations xt sm.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Existing Instance LocalStateField_XInteger.
Existing Instance LocalStateField_XBool.

Definition plusassign (a b: XInteger) : UExpression  XInteger false :=
{{
    a : XInteger @ "a" ; b : XInteger @ "b" ;
    { a } := !{a} + !{b}
}}.

Definition minusassign (a b: XInteger) : UExpression  XInteger false :=
{{
    a : XInteger @ "a" ; b : XInteger @ "b" ;
    { a } := !{a} - !{b}
}}.   

Definition incr (a: XInteger) : UExpression  XInteger false :=
{{
    a : XInteger @ "a";
    {a} := !{a} + 1
}}.

Definition decr (a: XInteger) : UExpression XInteger false :=
{{
    a : XInteger @ "a";
    {a} := !{a} - 1
}}.

Definition sum (a b :XInteger) : UExpression XInteger false := 
{{ 
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_ !{a} + !{b}
}}.

Definition minus (a b :XInteger) : UExpression XInteger false := 
{{
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_  !{a} - !{b}
}}.

Definition prod (a b :XInteger) : UExpression XInteger false := 
{{
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_ !{a} * !{b}
}}.

Definition div (a b :XInteger) : UExpression XInteger false := 
{{
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_ !{a} / !{b}
}}.

Definition andbu (a b :XBool) : UExpression XBool false := 
{{
    a : XBool @ "a";
    b : XBool @ "b";
    return_  !{a} and !{b}
}}.

Definition orbu (a b :XBool) : UExpression XBool false := 
{{
    a : XBool @ "a";
    b : XBool @ "b";
    return_ !{a} or !{b}
}}.

Definition nebu (a:XBool) : UExpression XBool false := 
{{
    a : XBool @ "a";
    return_ ~ !{a}
}}.

 
Definition leb (a b:XInteger) : UExpression XBool false := 
{{
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_ !{a} <=  !{b}
}}.

Definition geb (a b:XInteger) : UExpression XBool false := 
{{
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_ ! {a} >= ! {b}
}}.

Definition le (a b:XInteger) : UExpression XBool false := 
{{
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_ !{a} <  !{b}
}}.

Definition ge (a b:XInteger) : UExpression XBool false := 
{{
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_ !{a} >  !{b}
}}.
   
Definition eqbu (a b:XInteger) : UExpression XBool false := 
{{
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_ !{a} == !{b}
}}.

Definition neqbu (a b:XInteger) : UExpression XBool false := 
{{
    a : XInteger @ "a";
    b : XInteger @ "b";
    return_ !{a} != !{b}
}}.


End stdFunc.
            