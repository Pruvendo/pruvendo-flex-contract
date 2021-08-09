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
 
Require Import ZArith.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG25.
Require Import stdFunc.

Module stdFuncNotations (xt: XTypesSig) (sm: StateMonadSig)  (cs : ClassSig' xt) .

Module Export stdFuncModule := stdFunc xt sm cs.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.

Definition plusassign_call {b} (x: ULValue XInteger) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) plusassign 
    (RefLedgerableArg URValue {{ Λ "a" }} (local_left_copy x)) (SimpleLedgerableArg URValue {{ Λ "b" }} (local_right_copy y)).
 
Notation " 'plusassign_' '(' x , y ')' " := ( FuncallExpression (plusassign_call x y))  
    (in custom ULValue at level 0 , x custom ULValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition minusassign_call {b} (x: ULValue XInteger) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) minusassign 
    (RefLedgerableArg URValue {{ Λ "a" }} (local_left_copy x)) (SimpleLedgerableArg URValue {{ Λ "b" }} (local_right_copy y)).

Notation " 'minusassign_' '(' x , y ')' " := ( FuncallExpression (minusassign_call x y))  
    (in custom ULValue at level 0 , x custom ULValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition incr_call  (x: ULValue XInteger)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ1) incr 
    (RefLedgerableArg URValue {{ Λ "a" }} (local_left_copy x)).

Notation " 'incr_' '(' x ')' " := ( FuncallExpression (incr_call x))  
    (in custom ULValue at level 0 , x custom ULValue at level 0) : ursus_scope.


Definition decr_call  (x: ULValue XInteger)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ1) decr 
    (RefLedgerableArg URValue {{ Λ "a" }} (local_left_copy x)).

Notation " 'decr_' '(' x ')' " := ( FuncallExpression (decr_call x))  
    (in custom ULValue at level 0 , x custom ULValue at level 0) : ursus_scope.


Definition sum_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) sum 
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
    
    
Notation " 'sum_' '(' x , y ')' " := ( URResult (sum_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'sum_' '(' x , y ')' " := ( FuncallExpression (sum_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition minus_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) minus 
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
 Notation " 'minus_' '(' x , y ')' " := ( URResult (minus_call x y))  
    (in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.
    
 
 Notation " 'minus_' '(' x , y ')' " := ( FuncallExpression (sum_call x y))  
    (in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition prod_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) prod
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).    

Notation " 'prod_' '(' x , y ')' " := ( URResult (prod_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'prod_' '(' x , y ')' " := ( FuncallExpression (prod_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition div_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) div
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
Notation " 'div_' '(' x , y ')' " := ( URResult (div_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'div_' '(' x , y ')' " := ( FuncallExpression (div_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition andbu_call {b} (x: URValue XBool b) (y: URValue XBool b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) andbu
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
Notation " 'andbu_' '(' x , y ')' " := ( URResult (andbu_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'andbu_' '(' x , y ')' " := ( FuncallExpression (andbu_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition orbu_call {b} (x: URValue XBool b) (y: URValue XBool b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) orbu
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
Notation " 'orbu_' '(' x , y ')' " := ( URResult (orbu_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'orbu_' '(' x , y ')' " := ( FuncallExpression (orbu_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition nebu_call {b} (x: URValue XBool b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ1) nebu
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x).
 
 
Notation " 'nebu_' '(' x ')' " := ( URResult (nebu_call x ))  
(in custom URValue at level 0 , x custom URValue at level 0) : ursus_scope.


Notation " 'nebu_' '(' x ')' " := ( FuncallExpression (nebu_call x))  
(in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.

Definition leb_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) leb
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
Notation " 'leb_' '(' x , y ')' " := ( URResult (leb_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'leb_' '(' x , y ')' " := ( FuncallExpression (leb_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition geb_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) geb
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
Notation " 'geb_' '(' x , y ')' " := ( URResult (geb_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'geb_' '(' x , y ')' " := ( FuncallExpression (geb_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition le_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) le
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
Notation " 'le_' '(' x , y ')' " := ( URResult (le_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'le_' '(' x , y ')' " := ( FuncallExpression (le_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition ge_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) ge
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
Notation " 'ge_' '(' x , y ')' " := ( URResult (ge_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'ge_' '(' x , y ')' " := ( FuncallExpression (ge_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition eqbu_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) eqbu
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
Notation " 'eqbu_' '(' x , y ')' " := ( URResult (eqbu_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'eqbu_' '(' x , y ')' " := ( FuncallExpression (eqbu_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.

Definition neqbu_call {b} (x: URValue XInteger b) (y: URValue XInteger b)  := 
    🏓 ursus_call_with_args (LedgerableWithArgs := λ2) neqbu
    (SimpleLedgerableArg URValue {{ Λ "a" }}  x) (SimpleLedgerableArg URValue {{ Λ "b" }} y).
 
 
Notation " 'neqbu_' '(' x , y ')' " := ( URResult (neqbu_call x y))  
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


Notation " 'neqbu_' '(' x , y ')' " := ( FuncallExpression (neqbu_call x y))  
(in custom ULValue at level 0 , x custom URValue at level 0, y custom URValue at level 0) : ursus_scope.


End stdFuncNotations.