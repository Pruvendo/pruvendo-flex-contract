Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 
Require Import Coq.Lists.List.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.StateMonad21. 
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.ProofEnvironment2.
Require Import UMLang.SML_NG25.

Require Import classFlex.

Require Import FLeXContractTypes.

Require Import specFlex.
Require Import FLeXConstSig. 


Module FLeXFuncNotations (xt: XTypesSig) 
                          (sm: StateMonadSig) 
                          (dc : FLeXConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

Module Export specFlexSpec := specFlexSpec xt sm.
Local Open Scope record. 
Local Open Scope solidity_scope. 
Local Open Scope sml_scope. 
Local Open Scope string_scope.
Local Open Scope program_scope. 

(* Unset Typeclasses Iterative Deepening. 
Set Typeclasses Depth 100.  *)
Import ListNotations.
Import SMLNotations.


(* Notation " 'record1.A' " := ( SMLLState (U:=Record1) record1_ι_A ) (in custom SMLLValue at level 0) : sml_scope.
Notation " 'record1.A' " := ( SMLRState (U:=Record1) record1_ι_A ) (in custom SMLRValue at level 0) : sml_scope.

Notation " 'local.IntIndex' " := ( SMLLState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_IntIndex) (in custom SMLLValue at level 0) : sml_scope.
Notation " 'local.IntIndex' " := ( SMLRState (H1:=embeddedT6) (U:=LocalState) LocalState_ι_IntIndex) (in custom SMLRValue at level 0) : sml_scope.
 
Notation " 'error_code::const1' " := (sInject const1) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::const2' " := (sInject const2) (in custom SMLRValue at level 0) : sml_scope. 
Notation " 'error_code::const3' " := (sInject const3) (in custom SMLRValue at level 0) : sml_scope.
 *)
(**************************************************************************************************)

Module FuncEx (tc : specFLeXSig).
Import SMLNotations.
Local Open Scope sml_scope.
Import tc.
Require Import String.
Local Open Scope string_scope.

Definition bar33_call (x y: SMLRValue XBool false)  := 
   🏓 sml_call_with_args (LedgerableWithArgs := λ2) bar33 
(SimpleLedgerableArg SMLRValue {{ Λ "b0" }} x) (SimpleLedgerableArg SMLRValue {{ Λ "b1" }} y) .


Notation " 'bar33_' '(' x , y ')' " := ( SMLRResult (bar33_call x y))  
   (in custom SMLRValue at level 0 , x custom SMLRValue at level 0, y custom SMLRValue at level 0) : sml_scope.

Notation " 'bar33_' '(' x , y ')' " := ( FuncallExpression (bar33_call x y))  
   (in custom SMLLValue at level 0 , x custom SMLRValue at level 0, y custom SMLRValue at level 0) : sml_scope.
 (*Здесь будут сгенерена последовательность параметров внутри модуля тайпа. Появится новый модуль который будет параметризован 
этим модулетайпом (можно и в этом же файле). Появится абстрактный инстанс этого модулетайпа импорт икс и вот эти все параметры поя
вятся в контексте. Тогда для них мы сможем написать определения . Тогда подключив новый модуль можно писать 
какую-то формулировку. Тогда в новом модуле Роберт сможет сформулировать спецификацию функций, считая то они есть
А потом мы сделаем модуль с самими функциями. *)
 
End FuncEx. 
End FLeXFuncNotations.
