Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.

Require Import Project.CommonConstSig.

Require Import Contracts.SelfDeployer.Ledger.
Require Import FuncSig.

Module trainFuncNotations (xt: XTypesSig) 
                          (sm: StateMonadSig) 
                          (dc : trainConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.


Module Export trainContractSpecModule :=  trainContractSpec xt sm.

Import UrsusNotations.

Local Open Scope ursus_scope.

Notation " 'm_value' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SelfDeployer_ι_m_value ) (in custom ULValue at level 0) : ursus_scope.
Notation " 'm_value' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SelfDeployer_ι_m_value ) (in custom URValue at level 0) : ursus_scope.

Notation " 'm_parent' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SelfDeployer_ι_m_parent ) (in custom ULValue at level 0) : ursus_scope.
Notation " 'm_parent' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SelfDeployer_ι_m_parent ) (in custom URValue at level 0) : ursus_scope.

Notation " 'm_depth' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SelfDeployer_ι_m_depth ) (in custom ULValue at level 0) : ursus_scope.
Notation " 'm_depth' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SelfDeployer_ι_m_depth ) (in custom URValue at level 0) : ursus_scope.

Notation " 'm_chilred' " := ( ULState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SelfDeployer_ι_m_chilred ) (in custom ULValue at level 0) : ursus_scope.
Notation " 'm_chilred' " := ( URState (H0:=LedgerStateLEmbeddedType Ledger_ι_Contract) SelfDeployer_ι_m_chilred ) (in custom URValue at level 0) : ursus_scope.

Notation " 'error_code::const1' " := (sInject const1) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::const2' " := (sInject const2) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::const3' " := (sInject const3) (in custom URValue at level 0) : ursus_scope.

(**************************************************************************************************)

Module FuncEx (tc : trainContractSpecSig).

Export tc.

Local Open Scope string_scope.

Definition constructor_call {b} (x: URValue XInteger b): LedgerT (ControlResult PhantomType true) := 
   🏓 ursus_call_with_args (LedgerableWithArgs := λ1) constructor 
(SimpleLedgerableArg URValue {{ Λ "_depth" }} x) .

Notation " 'constructor_' '(' x ')' " := ( URResult (constructor_call x))  
   (in custom URValue at level 0 , x custom URValue at level 0) : ursus_scope.

Notation " 'constructor_' '(' x ')' " := ( FuncallExpression (constructor_call x))  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.   

Definition deploy_call {b} (x: URValue XInteger b): LedgerT (ControlResult XAddress b) := 
   🏓 ursus_call_with_args (LedgerableWithArgs := λ1) deploy 
(SimpleLedgerableArg URValue {{ Λ "_value" }} x) .

Notation " 'deploy_' '(' x ')' " := ( URResult (deploy_call x))  
   (in custom URValue at level 0 , x custom URValue at level 0) : ursus_scope.

Notation " 'deploy_' '(' x ')' " := ( FuncallExpression (deploy_call x))  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.   




End FuncEx. 

End trainFuncNotations.
