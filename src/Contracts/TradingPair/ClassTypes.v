Require Import FinProof.ProgrammingWith. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.

Inductive DTradingPairFields := | DTradingPair_ι_flex_addr_ | DTradingPair_ι_tip3_root_ | DTradingPair_ι_deploy_value_ | DTradingPair_ι_min_amount_ | DTradingPair_ι_notify_addr_.

Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Opaque addr_stdLRecord address.
Definition DTradingPairL : list Type := 
 [ ( address ) : Type ; 
 ( address ) : Type ; 
 ( XUInteger128 ) : Type ;
 ( XUInteger128 ) : Type ;
 ( address ) : Type ] .

Elpi GeneratePruvendoRecord DTradingPairL DTradingPairFields . 

End ClassTypes .
 