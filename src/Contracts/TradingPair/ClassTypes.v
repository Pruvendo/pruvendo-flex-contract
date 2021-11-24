Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdFunc.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdFuncNotations.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import FinProof.ProgrammingWith.  
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.

Inductive DTradingPairFields := | DTradingPair_ι_flex_addr_ | DTradingPair_ι_tip3_root_ | DTradingPair_ι_deploy_value_ | DTradingPair_ι_min_amount_ | DTradingPair_ι_notify_addr_.

Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Import CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Definition DTradingPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ;
 ( XUInteger128 ) : Type ;
 ( XAddress ) : Type ] .

Elpi GeneratePruvendoRecord DTradingPairL DTradingPairFields . 

Lemma DTradingPairFields_noeq : forall (f1 f2:  DTradingPairFields ) 
         (v2: field_type f2) (r :  DTradingPairLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  destruct f1; destruct f2;
  (revert r;     
               apply (countable_prop_proof (T:= DTradingPairLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .
 
End ClassTypes .
 