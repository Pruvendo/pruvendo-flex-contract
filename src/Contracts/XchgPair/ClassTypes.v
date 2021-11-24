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

(* Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library . *)
Inductive DXchgPairFields := | DXchgPair_ι_flex_addr_ | DXchgPair_ι_tip3_major_root_ | DXchgPair_ι_tip3_minor_root_ | DXchgPair_ι_min_amount_ | DXchgPair_ι_notify_addr_ .


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.


(* Definition StateInitL : list Type := 
 [ ( ( XMaybe XUInteger ) ) : Type ; 
 ( ( XMaybe TickTockLRecord ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
 *)
Definition DXchgPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord DXchgPairL DXchgPairFields . 
 
Lemma DXchgPairFields_noeq : forall (f1 f2:  DXchgPairFields ) 
         (v2: field_type f2) (r :  DXchgPairLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  destruct f1; destruct f2;
  (revert r;     
               apply (countable_prop_proof (T:= DXchgPairLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

End ClassTypes .
