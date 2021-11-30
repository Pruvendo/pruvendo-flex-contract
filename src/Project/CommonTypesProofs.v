Require Import FinProof.ProgrammingWith.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import CommonTypes.

(* Require Import Contracts.PriceXchg.ClassTypes.
Require Import Contracts.PriceXchg.Ledger . *)

Module CommonTypesProofs (xt: XTypesSig) (sm: StateMonadSig).
Module Export CommonTypes := Types xt sm.

Local Open Scope struct_scope.

Tactic Notation "proof1" constr(f) constr(r) constr(T) := 
    destruct f; 
    (revert r; apply (countable_prop_proof (T:=T)); cbv; reflexivity).

Tactic Notation "proof2" constr(f1) constr(f2) constr(r) constr(T) := 
  destruct f1; destruct f2; 
  (revert r;  apply (countable_prop_proof (T:= T));
   cbv; first [reflexivity| contradiction]).    

(*****************************************************************************)

Lemma TonsConfigLRecord_getset_diff : forall (f1 f2: TonsConfigFields ) 
         (v2: field_type f2) (r: TonsConfigLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r TonsConfigLRecord.  
Qed.

(*****************************************************************************)

Lemma TickTockLRecord_getset_diff : forall (f1 f2: TickTockFields ) 
         (v2: field_type f2) (r: TickTockLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r TickTockLRecord.  
Qed.

(*****************************************************************************)

(* Lemma addr_std_fixed_getset_diff : forall (f1 f2: addr_std_fixedFields ) 
         (v2: field_type f2) (r: addr_std_fixed) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r addr_std_fixed.  
Qed. *)

(*****************************************************************************)

Lemma Tip3ConfigLRecord_getset_diff : forall (f1 f2: Tip3ConfigFields ) 
         (v2: field_type f2) (r: Tip3ConfigLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r Tip3ConfigLRecord.  
Qed.

(*****************************************************************************)

Lemma StateInitLRecord_getset_diff : forall (f1 f2: StateInitFields ) 
         (v2: field_type f2) (r: StateInitLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r StateInitLRecord.  
Qed.

(*****************************************************************************)

Lemma OrderRetLRecord_getset_diff : forall (f1 f2: OrderRetFields ) 
         (v2: field_type f2) (r: OrderRetLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r OrderRetLRecord.  
Qed.


End CommonTypesProofs .