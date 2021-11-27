Require Import FinProof.ProgrammingWith.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import PriceXchg.ClassTypes.

Local Open Scope struct_scope.

Tactic Notation "proof1" constr(f) constr(r) constr(T) := 
    destruct f; 
    (revert r; apply (countable_prop_proof (T:=T)); cbv; reflexivity).

Tactic Notation "proof2" constr(f1) constr(f2) constr(r) constr(T) := 
  destruct f1; destruct f2; 
  (revert r;  apply (countable_prop_proof (T:= T));
   cbv; first [reflexivity| contradiction]). 

Module ClassTypesProofs (xt: XTypesSig) (sm: StateMonadSig).
Module Export ClassTypes := ClassTypes xt sm.

Lemma RationalPriceLRecord_getset_diff : forall (f1 f2: RationalPriceFields ) 
         (v2: field_type f2) (r:RationalPriceLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r RationalPriceLRecord.  
Qed.

Lemma DetailsInfoXchgLRecord_getset_diff : forall (f1 f2: DetailsInfoXchgFields ) 
         (v2: field_type f2) (r:DetailsInfoXchgLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r DetailsInfoXchgLRecord.  
Qed.

Lemma dealerLRecord_getset_diff : forall (f1 f2: dealerFields ) 
         (v2: field_type f2) (r:dealerLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r dealerLRecord.  
Qed.

Lemma OrderInfoXchgLRecord_getset_diff : forall (f1 f2: OrderInfoXchgFields ) 
         (v2: field_type f2) (r:OrderInfoXchgLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r OrderInfoXchgLRecord.  
Qed.

Lemma DPriceXchgLRecord_getset_diff : forall (f1 f2: DPriceXchgFields ) 
         (v2: field_type f2) (r:DPriceXchgLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r DPriceXchgLRecord.  
Qed.

Lemma process_retLRecord_getset_diff : forall (f1 f2: process_retFields ) 
         (v2: field_type f2) (r:process_retLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r process_retLRecord.  
Qed.

Lemma PayloadArgsLRecord_getset_diff : forall (f1 f2: PayloadArgsFields ) 
         (v2: field_type f2) (r: PayloadArgsLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r PayloadArgsLRecord.  
Qed.

End ClassTypesProofs.

Require Import PriceXchg.Ledger.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Tactic Notation "proof1" constr(f) constr(r) constr(T) := 
    destruct f; 
    (revert r; apply (countable_prop_proof (T:=T)); cbv; reflexivity).

Tactic Notation "proof2" constr(f1) constr(f2) constr(r) constr(T) := 
  destruct f1; destruct f2; 
  (revert r;  apply (countable_prop_proof (T:= T));
   cbv; first [reflexivity| contradiction]). 


Module StateProofs (xt: XTypesSig) (sm: StateMonadSig).
Module Export Ledger := Ledger xt sm.

Lemma MessagesAndEventsFields_diff : forall (f1 f2:  MessagesAndEventsFields ) 
         (v2: field_type f2) (r :  MessagesAndEventsLRecord  ) ,  
            f1 <> f2 -> 
            f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  proof2 f1 f2 r MessagesAndEventsLRecord.
Qed .

Lemma LedgerFields_diff : forall (f1 f2:  LedgerFields ) 
         (v2: field_type f2) (r :  LedgerLRecord  ) ,  
            f1 <> f2 -> 
            f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  proof2 f1 f2 r LedgerLRecord.
Qed .

(* Lemma LocalFields_noeq : forall (f1 f2:  LocalFieldsI ) 
         (v2: field_type f2) (r :  LocalStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= LocalStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed . *)

End StateProofs.
