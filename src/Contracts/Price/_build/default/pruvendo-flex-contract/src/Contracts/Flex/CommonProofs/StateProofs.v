Require Import FinProof.ProgrammingWith.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Flex.ClassTypes.

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

Lemma ListingConfigLRecord_getset_diff : forall (f1 f2: ListingConfigFields ) 
         (v2: field_type f2) (r: ListingConfigLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r ListingConfigLRecord.  
Qed.

Lemma WrapperListingRequestLRecord_getset_diff : forall (f1 f2: WrapperListingRequestFields ) 
         (v2: field_type f2) (r: WrapperListingRequestLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r WrapperListingRequestLRecord.  
Qed.

Lemma WrapperListingRequestWithPubkeyFLRecord_getset_diff : forall (f1 f2: WrapperListingRequestWithPubkeyFields ) 
         (v2: field_type f2) (r: WrapperListingRequestWithPubkeyLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r WrapperListingRequestWithPubkeyLRecord.  
Qed.

Lemma TradingPairListingRequestLRecord_getset_diff : forall (f1 f2: TradingPairListingRequestFields ) 
         (v2: field_type f2) (r: TradingPairListingRequestLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r TradingPairListingRequestLRecord.  
Qed.

Lemma TradingPairListingRequestWithPubkeyLRecord_getset_diff : forall (f1 f2: TradingPairListingRequestWithPubkeyFields ) 
         (v2: field_type f2) (r: TradingPairListingRequestWithPubkeyLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r TradingPairListingRequestWithPubkeyLRecord.  
Qed.

Lemma XchgPairListingRequestLRecord_getset_diff : forall (f1 f2: XchgPairListingRequestFields ) 
         (v2: field_type f2) (r: XchgPairListingRequestLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r XchgPairListingRequestLRecord.  
Qed.

Lemma XchgPairListingRequestWithPubkeyLRecord_getset_diff : forall (f1 f2: XchgPairListingRequestWithPubkeyFields ) 
         (v2: field_type f2) (r: XchgPairListingRequestWithPubkeyLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r XchgPairListingRequestWithPubkeyLRecord.  
Qed.

Lemma FlexOwnershipInfoLRecord_getset_diff : forall (f1 f2: FlexOwnershipInfoFields ) 
         (v2: field_type f2) (r: FlexOwnershipInfoLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r FlexOwnershipInfoLRecord.  
Qed.

Lemma FlexDetailsLRecord_getset_diff : forall (f1 f2: FlexDetailsFields ) 
         (v2: field_type f2) (r: FlexDetailsLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r FlexDetailsLRecord.  
Qed.

Lemma DFlexLRecord_getset_diff : forall (f1 f2: DFlexFields ) 
         (v2: field_type f2) (r: DFlexLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r DFlexLRecord.  
Qed.


End ClassTypesProofs.

Require Import Flex.Ledger.
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
