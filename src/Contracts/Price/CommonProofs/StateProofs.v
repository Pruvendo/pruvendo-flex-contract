Require Import FinProof.ProgrammingWith.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Price.ClassTypes.

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

(* Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
Inductive DetailsInfoFields := | DetailsInfo_ι_price | DetailsInfo_ι_min_amount | DetailsInfo_ι_sell_amount | DetailsInfo_ι_buy_amount .
Inductive dealerFields := | dealer_ι_tip3root_ | dealer_ι_notify_addr_ | dealer_ι_price_ | dealer_ι_deals_limit_ | dealer_ι_tons_cfg_ | dealer_ι_sells_amount_ | dealer_ι_sells_ | dealer_ι_buys_amount_ | dealer_ι_buys_ | dealer_ι_ret_ .
Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
Inductive DPriceFields := | DPrice_ι_price_ | DPrice_ι_sells_amount_ | DPrice_ι_buys_amount_ | DPrice_ι_flex_ | DPrice_ι_min_amount_ | DPrice_ι_deals_limit_ | DPrice_ι_notify_addr_ | DPrice_ι_workchain_id_ | DPrice_ι_tons_cfg_ | DPrice_ι_tip3_code_ | DPrice_ι_tip3cfg_ | DPrice_ι_sells_ | DPrice_ι_buys_ .
Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_sells_ | process_ret_ι_buys_amount | process_ret_ι_buys_ | process_ret_ι_ret_ .
 *)

Lemma SellArgsLRecord_getset_diff : forall (f1 f2: SellArgsFields ) 
         (v2: field_type f2) (r: SellArgsLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r SellArgsLRecord.  
Qed.

Lemma DetailsInfoLRecord_getset_diff : forall (f1 f2: DetailsInfoFields ) 
         (v2: field_type f2) (r: DetailsInfoLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r DetailsInfoLRecord.  
Qed.

Lemma dealerLRecord_getset_diff : forall (f1 f2: dealerFields ) 
         (v2: field_type f2) (r: dealerLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r dealerLRecord.  
Qed.

Lemma OrderInfoLRecord_getset_diff : forall (f1 f2: OrderInfoFields ) 
         (v2: field_type f2) (r: OrderInfoLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r OrderInfoLRecord.  
Qed.

Lemma DPriceLRecord_getset_diff : forall (f1 f2: DPriceFields ) 
         (v2: field_type f2) (r: DPriceLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r DPriceLRecord.  
Qed.

Lemma process_retLRecord_getset_diff : forall (f1 f2: process_retFields ) 
         (v2: field_type f2) (r: process_retLRecord) ,  
        f1 <> f2 -> 
        f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros. 
  proof2 f1 f2 r process_retLRecord.  
Qed.


End ClassTypesProofs.

Require Import Price.Ledger.
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
