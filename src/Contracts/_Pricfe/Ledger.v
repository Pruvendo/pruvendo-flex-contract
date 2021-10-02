 Require Import Coq.Program.Basics. 

Require Import String. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 

Require Import FinProof.ProgrammingWith.  
Require Import UMLang.UrsusLib. 
Require Import UMLang.SolidityNotations2. 
Require Import UMLang.ClassGenerator.ClassGenerator.
Require Import UrsusTVM.tvmFunc. 

Require Import Project.CommonTypes.

Require Import Contracts.Price.ClassTypes.
Require Import Contracts.Price.Interface.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope xlist_scope.


(* 1 *) Inductive MessagesAndEventsFields := | MessagesAndEvents_ι_field_1 | MessagesAndEvents_ι_field_2 | MessagesAndEvents_ι_field_3 | MessagesAndEvents_ι_field_4 .
(* 1 *) Inductive PriceFields := | Price_ι_price_ | Price_ι_sells_amount_ | Price_ι_buys_amount_ | Price_ι_flex_ | Price_ι_min_amount_ | Price_ι_deals_limit_ | Price_ι_notify_addr_ | Price_ι_workchain_id_ | Price_ι_tons_cfg_ | Price_ι_tip3_code_ | Price_ι_tip3cfg_ .
(* 1 *) Inductive LocalStateFieldsI := | LocalState_ι_uint | LocalState_ι_uintIndex | LocalState_ι_XCell | LocalState_ι_XCellIndex | LocalState_ι_address | LocalState_ι_addressIndex | LocalState_ι_int | LocalState_ι_intIndex | LocalState_ι_bool | LocalState_ι_boolIndex | LocalState_ι_cell | LocalState_ι_cellIndex .
(* 1 *) Inductive LedgerFieldsI := | Ledger_ι_Contract | Ledger_ι_ContractCopy | Ledger_ι_VMState | Ledger_ι_MessagesAndEvents | Ledger_ι_MessagesAndEventsCopy | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .

 Module PriceClass (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 
 Module Export SolidityNotationsClass := SolidityNotations xt sm. 
 Module Export VMStateModule := VMStateModule xt sm. 
 Module Export ClassTypesModule := ClassTypes xt sm .
Import xt.
Opaque Tip3ConfigStateLRecord .
(* 2 *) Definition MessagesAndEventsStateL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XBool ) : Type ; 
 ( XCell ) : Type ; 
 ( ( XHMap XInteger XInteger ) ) : Type ] .
GeneratePruvendoRecord MessagesAndEventsStateL MessagesAndEventsFields . 
  Opaque MessagesAndEventsStateLRecord . 

(* 2 *) Definition PriceStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TonsConfigStateLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigStateLRecord ) : Type ] .
GeneratePruvendoRecord PriceStateL PriceFields . 
 Opaque PriceStateLRecord .

(* 2 *) Definition LocalStateStateL : list Type := 
 [ ( XHMap (string*nat) XCell ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) StateInitStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( StateInitStateLRecord * XInteger256 ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XBool ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger32 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) PriceStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XMaybe XInteger128 ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger128 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XBool * XBool * XInteger128 ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) OrderInfoStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XMaybe (XInteger * OrderInfoStateLRecord) * (XHMap XInteger OrderInfoStateLRecord) * XInteger128 ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XMaybe (XInteger * OrderInfoStateLRecord) ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) OrderRetStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) dealerStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) process_retStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger8 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) TonsConfigStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( (XHMap XInteger OrderInfoStateLRecord) * XInteger128 ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) addr_std_fixedStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger256 (* Grams *) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) SellArgsStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XAddress ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) DetailsInfoStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XHMap XInteger OrderInfoStateLRecord ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XMaybe XAddress ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) TONTokenWalletStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XAddress * XInteger256 (* Grams *) ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XSlice ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XMaybe OrderRetStateLRecord ) ) : Type ; 
 ( XHMap string nat ) : Type ] .
Elpi GeneratePruvendoRecord LocalStateStateL LocalStateFieldsI . 
 Opaque LocalStateStateLRecord . 

(* 2 *) Definition LedgerStateL : list Type := 
 [ ( FlexClientStateLRecord ) : Type ; 
 ( FlexClientStateLRecord ) : Type ; 
 ( VMState ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ] .
Elpi GeneratePruvendoRecord LedgerStateL LedgerFieldsI .


Opaque VMStateLRecord.
Opaque MessagesAndEventsStateLRecord.
Opaque LocalStateStateLRecord.
Elpi GeneratePruvendoRecord LedgerStateL LedgerFieldsI .
Transparent TickTockStateLRecord .
Transparent StateInitStateLRecord .
Transparent addr_std_fixedStateLRecord .
Transparent TonsConfigStateLRecord .
Transparent OrderRetStateLRecord .
Transparent SellArgsStateLRecord .
Transparent OrderInfoStateLRecord .
Transparent DetailsInfoStateLRecord .
Transparent Tip3ConfigStateLRecord .
Transparent PriceStateLRecord .
Transparent dealerStateLRecord .
Transparent process_retStateLRecord .
Transparent lend_ownership_infoStateLRecord .
Transparent allowance_infoStateLRecord .
Transparent TONTokenWalletStateLRecord .
Transparent OrderInfoXchgStateLRecord .

Transparent VMStateLRecord.
Transparent MessagesAndEventsStateLRecord.
Transparent LocalStateStateLRecord.

(***************************************)

Definition LedgerPruvendoRecord := LedgerStateLPruvendoRecord .
Definition LedgerLocalState := LocalStateStateLRecord .
Definition LedgerLocalFields := LocalStateFieldsI.
Definition LedgerLocalPruvendoRecord := LocalStateStateLPruvendoRecord .
Definition LocalEmbedded := LedgerStateLEmbeddedType Ledger_ι_LocalState .
Definition LocalCopyEmbedded := LedgerStateLEmbeddedType Ledger_ι_LocalStateCopy.
Definition LocalDefault : XDefault LocalStateStateLRecord := prod_default.
Definition Ledger_LocalState := Ledger_ι_LocalState.
Definition Ledger_LocalStateCopy := Ledger_ι_LocalStateCopy.
Definition iso_local := Ledger_ι_LocalStateIso.
Definition Ledger := LedgerStateLRecord.
Definition LedgerFields := LedgerFieldsI.

Lemma LedgerFieldsDec: forall (m1 m2: LedgerFieldsI), {m1=m2}+{m1<>m2}.
Proof.
  intros.
  decide equality.
Defined.

Lemma LocalCopySameType: field_type  Ledger_LocalState = 
field_type Ledger_LocalStateCopy.
Proof.
  reflexivity.
Defined.

Class LocalStateField (X:Type): Type := 
{
    local_index_embedded:> EmbeddedType LocalStateStateLRecord (XHMap string nat) ;
    local_state_field: LedgerLocalFields;
    local_field_type_correct: field_type local_state_field = XHMap (string*nat)%type X;
}.


Definition LedgerVMStateEmbedded := LedgerStateLEmbeddedType Ledger_ι_VMState . 
Definition LedgerVMStateField := Ledger_ι_VMState .
Definition isoVMState := Ledger_ι_VMStateIso.

Definition LedgerMessagesEmbedded := LedgerStateLEmbeddedType Ledger_ι_MessagesAndEvents . 
Definition LedgerMessagesField := Ledger_ι_MessagesAndEvents .
Definition isoMessages := Ledger_ι_MessagesAndEventsIso.
Definition MessagesAndEvents := MessagesAndEventsStateLRecord .

GenerateLocalStateInstances LocalStateStateL LocalStateFieldsI Build_LocalStateField LocalStateStateLEmbeddedType.

Check LocalState_ι_uintLocalField.
Check LocalState_ι_boolLocalField.

Definition LocalStateField_XInteger := LocalState_ι_uintLocalField .
Definition LocalStateField_XBool := LocalState_ι_boolLocalField .
Definition LocalStateField_XCell := LocalState_ι_cellLocalField .


(***************************************)
Lemma MessagesAndEventsFields_noeq : forall (f1 f2:  MessagesAndEventsFields ) 
         (v2: field_type f2) (r :  MessagesAndEventsStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= MessagesAndEventsStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

Lemma PriceFields_noeq : forall (f1 f2:  PriceFields ) 
         (v2: field_type f2) (r :  PriceStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= PriceStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

Lemma LocalStateFields_noeq : forall (f1 f2:  LocalStateFieldsI ) 
         (v2: field_type f2) (r :  LocalStateStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= LocalStateStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

Lemma LedgerFields_noeq : forall (f1 f2:  LedgerFields ) 
         (v2: field_type f2) (r :  LedgerStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= LedgerStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

End PriceClass .
