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

Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Interface.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope xlist_scope.

(* 1 *) Inductive MessagesAndEventsFields := | MessagesAndEvents_ι_field_1 | MessagesAndEvents_ι_field_2 | MessagesAndEvents_ι_field_3 | MessagesAndEvents_ι_field_4 .
(* 1 *) Inductive FlexFields := | Flex_ι_deployer_pubkey_ | Flex_ι_tons_cfg_ | Flex_ι_pair_code_ | Flex_ι_xchg_pair_code_ | Flex_ι_price_code_ | Flex_ι_xchg_price_code_ | Flex_ι_deals_limit_ | Flex_ι_notify_addr_ .
(* 1 *) Inductive LocalStateFieldsI := | LocalState_ι_int | LocalState_ι_intIndex | LocalState_ι_optcell | LocalState_ι_optcellIndex | LocalState_ι_tpladdressaddress | LocalState_ι_tpladdressaddressIndex | LocalState_ι_uint256 | LocalState_ι_uint256Index | LocalState_ι_uint128 | LocalState_ι_uint128Index | LocalState_ι_uint8 | LocalState_ι_uint8Index | LocalState_ι_address | LocalState_ι_addressIndex | LocalState_ι_cell | LocalState_ι_cellIndex | LocalState_ι_XchgPair | LocalState_ι_XchgPairIndex | LocalState_ι_TradingPair | LocalState_ι_TradingPairIndex | LocalState_ι_tplStateInituint256 | LocalState_ι_tplStateInituint256Index | LocalState_ι_bool | LocalState_ι_boolIndex .
(* 1 *) Inductive LedgerFieldsI := | Ledger_ι_Contract | Ledger_ι_ContractCopy | Ledger_ι_VMState | Ledger_ι_MessagesAndEvents | Ledger_ι_MessagesAndEventsCopy | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .

 Module FlexClass (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 
 Module Export SolidityNotationsClass := SolidityNotations xt sm. 
 Module Export VMStateModule := VMStateModule xt sm. 
 Module Export ClassTypesModule := ClassTypes xt sm .
Import xt. 

(* 2 *) Definition MessagesAndEventsStateL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XBool ) : Type ; 
 ( XCell ) : Type ; 
 ( ( XHMap XInteger XInteger ) ) : Type ] .
GeneratePruvendoRecord MessagesAndEventsStateL MessagesAndEventsFields . 
  Opaque MessagesAndEventsStateLRecord . 

(* 2 *) Definition FlexStateL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( TonsConfigStateLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord FlexStateL FlexFields . 
 Opaque FlexStateLRecord . 
GeneratePruvendoRecord TradingPairStateL TradingPairFields . 
 Opaque TradingPairStateLRecord . 
GeneratePruvendoRecord XchgPairStateL XchgPairFields . 
 Opaque XchgPairStateLRecord . 

(* 2 *) Definition LocalStateStateL : list Type := 
 [ ( XHMap (string*nat) XInteger ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XMaybe XCell ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XAddress * XAddress ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger256 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger128 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger8 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XAddress ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XCell ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XchgPairStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) TradingPairStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( StateInitStateLRecord * XInteger256 ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XBool ) : Type ; 
 ( XHMap string nat ) : Type ] .
GeneratePruvendoRecord LocalStateStateL LocalStateFieldsI . 
 Opaque LocalStateStateLRecord .

Check VMStateLRecord.

(* 2 *) Definition LedgerStateL : list Type := 
 [ ( FlexStateLRecord ) : Type ; 
 ( FlexStateLRecord ) : Type ; 
 ( VMStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ] .
GeneratePruvendoRecord LedgerStateL LedgerFieldsI .
(***************************************)
Transparent MessagesAndEventsStateLRecord .
Transparent TickTockStateLRecord .
Transparent StateInitStateLRecord .
Transparent TonsConfigStateLRecord .
Transparent FlexStateLRecord .
Transparent TradingPairStateLRecord .
Transparent XchgPairStateLRecord .
Transparent LocalStateStateLRecord .
Transparent LedgerStateLRecord .

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

(* Definition MessagesAndEvents := Ledger_ι_MessagesAndEvents. *)


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

Definition LocalStateField_XInteger := LocalState_ι_intLocalField .
Definition LocalStateField_XBool := LocalState_ι_boolLocalField .
Definition LocalStateField_XCell := LocalState_ι_cellLocalField .

(* Definition LedgerVMStateEmbedded := LedgerStateLEmbeddedType Ledger_ι_VMState . 
Definition LedgerVMStateField := Ledger_ι_VMState .
Definition isoVMState := Ledger_ι_VMStateIso.

GenerateLocalStateInstances LocalStateStateL LocalStateFieldsI Build_LocalStateField LocalStateStateLEmbeddedType.

Definition LocalStateField_XInteger := LocalState_ι_intLocalField .
Definition LocalStateField_XBool := LocalState_ι_boolLocalField .
Definition LocalStateField_XCell := LocalState_ι_cellLocalField .
 *)



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
Lemma TickTockFields_noeq : forall (f1 f2:  TickTockFields ) 
         (v2: field_type f2) (r :  TickTockStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= TickTockStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .
Lemma StateInitFields_noeq : forall (f1 f2:  StateInitFields ) 
         (v2: field_type f2) (r :  StateInitStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= StateInitStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .
Lemma TonsConfigFields_noeq : forall (f1 f2:  TonsConfigFields ) 
         (v2: field_type f2) (r :  TonsConfigStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= TonsConfigStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .
Lemma FlexFields_noeq : forall (f1 f2:  FlexFields ) 
         (v2: field_type f2) (r :  FlexStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= FlexStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .
Lemma TradingPairFields_noeq : forall (f1 f2:  TradingPairFields ) 
         (v2: field_type f2) (r :  TradingPairStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= TradingPairStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .
Lemma XchgPairFields_noeq : forall (f1 f2:  XchgPairFields ) 
         (v2: field_type f2) (r :  XchgPairStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= XchgPairStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .
(* Lemma LocalStateFields_noeq : forall (f1 f2:  LocalStateFieldsI ) 
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
Qed . *)
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

End FlexClass .
