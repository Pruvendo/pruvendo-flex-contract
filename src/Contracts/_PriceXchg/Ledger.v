 Require Import Coq.Program.Basics. 

Require Import String. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 

Require Import FinProof.ProgrammingWith.  
Require Import UMLang.SML_NG28. 
Require Import UMLang.SolidityNotations2. 
Require Import UMLang.ClassGenerator.ClassGenerator.
Require Import UrsusTVM.tvmFunc. 

Require Import Project.CommonTypes. 
Require Import Contracts.PriceXchg.ClassTypes.
Require Import Contracts.PriceXchg.Interface.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope xlist_scope.


(* 1 *) Inductive MessagesAndEventsFields := | MessagesAndEvents_ι_field_1 | MessagesAndEvents_ι_field_2 | MessagesAndEvents_ι_field_3 | MessagesAndEvents_ι_field_4 .
(* 1 *) Inductive PriceXchgFields := | PriceXchg_ι_price_ | PriceXchg_ι_sells_amount_ | PriceXchg_ι_buys_amount_ | PriceXchg_ι_flex_ | PriceXchg_ι_min_amount_ | PriceXchg_ι_deals_limit_ | PriceXchg_ι_notify_addr_ | PriceXchg_ι_workchain_id_ | PriceXchg_ι_tons_cfg_ | PriceXchg_ι_tip3_code_ | PriceXchg_ι_major_tip3cfg_ | PriceXchg_ι_minor_tip3cfg_ .
(* 1 *) Inductive LocalStateFieldsI := | LocalState_ι_uint | LocalState_ι_uintIndex | LocalState_ι_XCell | LocalState_ι_XCellIndex | LocalState_ι_address | LocalState_ι_addressIndex | LocalState_ι_int | LocalState_ι_intIndex | LocalState_ι_bool | LocalState_ι_boolIndex | LocalState_ι_cell | LocalState_ι_cellIndex .
(* 1 *) Inductive LedgerFieldsI := | Ledger_ι_Contract | Ledger_ι_ContractCopy | Ledger_ι_VMState | Ledger_ι_MessagesAndEvents | Ledger_ι_MessagesAndEventsCopy | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .

Module PriceXchgClass (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 

Module Export SolidityNotationsClass := SolidityNotations xt sm. 
Module Export VMStateModule := VMStateModule xt sm. 

Import xt. 

Elpi GeneratePruvendoRecord TickTockStateL TickTockFields . 
 Opaque TickTockStateLRecord . 
Elpi GeneratePruvendoRecord StateInitStateL StateInitFields . 
 Opaque StateInitStateLRecord . 
Elpi GeneratePruvendoRecord addr_std_fixedStateL addr_std_fixedFields . 
 Opaque addr_std_fixedStateLRecord . 
Elpi GeneratePruvendoRecord OrderInfoStateL OrderInfoFields . 
 Opaque OrderInfoStateLRecord . 
Elpi GeneratePruvendoRecord TonsConfigStateL TonsConfigFields . 
 Opaque TonsConfigStateLRecord . 
Elpi GeneratePruvendoRecord RationalPriceStateL RationalPriceFields . 
 Opaque RationalPriceStateLRecord . 
Elpi GeneratePruvendoRecord Tip3ConfigStateL Tip3ConfigFields . 
 Opaque Tip3ConfigStateLRecord . 
Elpi GeneratePruvendoRecord PayloadArgsStateL PayloadArgsFields . 
 Opaque PayloadArgsStateLRecord . 
Elpi GeneratePruvendoRecord OrderInfoXchgStateL OrderInfoXchgFields . 
 Opaque OrderInfoXchgStateLRecord . 
Elpi GeneratePruvendoRecord DetailsInfoXchgStateL DetailsInfoXchgFields . 
 Opaque DetailsInfoXchgStateLRecord . 
Elpi GeneratePruvendoRecord OrderRetStateL OrderRetFields . 
 Opaque OrderRetStateLRecord . 
Elpi GeneratePruvendoRecord dealerStateL dealerFields . 
 Opaque dealerStateLRecord . 
Elpi GeneratePruvendoRecord process_retStateL process_retFields . 
 Opaque process_retStateLRecord . 
Elpi GeneratePruvendoRecord allowance_infoStateL allowance_infoFields . 
 Opaque allowance_infoStateLRecord . 
Elpi GeneratePruvendoRecord TONTokenWalletStateL TONTokenWalletFields . 
 Opaque TONTokenWalletStateLRecord . 


(* 2 *) Definition MessagesAndEventsStateL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XBool ) : Type ; 
 ( XCell ) : Type ; 
 ( ( XHMap XInteger XInteger ) ) : Type ] .

GeneratePruvendoRecord MessagesAndEventsStateL MessagesAndEventsFields .

(* 2 *) Definition PriceXchgStateL : list Type := 
 [ ( RationalPriceStateLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TonsConfigStateLRecord ) : Type ; 
 ( TvmCell ) : Type ; 
 ( Tip3ConfigStateLRecord ) : Type ; 
 ( Tip3ConfigStateLRecord ) : Type ] .
Elpi GeneratePruvendoRecord PriceXchgStateL PriceXchgFields . 
 Opaque PriceXchgStateLRecord . 
 
(* 2 *) Definition LocalStateStateL : list Type := 
 [ ( XHMap (string*nat) XInteger ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XCell ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XAddress ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XBool ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XCell ) : Type ; 
 ( XHMap string nat ) : Type ] .
Elpi GeneratePruvendoRecord LocalStateStateL LocalStateFieldsI .

(* 2 *) Definition LedgerStateL : list Type := 
 [ ( PriceXchgStateLRecord ) : Type ; 
 ( SPriceXchgStateLRecord ) : Type ; 
 ( VMStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ] .

Opaque VMStateLRecord.
Opaque MessagesAndEventsStateLRecord.
Opaque LocalStateStateLRecord.
Elpi GeneratePruvendoRecord LedgerStateL LedgerFieldsI .
Transparent TickTockStateLRecord .
Transparent StateInitStateLRecord .
Transparent addr_std_fixedStateLRecord .
Transparent OrderInfoStateLRecord .
Transparent TonsConfigStateLRecord .
Transparent RationalPriceStateLRecord .
Transparent Tip3ConfigStateLRecord .
Transparent PayloadArgsStateLRecord .
Transparent OrderInfoXchgStateLRecord .
Transparent DetailsInfoXchgStateLRecord .
Transparent PriceXchgStateLRecord .
Transparent OrderRetStateLRecord .
Transparent dealerStateLRecord .
Transparent process_retStateLRecord .
Transparent allowance_infoStateLRecord .
Transparent TONTokenWalletStateLRecord .
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

Lemma PriceXchgFields_noeq : forall (f1 f2:  PriceXchgFields ) 
         (v2: field_type f2) (r :  PriceXchgStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= PriceXchgStateLRecord ));
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

End PriceXchgClass .
