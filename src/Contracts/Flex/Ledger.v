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

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) Inductive MessagesAndEventsFields := | MessagesAndEvents_ι_field_1 | MessagesAndEvents_ι_field_2 | MessagesAndEvents_ι_field_3 | MessagesAndEvents_ι_field_4 .
(* 1 *) Inductive ContractFields := | deployer_pubkey_ 
                                    | tons_cfg_ 
                                    | pair_code_ 
                                    | xchg_pair_code_ 
                                    | price_code_ 
                                    | xchg_price_code_ 
                                    | deals_limit_ 
                                    | notify_addr_ .
(* (* 1 *) Inductive LocalStateFieldsI := 
| _int | _intIndex | _optcell | _optcellIndex | _tpladdressaddress 
| _tpladdressaddressIndex | _uint256 | _uint256Index | _uint128 
| _uint128Index | _uint8 | _uint8Index | _address | _addressIndex 
| _cell | _cellIndex | _XchgPair | _XchgPairIndex | _TradingPair 
| _TradingPairIndex | _tplStateInituint256 | _tplStateInituint256Index | _bool | _boolIndex .
 *)
(* 1 *) Inductive LedgerFieldsI := | _Contract | _ContractCopy | _VMState | _MessagesAndEvents | _MessagesAndEventsCopy | _LocalState | _LocalStateCopy .

 Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 
 Module Import SolidityNotationsForLedger := SolidityNotations xt sm.  
 Module Export VMStateModule := VMStateModule xt sm. 
 Module Export TypesModuleForLedger := ClassTypes xt sm .

(* 2 *) Definition MessagesAndEventsStateL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XBool ) : Type ; 
 ( XCell ) : Type ; 
 ( ( XHMap XInteger XInteger ) ) : Type ] .
GeneratePruvendoRecord MessagesAndEventsStateL MessagesAndEventsFields . 
  Opaque MessagesAndEventsStateLRecord . 

(* 2 *) Definition ContractL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( TonsConfigStateLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XAddress ) : Type ] .
GeneratePruvendoRecord ContractL ContractFields . 
 Opaque ContractLRecord . 
(* GeneratePruvendoRecord TradingPairStateL TradingPairFields . 
 Opaque TradingPairStateLRecord . 
GeneratePruvendoRecord XchgPairStateL XchgPairFields . 
 Opaque XchgPairStateLRecord . *) 


Inductive LocalStateFields0000I := | ι00000 | ι00001 . 
 Definition LocalState0000L := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0000L LocalStateFields0000I  . 
 Opaque LocalState0000LRecord . 
 
 Inductive LocalStateFields0001I := | ι00010 | ι00011 . 
 Definition LocalState0001L := [ ( XHMap (string*nat) ( XMaybe XCell ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0001L LocalStateFields0001I  . 
 Opaque LocalState0001LRecord . 
 
 Inductive LocalStateFields0010I := | ι00100 | ι00101 . 
 Definition LocalState0010L := [ ( XHMap (string*nat) ( XAddress * XAddress ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0010L LocalStateFields0010I  . 
 Opaque LocalState0010LRecord . 
 
 Inductive LocalStateFields0011I := | ι00110 | ι00111 . 
 Definition LocalState0011L := [ ( XHMap (string*nat) XInteger256 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0011L LocalStateFields0011I  . 
 Opaque LocalState0011LRecord . 
 
 Inductive LocalStateFields0100I := | ι01000 | ι01001 . 
 Definition LocalState0100L := [ ( XHMap (string*nat) XInteger128 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0100L LocalStateFields0100I  . 
 Opaque LocalState0100LRecord . 
 
 Inductive LocalStateFields0101I := | ι01010 | ι01011 . 
 Definition LocalState0101L := [ ( XHMap (string*nat) XInteger8 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0101L LocalStateFields0101I  . 
 Opaque LocalState0101LRecord . 
 
 Inductive LocalStateFields0110I := | ι01100 | ι01101 . 
 Definition LocalState0110L := [ ( XHMap (string*nat) XAddress ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0110L  LocalStateFields0110I  . 
 Opaque LocalState0110LRecord . 
 
 Inductive LocalStateFields0111I := | ι01110 | ι01111 . 
 Definition LocalState0111L := [ ( XHMap (string*nat) XCell ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0111L LocalStateFields0111I  . 
 Opaque LocalState0111LRecord . 
 
 Inductive LocalStateFields1000I := | ι10000 | ι10001 . 
 Definition LocalState1000L := [ ( XHMap (string*nat) XchgPairStateLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState1000L LocalStateFields1000I  . 
 Opaque LocalState1000LRecord . 
 
 Inductive LocalStateFields1001I := | ι10010 | ι10011 . 
 Definition LocalState1001L := [ ( XHMap (string*nat) TradingPairStateLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState1001L LocalStateFields1001I  . 
 Opaque LocalState1001LRecord . 
 
 Inductive LocalStateFields1010I := | ι10100 | ι10101 . 
 Definition LocalState1010L := [ ( XHMap (string*nat) XBool ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState1010L LocalStateFields1010I  . 
 Opaque LocalState1010LRecord . 
 


 Inductive LocalStateFields000I := | ι0000 | ι0001 . 
 Definition LocalState000L := [ LocalState0000LRecord ; LocalState0001LRecord ] . 
 GeneratePruvendoRecord LocalState000L LocalStateFields000I  . 
 Opaque LocalState000LRecord . 
 
 Inductive LocalStateFields001I := | ι0010 | ι0011 . 
 Definition LocalState001L := [ LocalState0010LRecord ; LocalState0011LRecord ] . 
 GeneratePruvendoRecord LocalState001L LocalStateFields001I  . 
 Opaque LocalState001LRecord . 
 
 Inductive LocalStateFields010I := | ι0100 | ι0101 . 
 Definition LocalState010L := [ LocalState0100LRecord ; LocalState0101LRecord ] . 
 GeneratePruvendoRecord LocalState010L LocalStateFields010I  . 
 Opaque LocalState010LRecord . 
 
 Inductive LocalStateFields011I := | ι0110 | ι0111 . 
 Definition LocalState011L := [ LocalState0110LRecord ; LocalState0111LRecord ] . 
 GeneratePruvendoRecord LocalState011L LocalStateFields011I  . 
 Opaque LocalState011LRecord . 
 
 Inductive LocalStateFields100I := | ι1000 | ι1001 . 
 Definition LocalState100L := [ LocalState1000LRecord ; LocalState1001LRecord ] . 
 GeneratePruvendoRecord LocalState100L LocalStateFields100I  . 
 Opaque LocalState100LRecord . 
 
 

 Inductive LocalStateFields00I := | ι000 | ι001 . 
 Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
 GeneratePruvendoRecord LocalState00L LocalStateFields00I  . 
 Opaque LocalState00LRecord . 
 
 Inductive LocalStateFields01I := | ι010 | ι011 . 
 Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
 GeneratePruvendoRecord LocalState01L LocalStateFields01I  . 
 Opaque LocalState01LRecord . 
 
     Inductive LocalStateFields10I := | ι100 | ι101 . 
     Definition LocalState10L := [ LocalState1010LRecord ; LocalState100LRecord ] . 
     GeneratePruvendoRecord LocalState10L LocalStateFields10I  . 
     Opaque LocalState10LRecord . 



 Inductive LocalStateFields0I := | ι00 | ι01 .
 Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
 GeneratePruvendoRecord LocalState0L LocalStateFields0I  . 
 Opaque LocalState0LRecord . 
  
     Inductive LocalStateFieldsI := | ι0 | ι1 . 
     Definition LocalStateL := [ LocalState10LRecord ; LocalState0LRecord ] . 
     GeneratePruvendoRecord LocalStateL LocalStateFieldsI  . 
     Opaque LocalStateLRecord . 
 
Transparent LocalState0000LRecord LocalState0001LRecord LocalState0010LRecord
            LocalState0011LRecord LocalState0100LRecord LocalState0101LRecord.

Transparent LocalState0110LRecord LocalState0111LRecord LocalState1000LRecord
            LocalState1001LRecord LocalState1010LRecord .

Transparent LocalState000LRecord LocalState001LRecord LocalState010LRecord
            LocalState011LRecord LocalState100LRecord .

Transparent LocalState00LRecord LocalState01LRecord LocalState10LRecord .

Transparent LocalState0LRecord LocalStateLRecord .

(* 
(* 2 *) Definition LocalStateL : list Type := 
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
 ( XHMap string nat ) : Type ;  ( XHMap (string*nat) XBool ) : Type ; 
 ( XHMap string nat ) : Type ] .
Opaque XchgPairStateLRecord TradingPairStateLRecord StateInitStateLRecord .
GeneratePruvendoRecord LocalStateL LocalStateFieldsI . *)
 Opaque LocalStateLRecord . 

Check VMStateLRecord.

(* 2 *) Definition LedgerL : list Type := 
 [ ( ContractLRecord ) : Type ; 
 ( ContractLRecord ) : Type ; 
 ( VMStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( LocalStateLRecord ) : Type ; 
 ( LocalStateLRecord ) : Type ] .
GeneratePruvendoRecord LedgerL LedgerFieldsI .
(***************************************)
Transparent MessagesAndEventsStateLRecord .
Transparent ContractLRecord .
Transparent LocalStateLRecord .
Transparent LedgerLRecord .

Definition LedgerPruvendoRecord := LedgerLPruvendoRecord .
Definition LedgerLocalState := LocalStateLRecord .
Definition LedgerLocalFields := LocalStateFieldsI.
Definition LedgerLocalPruvendoRecord := LocalStateLPruvendoRecord .
Definition LocalEmbedded := LedgerLEmbeddedType _LocalState .
Definition LocalCopyEmbedded := LedgerLEmbeddedType _LocalStateCopy.
(* Definition LocalDefault : XDefault LocalStateLRecord := prod_default. *)
Definition Ledger_LocalState := _LocalState.
Definition Ledger_LocalStateCopy := _LocalStateCopy.
Definition iso_local : LedgerLocalState = field_type Ledger_LocalState := eq_refl.
Definition Ledger := LedgerLRecord.
Definition LedgerFields := LedgerFieldsI.

(* Definition MessagesAndEvents := _MessagesAndEvents. *)


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


Class LocalStateField  (X:Type): Type := 
{
    local_index_embedded:> EmbeddedType LedgerLocalState (XHMap string nat) ;
    local_embedded:> EmbeddedType LedgerLocalState (XHMap (string*nat)%type X) ;
    (* local_state_field: LedgerLocalFields; *)
    (* local_field_type_correct: field_type (PruvendoRecord:=LedgerLocalPruvendoRecord) local_state_field = XHMap (string*nat)%type X; *)
}. 

Definition LedgerVMStateEmbedded := LedgerLEmbeddedType _VMState . 
Definition LedgerVMStateField := _VMState .
Definition isoVMState: VMStateLRecord =
 field_type LedgerVMStateField := eq_refl.

Definition LedgerMessagesEmbedded := LedgerLEmbeddedType _MessagesAndEvents . 
Definition LedgerMessagesField := _MessagesAndEvents .
Definition isoMessages : MessagesAndEventsStateLRecord =
 field_type LedgerMessagesField:= eq_refl.
Definition MessagesAndEvents := MessagesAndEventsStateLRecord .
 
GenerateLocalStateInstances LocalStateL LocalStateFieldsI Build_LocalStateField LocalStateLEmbeddedType.
Check LocalStateLEmbeddedType _int.
(* #[global]
 Declare Instance foo : LocalStateField (StateInitStateLRecord * XInteger256). *)
Locate _intLocalField.
Definition LocalStateField_XInteger := _intLocalField .
Definition LocalStateField_XBool := _boolLocalField .
Definition LocalStateField_XCell := _cellLocalField .

Check ContractLEmbeddedType.

Definition LedgerEmbedded := LedgerLEmbeddedType.
Definition LocalDefault (_: LedgerLocalState): LedgerLocalState  := default.


Lemma LedgerFieldsDec_eqrefl : forall m, LedgerFieldsDec m m = left eq_refl.
Proof.
intros.
destruct m; simpl; reflexivity.
Qed.




(* Definition LedgerVMStateEmbedded := LedgerStateLEmbeddedType _VMState . 
Definition LedgerVMStateField := _VMState .
Definition isoVMState := _VMStateIso.

GenerateLocalStateInstances LocalStateStateL LocalStateFieldsI Build_LocalStateField LocalStateStateLEmbeddedType.

Definition LocalStateField_XInteger := _intLocalField .
Definition LocalStateField_XBool := _boolLocalField .
Definition LocalStateField_XCell := _cellLocalField .




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
Qed . *)
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
Qed . *)

End Ledger .
