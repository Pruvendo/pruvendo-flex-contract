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
(* 1 *) Inductive ContractFields := | deployer_pubkey_ 
                                    | tons_cfg_ 
                                    | pair_code_ 
                                    | xchg_pair_code_ 
                                    | price_code_ 
                                    | xchg_price_code_ 
                                    | deals_limit_ 
                                    | notify_addr_ .
(* 1 *) Inductive LocalStateFieldsI := 
| _int | _intIndex | _optcell | _optcellIndex | _tpladdressaddress 
| _tpladdressaddressIndex | _uint256 | _uint256Index | _uint128 
| _uint128Index | _uint8 | _uint8Index | _address | _addressIndex 
| _cell | _cellIndex | _XchgPair | _XchgPairIndex | _TradingPair 
| _TradingPairIndex | _tplStateInituint256 | _tplStateInituint256Index | _bool | _boolIndex .
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
GeneratePruvendoRecord LocalStateL LocalStateFieldsI .
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

(* #[global]
 Declare Instance foo : LocalStateField (StateInitStateLRecord * XInteger256). *)

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
