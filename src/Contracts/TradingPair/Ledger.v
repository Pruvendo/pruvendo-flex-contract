Require Import Coq.Program.Basics. 

Require Import String. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 

Require Import FinProof.ProgrammingWith.  
Require Import UMLang.UrsusLib. 
Require Import UMLang.SolidityNotations2. 
Require Import UrsusTVM.tvmFunc. 

Require Import Project.CommonTypes. 
Require Import Contracts.TradingPair.ClassTypes.
Require Import Contracts.TradingPair.Interface.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) Inductive MessagesAndEventsFields := | _OutgoingMessages_SelfDeployer | _EmittedEvents | _MessagesLog.
(* 1 *) Inductive ContractFields := | flex_addr_ | tip3_root_ | min_amount_ | notify_addr_ .
(* 1 *) Inductive LedgerFieldsI := | _Contract | _ContractCopy | _VMState | _MessagesAndEvents | _MessagesAndEventsCopy | _LocalState | _LocalStateCopy .

Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 

Module TradingPairPublicInterfaceModule := PublicInterface xt sm.

Module Import SolidityNotationsClass := SolidityNotations xt sm.
Module Export VMStateModule := VMStateModule xt sm. 
Module Export TypesModuleForLedger := ClassTypes xt sm .
Import xt. 


(* 2 *) Definition MessagesAndEventsL : list Type := 
 [ ( XQueue TradingPairPublicInterfaceModule.OutgoingMessage ) : Type ; 
 ( XList TVMEvent ) : Type ; 
 ( XString ) : Type ] .
GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
  Opaque MessagesAndEventsLRecord .
 
(* 2 *) Definition ContractL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord ContractL ContractFields . 
 Opaque ContractLRecord . 


Inductive LocalStateFields0000I := | ι00000 | ι00001 . 
 Definition LocalState0000L := [ ( XHMap (string*nat) ( StateInitLRecord * XInteger256 ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0000L LocalStateFields0000I . 
 Opaque LocalState0000LRecord . 
 
 Inductive LocalStateFields0001I := | ι00010 | ι00011 . 
 Definition LocalState0001L := [ ( XHMap (string*nat) XCell ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0001L LocalStateFields0001I . 
 Opaque LocalState0001LRecord . 
 
 Inductive LocalStateFields0010I := | ι00100 | ι00101 . 
 Definition LocalState0010L := [ ( XHMap (string*nat) StateInitLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0010L LocalStateFields0010I . 
 Opaque LocalState0010LRecord . 
 
 Inductive LocalStateFields0011I := | ι00110 | ι00111 . 
 Definition LocalState0011L := [ ( XHMap (string*nat) XBool ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0011L LocalStateFields0011I . 
 Opaque LocalState0011LRecord . 
 
 Inductive LocalStateFields0100I := | ι01000 | ι01001 . 
 Definition LocalState0100L := [ ( XHMap (string*nat) XAddress ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0100L LocalStateFields0100I . 
 Opaque LocalState0100LRecord . 
 
 Inductive LocalStateFields0101I := | ι01010 | ι01011 . 
 Definition LocalState0101L := [ ( XHMap (string*nat) XInteger128 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0101L LocalStateFields0101I . 
 Opaque LocalState0101LRecord . 
 
 Inductive LocalStateFields0110I := | ι01100 | ι01101 . 
 Definition LocalState0110L := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0110L LocalStateFields0110I . 
 Opaque LocalState0110LRecord . 
 
 Inductive LocalStateFields0111I := | ι01110 | ι01111 . 
 Definition LocalState0111L := [ ( XHMap (string*nat) XInteger (* type1LRecord *) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState0111L LocalStateFields0111I . 
 Opaque LocalState0111LRecord . 
 
 Inductive LocalStateFields1000I := | ι10000 | ι10001 . 
 Definition LocalState1000L := [ ( XHMap (string*nat) XInteger (* type2LRecord *) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState1000L LocalStateFields1000I . 
 Opaque LocalState1000LRecord . 
 
 Inductive LocalStateFields1001I := | ι10010 | ι10011 . 
 Definition LocalState1001L := [ ( XHMap (string*nat) XInteger (* type3LRecord *) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState1001L LocalStateFields1001I . 
 Opaque LocalState1001LRecord . 
 
 
 Inductive LocalStateFields000I := | ι0000 | ι0001 . 
 Definition LocalState000L := [ LocalState0000LRecord ; LocalState0001LRecord ] . 
 GeneratePruvendoRecord LocalState000L LocalStateFields000I . 
 Opaque LocalState000LRecord . 
 
 Inductive LocalStateFields001I := | ι0010 | ι0011 . 
 Definition LocalState001L := [ LocalState0010LRecord ; LocalState0011LRecord ] . 
 GeneratePruvendoRecord LocalState001L LocalStateFields001I . 
 Opaque LocalState001LRecord . 
 
 Inductive LocalStateFields010I := | ι0100 | ι0101 . 
 Definition LocalState010L := [ LocalState0100LRecord ; LocalState0101LRecord ] . 
 GeneratePruvendoRecord LocalState010L LocalStateFields010I . 
 Opaque LocalState010LRecord . 
 
 Inductive LocalStateFields011I := | ι0110 | ι0111 . 
 Definition LocalState011L := [ LocalState0110LRecord ; LocalState0111LRecord ] . 
 GeneratePruvendoRecord LocalState011L LocalStateFields011I . 
 Opaque LocalState011LRecord . 
 
 Inductive LocalStateFields100I := | ι1000 | ι1001 . 
 Definition LocalState100L := [ LocalState1000LRecord ; LocalState1001LRecord ] . 
 GeneratePruvendoRecord LocalState100L LocalStateFields100I . 
 Opaque LocalState100LRecord . 
 
 
 
 Inductive LocalStateFields00I := | ι000 | ι001 . 
 Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
 GeneratePruvendoRecord LocalState00L LocalStateFields00I . 
 Opaque LocalState00LRecord . 
 
 Inductive LocalStateFields01I := | ι010 | ι011 . 
 Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
 GeneratePruvendoRecord LocalState01L LocalStateFields01I . 
 Opaque LocalState01LRecord . 
 
 
 
 Inductive LocalStateFields0I := | ι00 | ι01 . 
 Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
 GeneratePruvendoRecord LocalState0L LocalStateFields0I . 
 Opaque LocalState0LRecord . 
 
 
 
 Inductive LocalStateFieldsI := | ι0 | ι1 . 
 Definition LocalStateL := [ LocalState0LRecord ; LocalState100LRecord ] . 
 GeneratePruvendoRecord LocalStateL LocalStateFieldsI . 
 Opaque LocalStateLRecord . 
  
(* 2 *) Definition LedgerL : list Type := 
 [ ( ContractLRecord ) : Type ; 
 ( ContractLRecord ) : Type ; 
 ( VMStateLRecord ) : Type ; 
 ( MessagesAndEventsLRecord ) : Type ; 
 ( MessagesAndEventsLRecord ) : Type ; 
 ( LocalStateLRecord ) : Type ; 
 ( LocalStateLRecord ) : Type ] .
GeneratePruvendoRecord LedgerL LedgerFieldsI .
(***************************************)
Transparent MessagesAndEventsLRecord .
Transparent ContractLRecord .
Transparent LocalStateLRecord .
Transparent LedgerLRecord .


 Transparent LocalState0000LRecord LocalState0001LRecord LocalState0010LRecord LocalState0011LRecord LocalState0100LRecord LocalState0101LRecord LocalState0110LRecord LocalState0111LRecord LocalState1000LRecord LocalState1001LRecord LocalState000LRecord LocalState001LRecord LocalState010LRecord LocalState011LRecord LocalState100LRecord LocalState00LRecord LocalState01LRecord LocalState0LRecord LocalStateLRecord .



(***************************************)
Definition LedgerEmbedded := LedgerLEmbeddedType.
Definition LedgerLocalState := LocalStateLRecord .
Definition LocalDefault : LedgerLocalState -> LedgerLocalState := fun _ => default.
Definition LedgerPruvendoRecord := LedgerLPruvendoRecord . 
Definition LedgerLocalFields := LocalStateFieldsI.
Definition Ledger_LocalState := _LocalState.
Definition Ledger_LocalStateCopy := _LocalStateCopy. 
Definition iso_local : LedgerLocalState = (field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_LocalState)
           := eq_refl.
Definition Ledger := LedgerLRecord.
Definition LedgerFields := LedgerFieldsI.
Definition LocalEmbedded := LedgerLEmbeddedType Ledger_LocalState .
Definition LocalCopyEmbedded := LedgerLEmbeddedType Ledger_LocalStateCopy.

Lemma LedgerFieldsDec: forall (m1 m2: LedgerFieldsI), {m1=m2}+{m1<>m2}.
Proof.
  intros.
  decide equality.
Defined.

Lemma LocalCopySameType: field_type  Ledger_LocalState = field_type Ledger_LocalStateCopy.
Proof.
  reflexivity.
Defined.

Lemma LedgerFieldsDec_eqrefl: forall m, LedgerFieldsDec m m = left eq_refl.
Proof.
intros.
destruct m; reflexivity.
Defined.

Class LocalStateField (X:Type): Type := 
{
    local_index_embedded:> EmbeddedType LedgerLocalState (XHMap string nat) ;
    local_embedded:> EmbeddedType LedgerLocalState (XHMap (string*nat)%type X) ;
    (* local_state_field: LedgerLocalFields; *)
    (* local_field_type_correct: field_type (PruvendoRecord:=LedgerLocalPruvendoRecord) local_state_field = XHMap (string*nat)%type X; *)
}. 
Definition LedgerVMStateEmbedded := LedgerLEmbeddedType _VMState . 
Definition Ledger_VMState := _VMState .
Definition isoVMState : VMStateLRecord = (field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_VMState)
           := eq_refl.

Definition LedgerMessagesEmbedded := LedgerLEmbeddedType _MessagesAndEvents . 
Definition Ledger_MessagesState := _MessagesAndEvents .
Definition Ledger_MessagesStateCopy := _MessagesAndEventsCopy.
Definition MessagesAndEvents := MessagesAndEventsLRecord .
Definition isoMessages : MessagesAndEvents = (field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_MessagesState)
           := eq_refl.

Definition Ledger_MainState := _Contract .
Definition Ledger_MainStateCopy := _ContractCopy.

Definition  VMState_IsCommittedEmbedded := VMStateLEmbeddedType VMState_ι_IsCommitted.
Definition MainCopySameType : field_type  Ledger_MainState = field_type Ledger_MainStateCopy := eq_refl.
Definition MessagesCopySameType : field_type  Ledger_MessagesState = field_type Ledger_MessagesStateCopy := eq_refl.

#[local]
Obligation Tactic := idtac.



#[global, program] Instance LocalStateField0000 : LocalStateField ( StateInitLRecord * XInteger256 ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply (LocalState0000LEmbeddedType ι00001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply (LocalState0000LEmbeddedType ι00000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField0000 : typeclass_instances. 
 #[global, program] Instance LocalStateField0001 : LocalStateField XCell.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply (LocalState0001LEmbeddedType ι00011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply (LocalState0001LEmbeddedType ι00010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField0001 : typeclass_instances. 
 #[global, program] Instance LocalStateField0010 : LocalStateField StateInitLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply (LocalState0010LEmbeddedType ι00101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply (LocalState0010LEmbeddedType ι00100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField0010 : typeclass_instances. 
 #[global, program] Instance LocalStateField0011 : LocalStateField XBool.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply (LocalState0011LEmbeddedType ι00111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply (LocalState0011LEmbeddedType ι00110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField0011 : typeclass_instances. 
 #[global, program] Instance LocalStateField0100 : LocalStateField XAddress.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply (LocalState0100LEmbeddedType ι01001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply (LocalState0100LEmbeddedType ι01000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField0100 : typeclass_instances. 
 #[global, program] Instance LocalStateField0101 : LocalStateField XInteger128.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply (LocalState0101LEmbeddedType ι01011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply (LocalState0101LEmbeddedType ι01010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField0101 : typeclass_instances. 
 #[global, program] Instance LocalStateField0110 : LocalStateField XInteger.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply (LocalState0110LEmbeddedType ι01101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply (LocalState0110LEmbeddedType ι01100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField0110 : typeclass_instances. 
 #[global, program] Instance LocalStateField0111 : LocalStateField XInteger (* type2LRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply (LocalState0111LEmbeddedType ι01111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply (LocalState0111LEmbeddedType ι01110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField0111 : typeclass_instances. 
 #[global, program] Instance LocalStateField1000 : LocalStateField XInteger (* type2LRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply (LocalState1000LEmbeddedType ι10001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply (LocalState1000LEmbeddedType ι10000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField1000 : typeclass_instances. 
 #[global, program] Instance LocalStateField1001 : LocalStateField XInteger (* type3LRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply (LocalState1001LEmbeddedType ι10011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply (LocalState1001LEmbeddedType ι10010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField1001 : typeclass_instances. 

Definition LocalStateField_XInteger := LocalStateField0110 .
Definition LocalStateField_XBool := LocalStateField0011 .
Definition LocalStateField_XCell := LocalStateField0001 .


(***************************************)
Lemma MessagesAndEventsFields_noeq : forall (f1 f2:  MessagesAndEventsFields ) 
         (v2: field_type f2) (r :  MessagesAndEventsLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= MessagesAndEventsLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

Lemma SelfDeployerFields_noeq : forall (f1 f2:  ContractFields ) 
         (v2: field_type f2) (r :  ContractLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= ContractLRecord ));
               cbv;
               first [reflexivity| contradiction]).
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

Lemma LedgerFields_noeq : forall (f1 f2:  LedgerFields ) 
         (v2: field_type f2) (r :  LedgerLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= LedgerLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

End Ledger .




