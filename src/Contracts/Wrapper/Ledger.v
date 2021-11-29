Require Import Coq.Program.Basics. 
Require Import String. 

Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 
Require Import FinProof.ProgrammingWith.  

Require Import UMLang.UrsusLib. 
Require Import UMLang.BasicModuleTypes. 
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmFunc. 

Require Import Project.CommonTypes. 
Require  Import Contracts.TONTokenWallet.ClassTypes.

Require Import Wrapper.ClassTypes.
Require Import Wrapper.Interface.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(*TONTokenWallet only*)
Inductive MessagesAndEventsFields := | _OutgoingMessages_Wrapper | _EmittedEvents | _MessagesLog.
Inductive LedgerFieldsI := | _Contract | _ContractCopy | _VMState | _MessagesAndEvents | _MessagesAndEventsCopy | _LocalState | _LocalStateCopy .

Definition ContractFields := DWrapperFields.

Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 

Module WrapperPublicInterfaceModule := Wrapper.Interface.PublicInterface xt sm.

Module Export VMStateModule := VMStateModule xt sm. 
Module Export TypesModuleForLedger := Wrapper.ClassTypes.ClassTypes xt sm .
Import xt.
Module TONTonkenWalletModuleForPrice := 
                      Contracts.TONTokenWallet.ClassTypes.ClassTypes xt sm .


(* 2 *) Definition MessagesAndEventsL : list Type := 
 [ XHMap XAddress ( XQueue (OutgoingMessage  WrapperPublicInterfaceModule.IWrapper ) ) : Type ; 
   XList TVMEvent : Type ; 
   XString : Type ] .
GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
Opaque MessagesAndEventsLRecord .
 
(* 2 *) Definition ContractLRecord := TypesModuleForLedger.DWrapperLRecord.
Definition ContractLEmbeddedType := DWrapperLEmbeddedType.

Inductive LocalStateFields00000I := | ι000000 | ι000001 . 
Definition LocalState00000L := [ ( XHMap (string*nat) ( StateInitLRecord * XUInteger256 ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00000L LocalStateFields00000I . 
Opaque LocalState00000LRecord . 
 
Inductive LocalStateFields00001I := | ι000010 | ι000011 . 
Definition LocalState00001L := [ ( XHMap (string*nat) XCell ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00001L LocalStateFields00001I . 
Opaque LocalState00001LRecord . 

Inductive LocalStateFields00010I := | ι000100 | ι000101 . 
Definition LocalState00010L := [ ( XHMap (string*nat) StateInitLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00010L LocalStateFields00010I . 
Opaque LocalState00010LRecord . 

Inductive LocalStateFields00011I := | ι000110 | ι000111 . 
Definition LocalState00011L := [ ( XHMap (string*nat) XBool ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00011L LocalStateFields00011I . 
Opaque LocalState00011LRecord . 

Inductive LocalStateFields00100I := | ι001000 | ι001001 . 
Definition LocalState00100L := [ ( XHMap (string*nat) XAddress ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00100L LocalStateFields00100I . 
Opaque LocalState00100LRecord . 

Inductive LocalStateFields00101I := | ι001010 | ι001011 . 
Definition LocalState00101L := [ ( XHMap (string*nat) XAddress (* ITONTokenWalletPtrLRecord *) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00101L LocalStateFields00101I . 
Opaque LocalState00101LRecord . 

Inductive LocalStateFields00110I := | ι001100 | ι001101 . 
Definition LocalState00110L := [ ( XHMap (string*nat) WrapperRetLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00110L LocalStateFields00110I . 
Opaque LocalState00110LRecord . 
 
Inductive LocalStateFields00111I := | ι001110 | ι001111 . 
Definition LocalState00111L := [ ( XHMap (string*nat) XUInteger128 ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00111L LocalStateFields00111I . 
Opaque LocalState00111LRecord . 

Inductive LocalStateFields01000I := | ι010000 | ι010001 . 
Definition LocalState01000L := [ ( XHMap (string*nat) wrapper_details_infoLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01000L LocalStateFields01000I . 
Opaque LocalState01000LRecord . 

Inductive LocalStateFields01001I := | ι010010 | ι010011 . 
Definition LocalState01001L := [ ( XHMap (string*nat) XString ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01001L LocalStateFields01001I . 
Opaque LocalState01001LRecord . 

Inductive LocalStateFields01010I := | ι010100 | ι010101 . 
Definition LocalState01010L := [ ( XHMap (string*nat) XUInteger8 ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01010L LocalStateFields01010I . 
Opaque LocalState01010LRecord . 

Inductive LocalStateFields01011I := | ι010110 | ι010111 . 
Definition LocalState01011L := [ ( XHMap (string*nat) XUInteger256 ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01011L LocalStateFields01011I . 
Opaque LocalState01011LRecord . 

Inductive LocalStateFields01100I := | ι011000 | ι011001 . 
Definition LocalState01100L := [ ( XHMap (string*nat) XUInteger ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01100L LocalStateFields01100I . 
Opaque LocalState01100LRecord . 

Inductive LocalStateFields01101I := | ι011010 | ι011011 . 
Definition LocalState01101L := [ ( XHMap (string*nat) ( XMaybe XAddress ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01101L LocalStateFields01101I . 
Opaque LocalState01101LRecord . 

Inductive LocalStateFields01110I := | ι011100 | ι011101 . 
Definition LocalState01110L := [ ( XHMap (string*nat) ( StateInitLRecord * XAddress ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01110L LocalStateFields01110I . 
Opaque LocalState01110LRecord . 
 
Inductive LocalStateFields01111I := | ι011110 | ι011111 . 
Definition LocalState01111L := [ ( XHMap (string*nat) TONTonkenWalletModuleForPrice.DTONTokenWalletInternalLRecord (* record1 *) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01111L LocalStateFields01111I . 
Opaque LocalState01111LRecord . 

Inductive LocalStateFields10000I := | ι100000 | ι100001 . 
Definition LocalState10000L := [ ( XHMap (string*nat) FlexDeployWalletArgsLRecord (* record2 *) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10000L LocalStateFields10000I . 
Opaque LocalState10000LRecord . 

Inductive LocalStateFields10001I := | ι100010 | ι100011 . 
Definition LocalState10001L := [ ( XHMap (string*nat) DWrapperLRecord (* record3 *) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10001L LocalStateFields10001I . 
Opaque LocalState10001LRecord . 

Inductive LocalStateFields10010I := | ι100100 | ι100101 . 
Definition LocalState10010L := [ ( XHMap (string*nat) XUInteger (* record4 *) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10010L LocalStateFields10010I . 
Opaque LocalState10010LRecord . 

Inductive LocalStateFields10011I := | ι100110 | ι100111 . 
Definition LocalState10011L := [ ( XHMap (string*nat) XUInteger (* record5 *) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10011L LocalStateFields10011I . 
Opaque LocalState10011LRecord . 


Inductive LocalStateFields0000I := | ι00000 | ι00001 . 
Definition LocalState0000L := [ LocalState00000LRecord ; LocalState00001LRecord ] . 
GeneratePruvendoRecord LocalState0000L LocalStateFields0000I . 
Opaque LocalState0000LRecord . 

Inductive LocalStateFields0001I := | ι00010 | ι00011 . 
Definition LocalState0001L := [ LocalState00010LRecord ; LocalState00011LRecord ] . 
GeneratePruvendoRecord LocalState0001L LocalStateFields0001I . 
Opaque LocalState0001LRecord . 

Inductive LocalStateFields0010I := | ι00100 | ι00101 . 
Definition LocalState0010L := [ LocalState00100LRecord ; LocalState00101LRecord ] . 
GeneratePruvendoRecord LocalState0010L LocalStateFields0010I . 
Opaque LocalState0010LRecord . 
 
Inductive LocalStateFields0011I := | ι00110 | ι00111 . 
Definition LocalState0011L := [ LocalState00110LRecord ; LocalState00111LRecord ] . 
GeneratePruvendoRecord LocalState0011L LocalStateFields0011I . 
Opaque LocalState0011LRecord . 

Inductive LocalStateFields0100I := | ι01000 | ι01001 . 
Definition LocalState0100L := [ LocalState01000LRecord ; LocalState01001LRecord ] . 
GeneratePruvendoRecord LocalState0100L LocalStateFields0100I . 
Opaque LocalState0100LRecord . 

Inductive LocalStateFields0101I := | ι01010 | ι01011 . 
Definition LocalState0101L := [ LocalState01010LRecord ; LocalState01011LRecord ] . 
GeneratePruvendoRecord LocalState0101L LocalStateFields0101I . 
Opaque LocalState0101LRecord . 

Inductive LocalStateFields0110I := | ι01100 | ι01101 . 
Definition LocalState0110L := [ LocalState01100LRecord ; LocalState01101LRecord ] . 
GeneratePruvendoRecord LocalState0110L LocalStateFields0110I . 
Opaque LocalState0110LRecord . 

Inductive LocalStateFields0111I := | ι01110 | ι01111 . 
Definition LocalState0111L := [ LocalState01110LRecord ; LocalState01111LRecord ] . 
GeneratePruvendoRecord LocalState0111L LocalStateFields0111I . 
Opaque LocalState0111LRecord . 

Inductive LocalStateFields1000I := | ι10000 | ι10001 . 
Definition LocalState1000L := [ LocalState10000LRecord ; LocalState10001LRecord ] . 
GeneratePruvendoRecord LocalState1000L LocalStateFields1000I . 
Opaque LocalState1000LRecord . 

Inductive LocalStateFields1001I := | ι10010 | ι10011 . 
Definition LocalState1001L := [ LocalState10010LRecord ; LocalState10011LRecord ] . 
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

Elpi GeneratePruvendoRecord LedgerL LedgerFieldsI .
(***************************************)

 Transparent LocalState00000LRecord LocalState00001LRecord LocalState00010LRecord LocalState00011LRecord LocalState00100LRecord LocalState00101LRecord LocalState00110LRecord LocalState00111LRecord LocalState01000LRecord LocalState01001LRecord LocalState01010LRecord LocalState01011LRecord LocalState01100LRecord LocalState01101LRecord LocalState01110LRecord LocalState01111LRecord LocalState10000LRecord LocalState10001LRecord LocalState10010LRecord LocalState10011LRecord LocalState0000LRecord LocalState0001LRecord LocalState0010LRecord LocalState0011LRecord LocalState0100LRecord LocalState0101LRecord LocalState0110LRecord LocalState0111LRecord LocalState1000LRecord LocalState1001LRecord LocalState000LRecord LocalState001LRecord LocalState010LRecord LocalState011LRecord LocalState100LRecord LocalState00LRecord LocalState01LRecord LocalState0LRecord LocalStateLRecord .

Transparent MessagesAndEventsLRecord .
Transparent ContractLRecord .
Transparent LocalStateLRecord .
Transparent LedgerLRecord .

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

         
Obligation Tactic := idtac.



#[global, program] Instance LocalStateField00000 : LocalStateField ( StateInitLRecord * XUInteger256 ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00000). 
 eapply (LocalState00000LEmbeddedType ι000001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00000). 
 eapply (LocalState00000LEmbeddedType ι000000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00000 : typeclass_instances. 
 #[global, program] Instance LocalStateField00001 : LocalStateField XCell.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00001). 
 eapply (LocalState00001LEmbeddedType ι000011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00001). 
 eapply (LocalState00001LEmbeddedType ι000010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00001 : typeclass_instances. 
 #[global, program] Instance LocalStateField00010 : LocalStateField StateInitLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00010). 
 eapply (LocalState00010LEmbeddedType ι000101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00010). 
 eapply (LocalState00010LEmbeddedType ι000100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00010 : typeclass_instances. 
 #[global, program] Instance LocalStateField00011 : LocalStateField XBool.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00011). 
 eapply (LocalState00011LEmbeddedType ι000111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00011). 
 eapply (LocalState00011LEmbeddedType ι000110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00011 : typeclass_instances. 
 #[global, program] Instance LocalStateField00100 : LocalStateField XAddress.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00100). 
 eapply (LocalState00100LEmbeddedType ι001001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00100). 
 eapply (LocalState00100LEmbeddedType ι001000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00100 : typeclass_instances. 
 #[global, program] Instance LocalStateField00101 : LocalStateField XAddress (* ITONTokenWalletPtrLRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00101). 
 eapply (LocalState00101LEmbeddedType ι001011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00101). 
 eapply (LocalState00101LEmbeddedType ι001010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00101 : typeclass_instances. 
 #[global, program] Instance LocalStateField00110 : LocalStateField WrapperRetLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00110). 
 eapply (LocalState00110LEmbeddedType ι001101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00110). 
 eapply (LocalState00110LEmbeddedType ι001100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00110 : typeclass_instances. 
 #[global, program] Instance LocalStateField00111 : LocalStateField XUInteger128.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00111). 
 eapply (LocalState00111LEmbeddedType ι001111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00111). 
 eapply (LocalState00111LEmbeddedType ι001110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00111 : typeclass_instances. 
 #[global, program] Instance LocalStateField01000 : LocalStateField wrapper_details_infoLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01000). 
 eapply (LocalState01000LEmbeddedType ι010001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01000). 
 eapply (LocalState01000LEmbeddedType ι010000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01000 : typeclass_instances. 
 #[global, program] Instance LocalStateField01001 : LocalStateField XString.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01001). 
 eapply (LocalState01001LEmbeddedType ι010011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01001). 
 eapply (LocalState01001LEmbeddedType ι010010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01001 : typeclass_instances. 
 #[global, program] Instance LocalStateField01010 : LocalStateField XUInteger8.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01010). 
 eapply (LocalState01010LEmbeddedType ι010101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01010). 
 eapply (LocalState01010LEmbeddedType ι010100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01010 : typeclass_instances. 
 #[global, program] Instance LocalStateField01011 : LocalStateField XUInteger256.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01011). 
 eapply (LocalState01011LEmbeddedType ι010111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01011). 
 eapply (LocalState01011LEmbeddedType ι010110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01011 : typeclass_instances. 
 #[global, program] Instance LocalStateField01100 : LocalStateField XUInteger.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01100). 
 eapply (LocalState01100LEmbeddedType ι011001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01100). 
 eapply (LocalState01100LEmbeddedType ι011000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01100 : typeclass_instances. 
 #[global, program] Instance LocalStateField01101 : LocalStateField ( XMaybe XAddress ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01101). 
 eapply (LocalState01101LEmbeddedType ι011011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01101). 
 eapply (LocalState01101LEmbeddedType ι011010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01101 : typeclass_instances. 
 #[global, program] Instance LocalStateField01110 : LocalStateField ( StateInitLRecord * XAddress ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01110). 
 eapply (LocalState01110LEmbeddedType ι011101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01110). 
 eapply (LocalState01110LEmbeddedType ι011100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01110 : typeclass_instances. 
 #[global, program] Instance LocalStateField01111 : LocalStateField TONTonkenWalletModuleForPrice.DTONTokenWalletInternalLRecord (* record *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01111). 
 eapply (LocalState01111LEmbeddedType ι011111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01111). 
 eapply (LocalState01111LEmbeddedType ι011110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01111 : typeclass_instances. 
 #[global, program] Instance LocalStateField10000 : LocalStateField FlexDeployWalletArgsLRecord (* record *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10000). 
 eapply (LocalState10000LEmbeddedType ι100001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10000). 
 eapply (LocalState10000LEmbeddedType ι100000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10000 : typeclass_instances. 
 #[global, program] Instance LocalStateField10001 : LocalStateField DWrapperLRecord (* record *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10001). 
 eapply (LocalState10001LEmbeddedType ι100011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10001). 
 eapply (LocalState10001LEmbeddedType ι100010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10001 : typeclass_instances. 
 #[global, program] Instance LocalStateField10010 : LocalStateField XUInteger (* record *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10010). 
 eapply (LocalState10010LEmbeddedType ι100101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10010). 
 eapply (LocalState10010LEmbeddedType ι100100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10010 : typeclass_instances. 
 #[global, program] Instance LocalStateField10011 : LocalStateField XUInteger (* record *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10011). 
 eapply (LocalState10011LEmbeddedType ι100111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10011). 
 eapply (LocalState10011LEmbeddedType ι100110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10011 : typeclass_instances. 

Definition LocalStateField_XUInteger := LocalStateField01110 .
Definition LocalStateField_XBool := LocalStateField00011 .
Definition LocalStateField_XCell := LocalStateField00000 .

End Ledger .
