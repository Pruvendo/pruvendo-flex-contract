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
Require Import Flex.ClassTypes.
Require Import Flex.Interface.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) Inductive MessagesAndEventsFields := | _OutgoingMessages_SelfDeployer | _EmittedEvents | _MessagesLog.
(* 1 *) Inductive ContractFields := | deployer_pubkey_ | ownership_description_ | owner_address_ | tons_cfg_ | pair_code_ | xchg_pair_code_ | price_code_ | xchg_price_code_ | deals_limit_ .
(* 1 *) Inductive LedgerFieldsI := | _Contract | _ContractCopy | _VMState | _MessagesAndEvents | _MessagesAndEventsCopy | _LocalState | _LocalStateCopy .

Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 

Module SelfDeployerPublicInterfaceModule := PublicInterface xt sm.

Module Import SolidityNotationsClass := SolidityNotations xt sm.
Module Export VMStateModule := VMStateModule xt sm. 
Module Import TypesModuleForLedger := ClassTypes xt sm .
Import xt. 


(* 2 *) Definition MessagesAndEventsL : ClassGenerator.list Type := 
 [ ( XQueue SelfDeployerPublicInterfaceModule.OutgoingMessage ) : Type ; 
 ( XList TVMEvent ) : Type ; 
 ( XString ) : Type ] .
GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
  Opaque MessagesAndEventsLRecord .
 
(* 2 *) Definition ContractL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( XString ) : Type ; 
 ( XMaybe XAddress ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord ContractL ContractFields . 
 Opaque ContractLRecord . 


Inductive LocalFields00000I := | ι000000 | ι000001 . 
 Definition LocalState00000L := [ ( XHMap (string*nat) XInteger256 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00000L LocalFields00000I . 
 Opaque LocalState00000LRecord . 
 
 Inductive LocalFields00001I := | ι000010 | ι000011 . 
 Definition LocalState00001L := [ ( XHMap (string*nat) XInteger128 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00001L LocalFields00001I . 
 Opaque LocalState00001LRecord . 
 
 Inductive LocalFields00010I := | ι000100 | ι000101 . 
 Definition LocalState00010L := [ ( XHMap (string*nat) XInteger8 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00010L LocalFields00010I . 
 Opaque LocalState00010LRecord . 
 
 Inductive LocalFields00011I := | ι000110 | ι000111 .
 Definition LocalState00011L := [ ( XHMap (string*nat) ContractLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00011L LocalFields00011I . 
 Opaque LocalState00011LRecord . 
 
 Inductive LocalFields00100I := | ι001000 | ι001001 . 
 Definition LocalState00100L := [ ( XHMap (string*nat) XCell ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00100L LocalFields00100I . 
 Opaque LocalState00100LRecord . 
 
 Inductive LocalFields00101I := | ι001010 | ι001011 . 
 Definition LocalState00101L := [ ( XHMap (string*nat) StateInitLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00101L LocalFields00101I . 
 Opaque LocalState00101LRecord . 
 
 Inductive LocalFields00110I := | ι001100 | ι001101 . 
 Definition LocalState00110L := [ ( XHMap (string*nat) XString ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00110L LocalFields00110I . 
 Opaque LocalState00110LRecord . 
 
 Inductive LocalFields00111I := | ι001110 | ι001111 . 
 Definition LocalState00111L := [ ( XHMap (string*nat) ( XMaybe XAddress ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00111L LocalFields00111I . 
 Opaque LocalState00111LRecord . 
 
 Inductive LocalFields01000I := | ι010000 | ι010001 . 
 Definition LocalState01000L := [ ( XHMap (string*nat) XAddress ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01000L LocalFields01000I . 
 Opaque LocalState01000LRecord . 
 
 Inductive LocalFields01001I := | ι010010 | ι010011 . 
 Definition LocalState01001L := [ ( XHMap (string*nat) XBool ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01001L LocalFields01001I . 
 Opaque LocalState01001LRecord . 
 
 Inductive LocalFields01010I := | ι010100 | ι010101 . 
 Definition LocalState01010L := [ ( XHMap (string*nat) ( XAddress * XAddress ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01010L LocalFields01010I . 
 Opaque LocalState01010LRecord . 
 
 Inductive LocalFields01011I := | ι010110 | ι010111 . 
 Definition LocalState01011L := [ ( XHMap (string*nat) DTradingPairLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01011L LocalFields01011I . 
 Opaque LocalState01011LRecord . 
 
 Inductive LocalFields01100I := | ι011000 | ι011001 . 
 Definition LocalState01100L := [ ( XHMap (string*nat) ( StateInitLRecord * XAddress ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01100L LocalFields01100I . 
 Opaque LocalState01100LRecord . 
 
 Inductive LocalFields01101I := | ι011010 | ι011011 . 
 Definition LocalState01101L := [ ( XHMap (string*nat) addr_stdLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01101L LocalFields01101I . 
 Opaque LocalState01101LRecord . 
 
 Inductive LocalFields01110I := | ι011100 | ι011101 . 
 Definition LocalState01110L := [ ( XHMap (string*nat) DXchgPairLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01110L LocalFields01110I . 
 Opaque LocalState01110LRecord . 
 
 Inductive LocalFields01111I := | ι011110 | ι011111 . 
 Definition LocalState01111L := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01111L LocalFields01111I . 
 Opaque LocalState01111LRecord . 
 
 Inductive LocalFields10000I := | ι100000 | ι100001 . 
 Definition LocalState10000L := [ ( XHMap (string*nat) XSlice ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState10000L LocalFields10000I . 
 Opaque LocalState10000LRecord . 
 
 
 Inductive LocalFields0000I := | ι00000 | ι00001 . 
 Definition LocalState0000L := [ LocalState00000LRecord ; LocalState00001LRecord ] . 
 GeneratePruvendoRecord LocalState0000L LocalFields0000I . 
 Opaque LocalState0000LRecord . 
 
 Inductive LocalFields0001I := | ι00010 | ι00011 . 
 Definition LocalState0001L := [ LocalState00010LRecord ; LocalState00011LRecord ] . 
 GeneratePruvendoRecord LocalState0001L LocalFields0001I . 
 Opaque LocalState0001LRecord . 
 
 Inductive LocalFields0010I := | ι00100 | ι00101 . 
 Definition LocalState0010L := [ LocalState00100LRecord ; LocalState00101LRecord ] . 
 GeneratePruvendoRecord LocalState0010L LocalFields0010I . 
 Opaque LocalState0010LRecord . 
 
 Inductive LocalFields0011I := | ι00110 | ι00111 . 
 Definition LocalState0011L := [ LocalState00110LRecord ; LocalState00111LRecord ] . 
 GeneratePruvendoRecord LocalState0011L LocalFields0011I . 
 Opaque LocalState0011LRecord . 
 
 Inductive LocalFields0100I := | ι01000 | ι01001 . 
 Definition LocalState0100L := [ LocalState01000LRecord ; LocalState01001LRecord ] . 
 GeneratePruvendoRecord LocalState0100L LocalFields0100I . 
 Opaque LocalState0100LRecord . 
 
 Inductive LocalFields0101I := | ι01010 | ι01011 . 
 Definition LocalState0101L := [ LocalState01010LRecord ; LocalState01011LRecord ] . 
 GeneratePruvendoRecord LocalState0101L LocalFields0101I . 
 Opaque LocalState0101LRecord . 
 
 Inductive LocalFields0110I := | ι01100 | ι01101 . 
 Definition LocalState0110L := [ LocalState01100LRecord ; LocalState01101LRecord ] . 
 GeneratePruvendoRecord LocalState0110L LocalFields0110I . 
 Opaque LocalState0110LRecord . 
 
 Inductive LocalFields0111I := | ι01110 | ι01111 . 
 Definition LocalState0111L := [ LocalState01110LRecord ; LocalState01111LRecord ] . 
 GeneratePruvendoRecord LocalState0111L LocalFields0111I . 
 Opaque LocalState0111LRecord . 
 
 
 
 Inductive LocalFields000I := | ι0000 | ι0001 . 
 Definition LocalState000L := [ LocalState0000LRecord ; LocalState0001LRecord ] . 
 GeneratePruvendoRecord LocalState000L LocalFields000I . 
 Opaque LocalState000LRecord . 
 
 Inductive LocalFields001I := | ι0010 | ι0011 . 
 Definition LocalState001L := [ LocalState0010LRecord ; LocalState0011LRecord ] . 
 GeneratePruvendoRecord LocalState001L LocalFields001I . 
 Opaque LocalState001LRecord . 
 
 Inductive LocalFields010I := | ι0100 | ι0101 . 
 Definition LocalState010L := [ LocalState0100LRecord ; LocalState0101LRecord ] . 
 GeneratePruvendoRecord LocalState010L LocalFields010I . 
 Opaque LocalState010LRecord . 
 
 Inductive LocalFields011I := | ι0110 | ι0111 . 
 Definition LocalState011L := [ LocalState0110LRecord ; LocalState0111LRecord ] . 
 GeneratePruvendoRecord LocalState011L LocalFields011I . 
 Opaque LocalState011LRecord . 
 
 
 
 Inductive LocalFields00I := | ι000 | ι001 . 
 Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
 GeneratePruvendoRecord LocalState00L LocalFields00I . 
 Opaque LocalState00LRecord . 
 
 Inductive LocalFields01I := | ι010 | ι011 . 
 Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
 GeneratePruvendoRecord LocalState01L LocalFields01I . 
 Opaque LocalState01LRecord . 
 
 
 
 Inductive LocalFields0I := | ι00 | ι01 . 
 Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
 GeneratePruvendoRecord LocalState0L LocalFields0I . 
 Opaque LocalState0LRecord . 
 
 
 
 Inductive LocalFieldsI := | ι0 | ι1 . 
 Definition LocalStateL := [ LocalState0LRecord ; LocalState10000LRecord ] . 
 GeneratePruvendoRecord LocalStateL LocalFieldsI .
 Opaque LocalStateLRecord . 
 
 Transparent LocalState00000LRecord LocalState00001LRecord LocalState00010LRecord LocalState00011LRecord LocalState00100LRecord LocalState00101LRecord LocalState00110LRecord LocalState00111LRecord LocalState01000LRecord LocalState01001LRecord LocalState01010LRecord LocalState01011LRecord LocalState01100LRecord LocalState01101LRecord LocalState01110LRecord LocalState01111LRecord LocalState10000LRecord LocalState0000LRecord LocalState0001LRecord LocalState0010LRecord LocalState0011LRecord LocalState0100LRecord LocalState0101LRecord LocalState0110LRecord LocalState0111LRecord LocalState10000LRecord LocalState000LRecord LocalState001LRecord LocalState010LRecord LocalState011LRecord LocalState00LRecord LocalState01LRecord LocalState0LRecord LocalStateLRecord .
 


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

(***************************************)
Definition LedgerEmbedded := LedgerLEmbeddedType.
Definition LedgerLocalState := LocalStateLRecord .
Definition LocalDefault : LedgerLocalState -> LedgerLocalState := fun _ => default.
Definition LedgerPruvendoRecord := LedgerLPruvendoRecord .
Definition LedgerLocalFields := LocalFieldsI.
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
Definition LedgerVMStateField := _VMState .
Definition isoVMState : VMStateLRecord = (field_type (PruvendoRecord:=LedgerPruvendoRecord) LedgerVMStateField)
           := eq_refl.

Definition LedgerMessagesEmbedded := LedgerLEmbeddedType _MessagesAndEvents . 
Definition LedgerMessagesField := _MessagesAndEvents .
Definition MessagesAndEvents := MessagesAndEventsLRecord .
Definition isoMessages : MessagesAndEvents = (field_type (PruvendoRecord:=LedgerPruvendoRecord) LedgerMessagesField)
           := eq_refl.

         
Obligation Tactic := idtac.



#[global, program] Instance LocalStateField00000 : LocalStateField XInteger256.
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
 #[global, program] Instance LocalStateField00001 : LocalStateField XInteger128.
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
 #[global, program] Instance LocalStateField00010 : LocalStateField XInteger8.
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
 #[global, program] Instance LocalStateField00011 : LocalStateField ContractLRecord.
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
 #[global, program] Instance LocalStateField00100 : LocalStateField XCell.
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
 #[global, program] Instance LocalStateField00101 : LocalStateField StateInitLRecord.
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
 #[global, program] Instance LocalStateField00110 : LocalStateField XString.
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
 #[global, program] Instance LocalStateField00111 : LocalStateField ( XMaybe XAddress ).
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
 #[global, program] Instance LocalStateField01000 : LocalStateField XAddress.
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
 #[global, program] Instance LocalStateField01001 : LocalStateField XBool.
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
 #[global, program] Instance LocalStateField01010 : LocalStateField ( XAddress * XAddress ).
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
 #[global, program] Instance LocalStateField01011 : LocalStateField DTradingPairLRecord.
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
 #[global, program] Instance LocalStateField01100 : LocalStateField ( StateInitLRecord * XAddress ).
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
 #[global, program] Instance LocalStateField01101 : LocalStateField addr_stdLRecord.
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
 #[global, program] Instance LocalStateField01110 : LocalStateField DXchgPairLRecord.
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
 #[global, program] Instance LocalStateField01111 : LocalStateField XInteger.
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
 #[global, program] Instance LocalStateField10000 : LocalStateField XSlice.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply (LocalState10000LEmbeddedType ι100001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply (LocalState10000LEmbeddedType ι100000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10000 : typeclass_instances. 



Definition LocalStateField_XInteger := LocalStateField01111 .
Definition LocalStateField_XBool := LocalStateField01001 .
Definition LocalStateField_XCell := LocalStateField00100 .


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




