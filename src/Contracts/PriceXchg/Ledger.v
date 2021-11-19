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
Require Import Contracts.PriceXchg.ClassTypes.
Require Import Contracts.PriceXchg.Interface.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) Inductive MessagesAndEventsFields := | _OutgoingMessages_Price | _EmittedEvents | _MessagesLog.
(* 1 *) Inductive ContractFields := | price_ | sells_amount_ | buys_amount_ | flex_ | min_amount_ | deals_limit_ | notify_addr_ | workchain_id_ | tons_cfg_ | tip3_code_ | major_tip3cfg_ | minor_tip3cfg_ | sells_ | buys_ .
(* 1 *) Inductive LedgerFieldsI := | _Contract | _ContractCopy | _VMState | _MessagesAndEvents | _MessagesAndEventsCopy | _LocalState | _LocalStateCopy .

Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 

Module PriceXchgPublicInterfaceModule := PublicInterface xt sm.

Module Import SolidityNotationsClass := SolidityNotations xt sm.
Module Export VMStateModule := VMStateModule xt sm. 
Module Export TypesModuleForLedger := ClassTypes xt sm .
Import xt.

Local Open Scope ursus_scope.

(* 2 *) Definition MessagesAndEventsL : list Type := 
 [ ( XQueue PriceXchgPublicInterfaceModule.OutgoingMessage ) : Type ; 
 ( XList TVMEvent ) : Type ; 
 ( XString ) : Type ] .
GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
  Opaque MessagesAndEventsLRecord .
 
(* 2 *) Definition ContractL : list Type := 
 [ ( RationalPriceLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XAddress (* IFlexNotifyPtrLRecord *) ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord ContractL ContractFields . 
 Opaque ContractLRecord . 

Inductive LocalStateFields00000I := | ι000000 | ι000001 . 
 Definition LocalState00000L := [ ( XHMap (string*nat) ( StateInitLRecord * XInteger256 ) ) : Type ; ( XHMap string nat ) : Type ] . 
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
 Definition LocalState00100L := [ ( XHMap (string*nat) ( XMaybe XInteger128 ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00100L LocalStateFields00100I . 
 Opaque LocalState00100LRecord . 
 
 Inductive LocalStateFields00101I := | ι001010 | ι001011 . 
 Definition LocalState00101L := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00101L LocalStateFields00101I . 
 Opaque LocalState00101LRecord . 
 
 Inductive LocalStateFields00110I := | ι001100 | ι001101 . 
 Definition LocalState00110L := [ ( XHMap (string*nat) ( XBool * XBool * XInteger128 ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00110L LocalStateFields00110I . 
 Opaque LocalState00110LRecord . 
 
 Inductive LocalStateFields00111I := | ι001110 | ι001111 . 
 Definition LocalState00111L := [ ( XHMap (string*nat) XInteger128 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState00111L LocalStateFields00111I . 
 Opaque LocalState00111LRecord . 
 
 Inductive LocalStateFields01000I := | ι010000 | ι010001 . 
 Definition LocalState01000L := [ ( XHMap (string*nat) ( XInteger * OrderInfoXchgLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01000L LocalStateFields01000I . 
 Opaque LocalState01000LRecord . 
 
 Inductive LocalStateFields01001I := | ι010010 | ι010011 . 
 Definition LocalState01001L := [ ( XHMap (string*nat) OrderRetLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01001L LocalStateFields01001I . 
 Opaque LocalState01001LRecord . 
 
 Inductive LocalStateFields01010I := | ι010100 | ι010101 . 
 Definition LocalState01010L := [ ( XHMap (string*nat) process_retLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01010L LocalStateFields01010I . 
 Opaque LocalState01010LRecord . 
 
 Inductive LocalStateFields01011I := | ι010110 | ι010111 . 
 Definition LocalState01011L := [ ( XHMap (string*nat) dealerLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01011L LocalStateFields01011I . 
 Opaque LocalState01011LRecord . 
 
 Inductive LocalStateFields01100I := | ι011000 | ι011001 . 
 Definition LocalState01100L := [ ( XHMap (string*nat) ( XAddress * XInteger (* Grams *) ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01100L LocalStateFields01100I . 
 Opaque LocalState01100LRecord . 
 
 Inductive LocalStateFields01101I := | ι011010 | ι011011 . 
 Definition LocalState01101L := [ ( XHMap (string*nat) XAddress ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01101L LocalStateFields01101I . 
 Opaque LocalState01101LRecord . 
 
 Inductive LocalStateFields01110I := | ι011100 | ι011101 . 
 Definition LocalState01110L := [ ( XHMap (string*nat) (XMaybe OrderRetLRecord) (* XAddress *) (* ITONTokenWalletPtrLRecord *) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01110L LocalStateFields01110I . 
 Opaque LocalState01110LRecord . 
 
 Inductive LocalStateFields01111I := | ι011110 | ι011111 . 
 Definition LocalState01111L := [ ( XHMap (string*nat) (XQueue OrderInfoXchgLRecord) (* XInteger *) (* Grams *) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState01111L LocalStateFields01111I . 
 Opaque LocalState01111LRecord . 
 
 Inductive LocalStateFields10000I := | ι100000 | ι100001 . 
 Definition LocalState10000L := [ ( XHMap (string*nat) OrderInfoXchgLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState10000L LocalStateFields10000I . 
 Opaque LocalState10000LRecord . 
 
 Inductive LocalStateFields10001I := | ι100010 | ι100011 . 
 Definition LocalState10001L := [ ( XHMap (string*nat) addr_std_fixedLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState10001L LocalStateFields10001I . 
 Opaque LocalState10001LRecord . 
 
 Inductive LocalStateFields10010I := | ι100100 | ι100101 . 
 Definition LocalState10010L := [ ( XHMap (string*nat) DetailsInfoXchgLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState10010L LocalStateFields10010I . 
 Opaque LocalState10010LRecord . 
 
 Inductive LocalStateFields10011I := | ι100110 | ι100111 . 
 Definition LocalState10011L := [ ( XHMap (string*nat) TonsConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState10011L LocalStateFields10011I . 
 Opaque LocalState10011LRecord . 
 
 Inductive LocalStateFields10100I := | ι101000 | ι101001 . 
 Definition LocalState10100L := [ ( XHMap (string*nat) ( XHMap XInteger OrderInfoXchgLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState10100L LocalStateFields10100I . 
 Opaque LocalState10100LRecord . 
 
 Inductive LocalStateFields10101I := | ι101010 | ι101011 . 
 Definition LocalState10101L := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState10101L LocalStateFields10101I . 
 Opaque LocalState10101LRecord . 
 
 Inductive LocalStateFields10110I := | ι101100 | ι101101 . 
 Definition LocalState10110L := [ ( XHMap (string*nat) XInteger256 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState10110L LocalStateFields10110I . 
 Opaque LocalState10110LRecord . 
 
 Inductive LocalStateFields10111I := | ι101110 | ι101111 . 
 Definition LocalState10111L := [ ( XHMap (string*nat) ( XMaybe XAddress ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState10111L LocalStateFields10111I . 
 Opaque LocalState10111LRecord . 
 
 Inductive LocalStateFields11000I := | ι110000 | ι110001 .
 Definition LocalState11000L := [ ( XHMap (string*nat) ( XMaybe (XInteger # OrderInfoXchgLRecord) ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState11000L LocalStateFields11000I . 
 Opaque LocalState11000LRecord . 
 
 Inductive LocalStateFields11001I := | ι110010 | ι110011 . 
 Definition LocalState11001L := [ ( XHMap (string*nat) PayloadArgsLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState11001L LocalStateFields11001I . 
 Opaque LocalState11001LRecord . 
 
 Inductive LocalStateFields11010I := | ι110100 | ι110101 . 
 Definition LocalState11010L := [ ( XHMap (string*nat) DTONTokenWalletInternalLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState11010L LocalStateFields11010I . 
 Opaque LocalState11010LRecord . 
 
 
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
 
 Inductive LocalStateFields1010I := | ι10100 | ι10101 . 
 Definition LocalState1010L := [ LocalState10100LRecord ; LocalState10101LRecord ] . 
 GeneratePruvendoRecord LocalState1010L LocalStateFields1010I . 
 Opaque LocalState1010LRecord . 
 
 Inductive LocalStateFields1011I := | ι10110 | ι10111 . 
 Definition LocalState1011L := [ LocalState10110LRecord ; LocalState10111LRecord ] . 
 GeneratePruvendoRecord LocalState1011L LocalStateFields1011I . 
 Opaque LocalState1011LRecord . 
 
 Inductive LocalStateFields1100I := | ι11000 | ι11001 . 
 Definition LocalState1100L := [ LocalState11000LRecord ; LocalState11001LRecord ] . 
 GeneratePruvendoRecord LocalState1100L LocalStateFields1100I . 
 Opaque LocalState1100LRecord . 
 
 
 
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
 
 Inductive LocalStateFields101I := | ι1010 | ι1011 . 
 Definition LocalState101L := [ LocalState1010LRecord ; LocalState1011LRecord ] . 
 GeneratePruvendoRecord LocalState101L LocalStateFields101I . 
 Opaque LocalState101LRecord . 
 
 Inductive LocalStateFields110I := | ι1100 | ι1101 . 
 Definition LocalState110L := [ LocalState1100LRecord ; LocalState11010LRecord ] . 
 GeneratePruvendoRecord LocalState110L LocalStateFields110I . 
 Opaque LocalState110LRecord . 
 
 
 
 Inductive LocalStateFields00I := | ι000 | ι001 . 
 Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
 GeneratePruvendoRecord LocalState00L LocalStateFields00I . 
 Opaque LocalState00LRecord . 
 
 Inductive LocalStateFields01I := | ι010 | ι011 . 
 Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
 GeneratePruvendoRecord LocalState01L LocalStateFields01I . 
 Opaque LocalState01LRecord . 
 
 Inductive LocalStateFields10I := | ι100 | ι101 . 
 Definition LocalState10L := [ LocalState100LRecord ; LocalState101LRecord ] . 
 GeneratePruvendoRecord LocalState10L LocalStateFields10I . 
 Opaque LocalState10LRecord . 
 
 
 
 Inductive LocalStateFields0I := | ι00 | ι01 . 
 Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
 GeneratePruvendoRecord LocalState0L LocalStateFields0I . 
 Opaque LocalState0LRecord . 
 
 Inductive LocalStateFields1I := | ι10 | ι11 . 
 Definition LocalState1L := [ LocalState10LRecord ; LocalState110LRecord ] . 
 GeneratePruvendoRecord LocalState1L LocalStateFields1I . 
 Opaque LocalState1LRecord . 
 
 
 
 Inductive LocalStateFieldsI := | ι0 | ι1 . 
 Definition LocalStateL := [ LocalState0LRecord ; LocalState1LRecord ] . 
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

Transparent LocalState00000LRecord LocalState00001LRecord LocalState00010LRecord LocalState00011LRecord LocalState00100LRecord LocalState00101LRecord LocalState00110LRecord LocalState00111LRecord LocalState01000LRecord LocalState01001LRecord LocalState01010LRecord LocalState01011LRecord LocalState01100LRecord LocalState01101LRecord LocalState01110LRecord LocalState01111LRecord LocalState10000LRecord LocalState10001LRecord LocalState10010LRecord LocalState10011LRecord LocalState10100LRecord LocalState10101LRecord LocalState10110LRecord LocalState10111LRecord LocalState11000LRecord LocalState11001LRecord LocalState11010LRecord LocalState0000LRecord LocalState0001LRecord LocalState0010LRecord LocalState0011LRecord LocalState0100LRecord LocalState0101LRecord LocalState0110LRecord LocalState0111LRecord LocalState1000LRecord LocalState1001LRecord LocalState1010LRecord LocalState1011LRecord LocalState1100LRecord LocalState11010LRecord LocalState000LRecord LocalState001LRecord LocalState010LRecord LocalState011LRecord LocalState100LRecord LocalState101LRecord LocalState110LRecord LocalState00LRecord LocalState01LRecord LocalState10LRecord LocalState0LRecord LocalState1LRecord LocalStateLRecord .
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

#[global, program] Instance LocalStateField00000 : LocalStateField ( StateInitLRecord * XInteger256 ).
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
 #[global, program] Instance LocalStateField00100 : LocalStateField ( XMaybe XInteger128 ).
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
 #[global, program] Instance LocalStateField00101 : LocalStateField XInteger.
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
 #[global, program] Instance LocalStateField00110 : LocalStateField ( XBool * XBool * XInteger128 ).
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
 #[global, program] Instance LocalStateField00111 : LocalStateField XInteger128.
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
 #[global, program] Instance LocalStateField01000 : LocalStateField ( XInteger * OrderInfoXchgLRecord ).
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
 #[global, program] Instance LocalStateField01001 : LocalStateField OrderRetLRecord.
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
 #[global, program] Instance LocalStateField01010 : LocalStateField process_retLRecord.
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
 #[global, program] Instance LocalStateField01011 : LocalStateField dealerLRecord.
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
 #[global, program] Instance LocalStateField01100 : LocalStateField ( XAddress * XInteger (* Grams *) ).
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
 #[global, program] Instance LocalStateField01101 : LocalStateField XAddress.
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
 #[global, program] Instance LocalStateField01110 : LocalStateField (XMaybe OrderRetLRecord) (* XAddress *) (* ITONTokenWalletPtrLRecord *).
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
 #[global, program] Instance LocalStateField01111 : LocalStateField (XQueue OrderInfoXchgLRecord) (* XInteger *) (* Grams *).
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
 #[global, program] Instance LocalStateField10000 : LocalStateField OrderInfoXchgLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10000). 
 eapply (LocalState10000LEmbeddedType ι100001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10000). 
 eapply (LocalState10000LEmbeddedType ι100000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10000 : typeclass_instances. 
 #[global, program] Instance LocalStateField10001 : LocalStateField addr_std_fixedLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10001). 
 eapply (LocalState10001LEmbeddedType ι100011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10001). 
 eapply (LocalState10001LEmbeddedType ι100010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10001 : typeclass_instances. 
 #[global, program] Instance LocalStateField10010 : LocalStateField DetailsInfoXchgLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10010). 
 eapply (LocalState10010LEmbeddedType ι100101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10010). 
 eapply (LocalState10010LEmbeddedType ι100100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10010 : typeclass_instances. 
 #[global, program] Instance LocalStateField10011 : LocalStateField TonsConfigLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10011). 
 eapply (LocalState10011LEmbeddedType ι100111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10011). 
 eapply (LocalState10011LEmbeddedType ι100110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10011 : typeclass_instances. 
 #[global, program] Instance LocalStateField10100 : LocalStateField ( XHMap XInteger OrderInfoXchgLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι1010). 
 eapply TransEmbedded. eapply (_ ι10100). 
 eapply (LocalState10100LEmbeddedType ι101001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι1010). 
 eapply TransEmbedded. eapply (_ ι10100). 
 eapply (LocalState10100LEmbeddedType ι101000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10100 : typeclass_instances. 
 #[global, program] Instance LocalStateField10101 : LocalStateField XInteger.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι1010). 
 eapply TransEmbedded. eapply (_ ι10101). 
 eapply (LocalState10101LEmbeddedType ι101011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι1010). 
 eapply TransEmbedded. eapply (_ ι10101). 
 eapply (LocalState10101LEmbeddedType ι101010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10101 : typeclass_instances. 
 #[global, program] Instance LocalStateField10110 : LocalStateField XInteger256.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι1011). 
 eapply TransEmbedded. eapply (_ ι10110). 
 eapply (LocalState10110LEmbeddedType ι101101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι1011). 
 eapply TransEmbedded. eapply (_ ι10110). 
 eapply (LocalState10110LEmbeddedType ι101100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10110 : typeclass_instances. 
 #[global, program] Instance LocalStateField10111 : LocalStateField ( XMaybe XAddress ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι1011). 
 eapply TransEmbedded. eapply (_ ι10111). 
 eapply (LocalState10111LEmbeddedType ι101111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι10). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι1011). 
 eapply TransEmbedded. eapply (_ ι10111). 
 eapply (LocalState10111LEmbeddedType ι101110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10111 : typeclass_instances. 
 #[global, program] Instance LocalStateField11000 : LocalStateField ( XMaybe (XInteger # OrderInfoXchgLRecord) ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι11). 
 eapply TransEmbedded. eapply (_ ι1100). 
 eapply TransEmbedded. eapply (_ ι11000). 
 eapply (LocalState11000LEmbeddedType ι110001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι11). 
 eapply TransEmbedded. eapply (_ ι1100). 
 eapply TransEmbedded. eapply (_ ι11000). 
 eapply (LocalState11000LEmbeddedType ι110000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField11000 : typeclass_instances. 
 #[global, program] Instance LocalStateField11001 : LocalStateField PayloadArgsLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι11). 
 eapply TransEmbedded. eapply (_ ι1100). 
 eapply TransEmbedded. eapply (_ ι11001). 
 eapply (LocalState11001LEmbeddedType ι110011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι11). 
 eapply TransEmbedded. eapply (_ ι1100). 
 eapply TransEmbedded. eapply (_ ι11001). 
 eapply (LocalState11001LEmbeddedType ι110010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField11001 : typeclass_instances. 
 #[global, program] Instance LocalStateField11010 : LocalStateField DTONTokenWalletInternalLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι11). 
 eapply TransEmbedded. eapply (_ ι1101). 
 eapply (LocalState11010LEmbeddedType ι110101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι11). 
 eapply TransEmbedded. eapply (_ ι1101). 
 eapply (LocalState11010LEmbeddedType ι110100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField11010 : typeclass_instances. 

Definition LocalStateField_XInteger := LocalStateField01110 .
Definition LocalStateField_XBool := LocalStateField00011 .
Definition LocalStateField_XCell := LocalStateField00000 .


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




























