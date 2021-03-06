Require Import Coq.Program.Basics. 
Require Import String. 

Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 
Require Import FinProof.ProgrammingWith.  

Require Import UMLang.UrsusLib. 
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc. 
Require Import UrsusTVM.Cpp.TvmCells. 

Require Project.CommonTypes. 

Require Import Price.ClassTypes.
Require TONTokenWallet.ClassTypes.
Require Flex.ClassTypes.

Require Import Price.Interface.
Require Import Flex.Interface.
Require Import TONTokenWallet.Interface.

Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.


(* 1 *) Inductive MessagesAndEventsFields := 
  | _OutgoingMessages_Price 
  | _OutgoingMessages_ITONTokenWallet 
  | _OutgoingMessages_IFlexNotify
  | _OutgoingMessages_IPriceCallBack
  | _EmittedEvents 
  | _GlobalParams
  | _OutgoingMessageParams
  | _MessagesLog.

(* 1 *) Inductive LedgerFieldsI := | _Contract | _ContractCopy | _VMState | _MessagesAndEvents | _MessagesAndEventsCopy | _LocalState | _LocalStateCopy .
Definition ContractFields := DPriceFields. 

Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 



(* Module Import BasicTypesClass := BasicTypes xt sm. *)
Module Export VMStateModule := VMStateModule xt sm. 
Module Export TypesModuleForLedger := Contracts.Price.ClassTypes.ClassTypes xt sm .
Import xt.


Module PricePublicInterfaceModule := Price.Interface.PublicInterface xt sm.
Module TokenWalletClassTypesModule := TONTokenWallet.ClassTypes.ClassTypes xt sm .
Module FlexClassTypesModule := Flex.ClassTypes.ClassTypes xt sm .

Module TONTokenWalletInterfaceModule := TONTokenWallet.Interface.PublicInterface xt sm .
Module FlexInterfaceModule := Flex.Interface.PublicInterface xt sm .

(* 2 *) Definition MessagesAndEventsL : list Type := 
 [  XHMap address (XQueue (OutgoingMessage PricePublicInterfaceModule.IPrice)) : Type ; 
 ( XHMap address (XQueue (OutgoingMessage TONTokenWalletInterfaceModule.ITONTokenWallet )) ) : Type ;
 ( XHMap address (XQueue (OutgoingMessage FlexInterfaceModule.IFlexNotify )) ) : Type ;
 ( XHMap address (XQueue (OutgoingMessage PricePublicInterfaceModule.IPriceCallback )) ) : Type ;
   XList TVMEvent : Type ; 
   GlobalParamsLRecord: Type ;
   OutgoingMessageParamsLRecord: Type ;
   XList XString : Type ] .
GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
Opaque MessagesAndEventsLRecord .
 
(* 2 *) Definition ContractLRecord := DPriceLRecord.

 Definition ContractLEmbeddedType := DPriceLEmbeddedType. 

Inductive LocalStateFields00000I := | ??000000 | ??000001 . 
Definition LocalState00000L := [ ( XHMap (string*nat) ( StateInitLRecord * XUInteger256 ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00000L LocalStateFields00000I . 
Opaque LocalState00000LRecord . 

Inductive LocalStateFields00001I := | ??000010 | ??000011 . 
Definition LocalState00001L := [ ( XHMap (string*nat) cell_ ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00001L LocalStateFields00001I . 
Opaque LocalState00001LRecord . 

Inductive LocalStateFields00010I := | ??000100 | ??000101 . 
Definition LocalState00010L := [ ( XHMap (string*nat) StateInitLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00010L LocalStateFields00010I . 
Opaque LocalState00010LRecord . 

Inductive LocalStateFields00011I := | ??000110 | ??000111 . 
Definition LocalState00011L := [ ( XHMap (string*nat) XBool ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00011L LocalStateFields00011I . 
Opaque LocalState00011LRecord . 

Inductive LocalStateFields00100I := | ??001000 | ??001001 . 
Definition LocalState00100L := [ ( XHMap (string*nat) ( XMaybe XUInteger128 ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00100L LocalStateFields00100I . 
Opaque LocalState00100LRecord . 

Inductive LocalStateFields00101I := | ??001010 | ??001011 . 
Definition LocalState00101L := [ ( XHMap (string*nat) XUInteger ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00101L LocalStateFields00101I . 
Opaque LocalState00101LRecord . 

Inductive LocalStateFields00110I := | ??001100 | ??001101 . 
Definition LocalState00110L := [ ( XHMap (string*nat) ( XBool * XBool * XUInteger128 ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00110L LocalStateFields00110I . 
Opaque LocalState00110LRecord . 

Inductive LocalStateFields00111I := | ??001110 | ??001111 . 
Definition LocalState00111L := [ ( XHMap (string*nat) XUInteger128 ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00111L LocalStateFields00111I . 
Opaque LocalState00111LRecord . 

Inductive LocalStateFields01000I := | ??010000 | ??010001 .
Definition LocalState01000L := [ ( XHMap (string*nat) ( XMaybe (XUInteger * OrderInfoLRecord) ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01000L LocalStateFields01000I . 
Opaque LocalState01000LRecord . 

Inductive LocalStateFields01001I := | ??010010 | ??010011 . 
Definition LocalState01001L := [ ( XHMap (string*nat) OrderRetLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01001L LocalStateFields01001I . 
Opaque LocalState01001LRecord . 

Inductive LocalStateFields01010I := | ??010100 | ??010101 . 
Definition LocalState01010L := [ ( XHMap (string*nat) address ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01010L LocalStateFields01010I . 
Opaque LocalState01010LRecord . 

Inductive LocalStateFields01011I := | ??010110 | ??010111 . 
Definition LocalState01011L := [ ( XHMap (string*nat) address (* IFlexNotifyPtrLRecord *) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01011L LocalStateFields01011I . 
Opaque LocalState01011LRecord . 

Inductive LocalStateFields01100I := | ??011000 | ??011001 . 
Definition LocalState01100L := [ ( XHMap (string*nat) TonsConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01100L LocalStateFields01100I . 
Opaque LocalState01100LRecord . 

Inductive LocalStateFields01101I := | ??011010 | ??011011 . 
Definition LocalState01101L := [ ( XHMap (string*nat) ( XMaybe OrderRetLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01101L LocalStateFields01101I . 
Opaque LocalState01101LRecord . 

Inductive LocalStateFields01110I := | ??011100 | ??011101 . 
Definition LocalState01110L := [ ( XHMap (string*nat) process_retLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01110L LocalStateFields01110I . 
Opaque LocalState01110LRecord . 

Inductive LocalStateFields01111I := | ??011110 | ??011111 . 
Definition LocalState01111L := [ ( XHMap (string*nat) dealerLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01111L LocalStateFields01111I . 
Opaque LocalState01111LRecord . 

Inductive LocalStateFields10000I := | ??100000 | ??100001 . 
Definition LocalState10000L := [ ( XHMap (string*nat) address (* ITONTokenWalletPtrLRecord *) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10000L LocalStateFields10000I . 
Opaque LocalState10000LRecord . 

Inductive LocalStateFields10001I := | ??100010 | ??100011 . 
Definition LocalState10001L := [ ( XHMap (string*nat) Grams) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10001L LocalStateFields10001I . 
Opaque LocalState10001LRecord . 

Inductive LocalStateFields10010I := | ??100100 | ??100101 . 
Definition LocalState10010L := [ ( XHMap (string*nat) OrderInfoLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10010L LocalStateFields10010I . 
Opaque LocalState10010LRecord . 

Inductive LocalStateFields10011I := | ??100110 | ??100111 . 
Definition LocalState10011L := [ ( XHMap (string*nat) addr_std_fixed ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10011L LocalStateFields10011I . 
Opaque LocalState10011LRecord . 

Inductive LocalStateFields10100I := | ??101000 | ??101001 . 
Definition LocalState10100L := [ ( XHMap (string*nat) DetailsInfoLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10100L LocalStateFields10100I . 
Opaque LocalState10100LRecord . 

Inductive LocalStateFields10101I := | ??101010 | ??101011 . 
Definition LocalState10101L := [ ( XHMap (string*nat) ( XHMap XUInteger OrderInfoLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10101L LocalStateFields10101I . 
Opaque LocalState10101LRecord . 

Inductive LocalStateFields10110I := | ??101100 | ??101101 . 
Definition LocalState10110L := [ ( XHMap (string*nat) XUInteger ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10110L LocalStateFields10110I . 
Opaque LocalState10110LRecord . 

Inductive LocalStateFields10111I := | ??101110 | ??101111 . 
Definition LocalState10111L := [ ( XHMap (string*nat) XUInteger256 ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10111L LocalStateFields10111I . 
Opaque LocalState10111LRecord . 

Inductive LocalStateFields11000I := | ??110000 | ??110001 . 
Definition LocalState11000L := [ ( XHMap (string*nat) ( XMaybe address ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState11000L LocalStateFields11000I . 
Opaque LocalState11000LRecord . 

Inductive LocalStateFields11001I := | ??110010 | ??110011 . 
Definition LocalState11001L := [ ( XHMap (string*nat) TokenWalletClassTypesModule.DTONTokenWalletInternalLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState11001L LocalStateFields11001I . 
Opaque LocalState11001LRecord . 

Inductive LocalStateFields11010I := | ??110100 | ??110101 . 
Definition LocalState11010L := [ ( XHMap (string*nat) SellArgsLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState11010L LocalStateFields11010I . 
Opaque LocalState11010LRecord . 

Inductive LocalStateFields11011I := | ??110110 | ??110111 . 
Definition LocalState11011L := [ ( XHMap (string*nat) XUInteger ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState11011L LocalStateFields11011I . 
Opaque LocalState11011LRecord . 


Inductive LocalStateFields0000I := | ??00000 | ??00001 . 
Definition LocalState0000L := [ LocalState00000LRecord ; LocalState00001LRecord ] . 
GeneratePruvendoRecord LocalState0000L LocalStateFields0000I . 
Opaque LocalState0000LRecord . 

Inductive LocalStateFields0001I := | ??00010 | ??00011 . 
Definition LocalState0001L := [ LocalState00010LRecord ; LocalState00011LRecord ] . 
GeneratePruvendoRecord LocalState0001L LocalStateFields0001I . 
Opaque LocalState0001LRecord . 

Inductive LocalStateFields0010I := | ??00100 | ??00101 . 
Definition LocalState0010L := [ LocalState00100LRecord ; LocalState00101LRecord ] . 
GeneratePruvendoRecord LocalState0010L LocalStateFields0010I . 
Opaque LocalState0010LRecord . 

Inductive LocalStateFields0011I := | ??00110 | ??00111 . 
Definition LocalState0011L := [ LocalState00110LRecord ; LocalState00111LRecord ] . 
GeneratePruvendoRecord LocalState0011L LocalStateFields0011I . 
Opaque LocalState0011LRecord . 

Inductive LocalStateFields0100I := | ??01000 | ??01001 . 
Definition LocalState0100L := [ LocalState01000LRecord ; LocalState01001LRecord ] . 
GeneratePruvendoRecord LocalState0100L LocalStateFields0100I . 
Opaque LocalState0100LRecord . 

Inductive LocalStateFields0101I := | ??01010 | ??01011 . 
Definition LocalState0101L := [ LocalState01010LRecord ; LocalState01011LRecord ] . 
GeneratePruvendoRecord LocalState0101L LocalStateFields0101I . 
Opaque LocalState0101LRecord . 

Inductive LocalStateFields0110I := | ??01100 | ??01101 . 
Definition LocalState0110L := [ LocalState01100LRecord ; LocalState01101LRecord ] . 
GeneratePruvendoRecord LocalState0110L LocalStateFields0110I . 
Opaque LocalState0110LRecord . 

Inductive LocalStateFields0111I := | ??01110 | ??01111 . 
Definition LocalState0111L := [ LocalState01110LRecord ; LocalState01111LRecord ] . 
GeneratePruvendoRecord LocalState0111L LocalStateFields0111I . 
Opaque LocalState0111LRecord . 

Inductive LocalStateFields1000I := | ??10000 | ??10001 . 
Definition LocalState1000L := [ LocalState10000LRecord ; LocalState10001LRecord ] . 
GeneratePruvendoRecord LocalState1000L LocalStateFields1000I . 
Opaque LocalState1000LRecord . 

Inductive LocalStateFields1001I := | ??10010 | ??10011 . 
Definition LocalState1001L := [ LocalState10010LRecord ; LocalState10011LRecord ] . 
GeneratePruvendoRecord LocalState1001L LocalStateFields1001I . 
Opaque LocalState1001LRecord . 

Inductive LocalStateFields1010I := | ??10100 | ??10101 . 
Definition LocalState1010L := [ LocalState10100LRecord ; LocalState10101LRecord ] . 
GeneratePruvendoRecord LocalState1010L LocalStateFields1010I . 
Opaque LocalState1010LRecord . 

Inductive LocalStateFields1011I := | ??10110 | ??10111 . 
Definition LocalState1011L := [ LocalState10110LRecord ; LocalState10111LRecord ] . 
GeneratePruvendoRecord LocalState1011L LocalStateFields1011I . 
Opaque LocalState1011LRecord . 

Inductive LocalStateFields1100I := | ??11000 | ??11001 . 
Definition LocalState1100L := [ LocalState11000LRecord ; LocalState11001LRecord ] . 
GeneratePruvendoRecord LocalState1100L LocalStateFields1100I . 
Opaque LocalState1100LRecord . 

Inductive LocalStateFields1101I := | ??11010 | ??11011 . 
Definition LocalState1101L := [ LocalState11010LRecord ; LocalState11011LRecord ] . 
GeneratePruvendoRecord LocalState1101L LocalStateFields1101I . 
Opaque LocalState1101LRecord . 



Inductive LocalStateFields000I := | ??0000 | ??0001 . 
Definition LocalState000L := [ LocalState0000LRecord ; LocalState0001LRecord ] . 
GeneratePruvendoRecord LocalState000L LocalStateFields000I . 
Opaque LocalState000LRecord . 

Inductive LocalStateFields001I := | ??0010 | ??0011 . 
Definition LocalState001L := [ LocalState0010LRecord ; LocalState0011LRecord ] . 
GeneratePruvendoRecord LocalState001L LocalStateFields001I . 
Opaque LocalState001LRecord . 

Inductive LocalStateFields010I := | ??0100 | ??0101 . 
Definition LocalState010L := [ LocalState0100LRecord ; LocalState0101LRecord ] . 
GeneratePruvendoRecord LocalState010L LocalStateFields010I . 
Opaque LocalState010LRecord . 

Inductive LocalStateFields011I := | ??0110 | ??0111 . 
Definition LocalState011L := [ LocalState0110LRecord ; LocalState0111LRecord ] . 
GeneratePruvendoRecord LocalState011L LocalStateFields011I . 
Opaque LocalState011LRecord . 

Inductive LocalStateFields100I := | ??1000 | ??1001 . 
Definition LocalState100L := [ LocalState1000LRecord ; LocalState1001LRecord ] . 
GeneratePruvendoRecord LocalState100L LocalStateFields100I . 
Opaque LocalState100LRecord . 

Inductive LocalStateFields101I := | ??1010 | ??1011 . 
Definition LocalState101L := [ LocalState1010LRecord ; LocalState1011LRecord ] . 
GeneratePruvendoRecord LocalState101L LocalStateFields101I . 
Opaque LocalState101LRecord . 

Inductive LocalStateFields110I := | ??1100 | ??1101 . 
Definition LocalState110L := [ LocalState1100LRecord ; LocalState1101LRecord ] . 
GeneratePruvendoRecord LocalState110L LocalStateFields110I . 
Opaque LocalState110LRecord . 



Inductive LocalStateFields00I := | ??000 | ??001 . 
Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
GeneratePruvendoRecord LocalState00L LocalStateFields00I . 
Opaque LocalState00LRecord . 

Inductive LocalStateFields01I := | ??010 | ??011 . 
Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
GeneratePruvendoRecord LocalState01L LocalStateFields01I . 
Opaque LocalState01LRecord . 

Inductive LocalStateFields10I := | ??100 | ??101 . 
Definition LocalState10L := [ LocalState100LRecord ; LocalState101LRecord ] . 
GeneratePruvendoRecord LocalState10L LocalStateFields10I . 
Opaque LocalState10LRecord . 



Inductive LocalStateFields0I := | ??00 | ??01 . 
Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
GeneratePruvendoRecord LocalState0L LocalStateFields0I . 
Opaque LocalState0LRecord . 

Inductive LocalStateFields1I := | ??10 | ??11 . 
Definition LocalState1L := [ LocalState10LRecord ; LocalState110LRecord ] . 
GeneratePruvendoRecord LocalState1L LocalStateFields1I . 
Opaque LocalState1LRecord . 



Inductive LocalStateFieldsI := | ??0 | ??1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState1LRecord ] . 
GeneratePruvendoRecord LocalStateL LocalStateFieldsI . 
Opaque LocalStateLRecord . 
 
  
(* 2 *) Definition LedgerL : list Type := 
 [ ( DPriceLRecord ) : Type ; 
 ( DPriceLRecord ) : Type ; 
 ( VMStateLRecord ) : Type ; 
 ( MessagesAndEventsLRecord ) : Type ; 
 ( MessagesAndEventsLRecord ) : Type ; 
 ( LocalStateLRecord ) : Type ; 
 ( LocalStateLRecord ) : Type ] .

Elpi GeneratePruvendoRecord LedgerL LedgerFieldsI .
(***************************************)

Transparent LocalState00000LRecord LocalState00001LRecord LocalState00010LRecord LocalState00011LRecord LocalState00100LRecord LocalState00101LRecord LocalState00110LRecord LocalState00111LRecord LocalState01000LRecord LocalState01001LRecord LocalState01010LRecord LocalState01011LRecord LocalState01100LRecord LocalState01101LRecord LocalState01110LRecord LocalState01111LRecord LocalState10000LRecord LocalState10001LRecord LocalState10010LRecord LocalState10011LRecord LocalState10100LRecord LocalState10101LRecord LocalState10110LRecord LocalState10111LRecord LocalState11000LRecord LocalState11001LRecord LocalState11010LRecord LocalState11011LRecord LocalState0000LRecord LocalState0001LRecord LocalState0010LRecord LocalState0011LRecord LocalState0100LRecord LocalState0101LRecord LocalState0110LRecord LocalState0111LRecord LocalState1000LRecord LocalState1001LRecord LocalState1010LRecord LocalState1011LRecord LocalState1100LRecord LocalState1101LRecord LocalState000LRecord LocalState001LRecord LocalState010LRecord LocalState011LRecord LocalState100LRecord LocalState101LRecord LocalState110LRecord LocalState00LRecord LocalState01LRecord LocalState10LRecord LocalState0LRecord LocalState1LRecord LocalStateLRecord  .

Transparent MessagesAndEventsLRecord .
Transparent DPriceLRecord .
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

Definition VMState_IsCommittedEmbedded := VMStateLEmbeddedType VMState_??_IsCommitted.
Definition MainCopySameType : field_type  Ledger_MainState = field_type Ledger_MainStateCopy := eq_refl.
Definition MessagesCopySameType : field_type  Ledger_MessagesState = field_type Ledger_MessagesStateCopy := eq_refl.

         
Obligation Tactic := idtac.

#[global, program] Instance LocalStateField00000 : LocalStateField ( StateInitLRecord * XUInteger256 ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00000). 
 eapply (LocalState00000LEmbeddedType ??000001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00000). 
 eapply (LocalState00000LEmbeddedType ??000000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00000 : typeclass_instances. 
 #[global, program] Instance LocalStateField00001 : LocalStateField cell.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00001). 
 eapply (LocalState00001LEmbeddedType ??000011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00001). 
 eapply (LocalState00001LEmbeddedType ??000010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00001 : typeclass_instances. 
 #[global, program] Instance LocalStateField00010 : LocalStateField StateInitLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00010). 
 eapply (LocalState00010LEmbeddedType ??000101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00010). 
 eapply (LocalState00010LEmbeddedType ??000100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00010 : typeclass_instances. 
 #[global, program] Instance LocalStateField00011 : LocalStateField XBool.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00011). 
 eapply (LocalState00011LEmbeddedType ??000111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00011). 
 eapply (LocalState00011LEmbeddedType ??000110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00011 : typeclass_instances. 
 #[global, program] Instance LocalStateField00100 : LocalStateField ( XMaybe XUInteger128 ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00100). 
 eapply (LocalState00100LEmbeddedType ??001001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00100). 
 eapply (LocalState00100LEmbeddedType ??001000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00100 : typeclass_instances. 
 #[global, program] Instance LocalStateField00101 : LocalStateField XUInteger.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00101). 
 eapply (LocalState00101LEmbeddedType ??001011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00101). 
 eapply (LocalState00101LEmbeddedType ??001010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00101 : typeclass_instances. 
 #[global, program] Instance LocalStateField00110 : LocalStateField ( XBool * XBool * XUInteger128 ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00110). 
 eapply (LocalState00110LEmbeddedType ??001101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00110). 
 eapply (LocalState00110LEmbeddedType ??001100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00110 : typeclass_instances. 
 #[global, program] Instance LocalStateField00111 : LocalStateField XUInteger128.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00111). 
 eapply (LocalState00111LEmbeddedType ??001111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00111). 
 eapply (LocalState00111LEmbeddedType ??001110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField00111 : typeclass_instances. 
 #[global, program] Instance LocalStateField01000 : LocalStateField ( XMaybe (XUInteger * OrderInfoLRecord) ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01000). 
 eapply (LocalState01000LEmbeddedType ??010001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01000). 
 eapply (LocalState01000LEmbeddedType ??010000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01000 : typeclass_instances. 
 #[global, program] Instance LocalStateField01001 : LocalStateField OrderRetLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01001). 
 eapply (LocalState01001LEmbeddedType ??010011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01001). 
 eapply (LocalState01001LEmbeddedType ??010010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01001 : typeclass_instances. 
 #[global, program] Instance LocalStateField01010 : LocalStateField address.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01010). 
 eapply (LocalState01010LEmbeddedType ??010101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01010). 
 eapply (LocalState01010LEmbeddedType ??010100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01010 : typeclass_instances. 
 #[global, program] Instance LocalStateField01011 : LocalStateField address (* IFlexNotifyPtrLRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01011). 
 eapply (LocalState01011LEmbeddedType ??010111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01011). 
 eapply (LocalState01011LEmbeddedType ??010110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01011 : typeclass_instances. 
 #[global, program] Instance LocalStateField01100 : LocalStateField TonsConfigLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01100). 
 eapply (LocalState01100LEmbeddedType ??011001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01100). 
 eapply (LocalState01100LEmbeddedType ??011000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01100 : typeclass_instances. 
 #[global, program] Instance LocalStateField01101 : LocalStateField ( XMaybe OrderRetLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01101). 
 eapply (LocalState01101LEmbeddedType ??011011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01101). 
 eapply (LocalState01101LEmbeddedType ??011010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01101 : typeclass_instances. 
 #[global, program] Instance LocalStateField01110 : LocalStateField process_retLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01110). 
 eapply (LocalState01110LEmbeddedType ??011101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01110). 
 eapply (LocalState01110LEmbeddedType ??011100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01110 : typeclass_instances. 
 #[global, program] Instance LocalStateField01111 : LocalStateField dealerLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01111). 
 eapply (LocalState01111LEmbeddedType ??011111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01111). 
 eapply (LocalState01111LEmbeddedType ??011110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField01111 : typeclass_instances. 
 #[global, program] Instance LocalStateField10000 : LocalStateField address (* ITONTokenWalletPtrLRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10000). 
 eapply (LocalState10000LEmbeddedType ??100001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10000). 
 eapply (LocalState10000LEmbeddedType ??100000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10000 : typeclass_instances. 
 #[global, program] Instance LocalStateField10001 : LocalStateField Grams .
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10001). 
 eapply (LocalState10001LEmbeddedType ??100011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10001).
 compute. 
 eapply (LocalState10001LEmbeddedType ??100010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10001 : typeclass_instances. 
 #[global, program] Instance LocalStateField10010 : LocalStateField OrderInfoLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10010). 
 eapply (LocalState10010LEmbeddedType ??100101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10010). 
 eapply (LocalState10010LEmbeddedType ??100100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10010 : typeclass_instances. 
 #[global, program] Instance LocalStateField10011 : LocalStateField addr_std_fixed.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10011). 
 eapply (LocalState10011LEmbeddedType ??100111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10011). 
 eapply (LocalState10011LEmbeddedType ??100110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10011 : typeclass_instances. 
 #[global, program] Instance LocalStateField10100 : LocalStateField DetailsInfoLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??1010). 
 eapply TransEmbedded. eapply (_ ??10100). 
 eapply (LocalState10100LEmbeddedType ??101001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??1010). 
 eapply TransEmbedded. eapply (_ ??10100). 
 eapply (LocalState10100LEmbeddedType ??101000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10100 : typeclass_instances. 
 #[global, program] Instance LocalStateField10101 : LocalStateField ( XHMap XUInteger OrderInfoLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??1010). 
 eapply TransEmbedded. eapply (_ ??10101). 
 eapply (LocalState10101LEmbeddedType ??101011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??1010). 
 eapply TransEmbedded. eapply (_ ??10101). 
 eapply (LocalState10101LEmbeddedType ??101010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10101 : typeclass_instances. 
 #[global, program] Instance LocalStateField10110 : LocalStateField XUInteger.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??1011). 
 eapply TransEmbedded. eapply (_ ??10110). 
 eapply (LocalState10110LEmbeddedType ??101101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??1011). 
 eapply TransEmbedded. eapply (_ ??10110). 
 eapply (LocalState10110LEmbeddedType ??101100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10110 : typeclass_instances. 
 #[global, program] Instance LocalStateField10111 : LocalStateField XUInteger256.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??1011). 
 eapply TransEmbedded. eapply (_ ??10111). 
 eapply (LocalState10111LEmbeddedType ??101111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??10). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??1011). 
 eapply TransEmbedded. eapply (_ ??10111). 
 eapply (LocalState10111LEmbeddedType ??101110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10111 : typeclass_instances. 
 #[global, program] Instance LocalStateField11000 : LocalStateField ( XMaybe address ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??11). 
 eapply TransEmbedded. eapply (_ ??1100). 
 eapply TransEmbedded. eapply (_ ??11000). 
 eapply (LocalState11000LEmbeddedType ??110001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??11). 
 eapply TransEmbedded. eapply (_ ??1100). 
 eapply TransEmbedded. eapply (_ ??11000). 
 eapply (LocalState11000LEmbeddedType ??110000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField11000 : typeclass_instances. 
 #[global, program] Instance LocalStateField11001 : LocalStateField TokenWalletClassTypesModule.DTONTokenWalletInternalLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??11). 
 eapply TransEmbedded. eapply (_ ??1100). 
 eapply TransEmbedded. eapply (_ ??11001). 
 eapply (LocalState11001LEmbeddedType ??110011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??11). 
 eapply TransEmbedded. eapply (_ ??1100). 
 eapply TransEmbedded. eapply (_ ??11001). 
 eapply (LocalState11001LEmbeddedType ??110010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField11001 : typeclass_instances. 
 #[global, program] Instance LocalStateField11010 : LocalStateField SellArgsLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??11). 
 eapply TransEmbedded. eapply (_ ??1101). 
 eapply TransEmbedded. eapply (_ ??11010). 
 eapply (LocalState11010LEmbeddedType ??110101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??11). 
 eapply TransEmbedded. eapply (_ ??1101). 
 eapply TransEmbedded. eapply (_ ??11010). 
 eapply (LocalState11010LEmbeddedType ??110100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField11010 : typeclass_instances. 
 #[global, program] Instance LocalStateField11011 : LocalStateField XUInteger.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??11). 
 eapply TransEmbedded. eapply (_ ??1101). 
 eapply TransEmbedded. eapply (_ ??11011). 
 eapply (LocalState11011LEmbeddedType ??110111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??11). 
 eapply TransEmbedded. eapply (_ ??1101). 
 eapply TransEmbedded. eapply (_ ??11011). 
 eapply (LocalState11011LEmbeddedType ??110110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField11011 : typeclass_instances. 

Definition GlobalParamsEmbedded := MessagesAndEventsLEmbeddedType _GlobalParams.
Definition OutgoingMessageParamsEmbedded := MessagesAndEventsLEmbeddedType _OutgoingMessageParams.

End Ledger .
