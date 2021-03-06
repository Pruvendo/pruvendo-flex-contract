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
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonTypes. 

Require Import FlexClient.ClassTypes.
Require TradingPair.ClassTypes.
Require XchgPair.ClassTypes.
Require TONTokenWallet.ClassTypes.
Require Price.ClassTypes.
Require PriceXchg.ClassTypes.
Require Flex.ClassTypes.

Require Import FlexClient.Interface.
Require Import TradingPair.Interface.
Require Import Contracts.FlexClient.Interface.
Require Import Contracts.XchgPair.Interface.
Require Import Contracts.TONTokenWallet.Interface.
Require Import Contracts.PriceXchg.Interface.
Require Import Contracts.Price.Interface.
Require Import Contracts.Flex.Interface.


Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Inductive MessagesAndEventsFields := | _OutgoingMessages_FlexClient 
| _OutgoingMessages_ITradingPair 
| _OutgoingMessages_IXchgPair 
| _OutgoingMessages_ITONTokenWallet 
| _OutgoingMessages_IPriceXchg 
| _OutgoingMessages_IFlex 
| _OutgoingMessages_IPrice 
| _GlobalParams
| _OutgoingMessageParams
| _EmittedEvents | _MessagesLog.

Inductive LedgerFieldsI := | _Contract | _ContractCopy | _VMState | _MessagesAndEvents | _MessagesAndEventsCopy | _LocalState | _LocalStateCopy .

Definition ContractFields := DFlexClientFields.

Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 

Module FlexClientPublicInterfaceModule := FlexClient.Interface.PublicInterface xt sm.

Module Import BasicTypesClass := Project.CommonTypes.Types xt sm.
Module Export BasicTypesModule := BasicTypes xt sm.
Module Export VMStateModule := VMStateModule xt sm. 

Module FlexClientClassTypesModule := FlexClient.ClassTypes.ClassTypes xt sm .
Module PriceClassTypesModule := Price.ClassTypes.ClassTypes xt sm .
Module PriceXchgClassTypesModule := PriceXchg.ClassTypes.ClassTypes xt sm .
Module TradingPairClassTypesModule := TradingPair.ClassTypes.ClassTypes xt sm .
Module XchgPairClassTypesModule := XchgPair.ClassTypes.ClassTypes xt sm .
Module TokenWalletClassTypesModule := TONTokenWallet.ClassTypes.ClassTypes xt sm .
Module FlexClassTypesModule := Flex.ClassTypes.ClassTypes xt sm .

Module TradingPairInterfaceModule := TradingPair.Interface.PublicInterface xt sm .
Module XchgPairInterfaceModule := XchgPair.Interface.PublicInterface xt sm .
Module TONTokenWalletInterfaceModule := TONTokenWallet.Interface.PublicInterface xt sm .
Module PriceXchgInterfaceModule := PriceXchg.Interface.PublicInterface xt sm .
Module PriceInterfaceModule := Price.Interface.PublicInterface xt sm .
Module FlexInterfaceModule := Flex.Interface.PublicInterface xt sm .

Import xt.

Definition MessagesAndEventsL : list Type := 
 [ ( XQueue (OutgoingMessage FlexClientPublicInterfaceModule.IFlexClient) ) : Type ; 
 ( XHMap address (XQueue (OutgoingMessage TradingPairInterfaceModule.ITradingPair )) ) : Type ;
 ( XHMap address (XQueue (OutgoingMessage XchgPairInterfaceModule.IXchgPair )) ) : Type ;
 ( XHMap address (XQueue (OutgoingMessage TONTokenWalletInterfaceModule.ITONTokenWallet )) ) : Type ;
 ( XHMap address (XQueue (OutgoingMessage PriceXchgInterfaceModule.IPriceXchg )) ) : Type ;
 ( XHMap address (XQueue (OutgoingMessage FlexInterfaceModule.IFlex )) ) : Type ;
 ( XHMap address (XQueue (OutgoingMessage PriceInterfaceModule.IPrice )) ) : Type ;
  GlobalParamsLRecord: Type ;
  OutgoingMessageParamsLRecord: Type ;
 ( XList TVMEvent ) : Type ; 
 ( XString ) : Type ] .
 GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
Opaque MessagesAndEventsLRecord .
 
Definition ContractLRecord := FlexClientClassTypesModule.DFlexClientLRecord.
Definition ContractLEmbeddedType := FlexClientClassTypesModule.DFlexClientLEmbeddedType.

Inductive LocalStateFields00000I := | ??000000 | ??000001 . 
Definition LocalState00000L := [ ( XHMap (string*nat) XUInteger128 ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00000L LocalStateFields00000I . 
Opaque LocalState00000LRecord . 

Inductive LocalStateFields00001I := | ??000010 | ??000011 . 
Definition LocalState00001L := [ ( XHMap (string*nat) address ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00001L LocalStateFields00001I . 
Opaque LocalState00001LRecord . 

Inductive LocalStateFields00010I := | ??000100 | ??000101 . 
Definition LocalState00010L := [ ( XHMap (string*nat) TradingPairClassTypesModule.DTradingPairLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00010L LocalStateFields00010I . 
Opaque LocalState00010LRecord . 

Inductive LocalStateFields00011I := | ??000110 | ??000111 . 
Definition LocalState00011L := [ ( XHMap (string*nat) TokenWalletClassTypesModule.DTONTokenWalletInternalLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00011L LocalStateFields00011I . 
Opaque LocalState00011LRecord . 

Inductive LocalStateFields00100I := | ??001000 | ??001001 . 
Definition LocalState00100L := [ ( XHMap (string*nat) XchgPairClassTypesModule.DXchgPairLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00100L LocalStateFields00100I . 
Opaque LocalState00100LRecord . 

Inductive LocalStateFields00101I := | ??001010 | ??001011 . 
Definition LocalState00101L := [ ( XHMap (string*nat) cell_ ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00101L LocalStateFields00101I . 
Opaque LocalState00101LRecord . 

Inductive LocalStateFields00110I := | ??001100 | ??001101 . 
Definition LocalState00110L := [ ( XHMap (string*nat) PriceClassTypesModule.SellArgsLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00110L LocalStateFields00110I . 
Opaque LocalState00110LRecord . 

Inductive LocalStateFields00111I := | ??001110 | ??001111 . 
Definition LocalState00111L := [ ( XHMap (string*nat) BasicTypesClass.Tip3ConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState00111L LocalStateFields00111I . 
Opaque LocalState00111LRecord . 

Inductive LocalStateFields01000I := | ??010000 | ??010001 . 
Definition LocalState01000L := [ ( XHMap (string*nat) BasicTypesClass.TonsConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01000L LocalStateFields01000I . 
Opaque LocalState01000LRecord . 

Inductive LocalStateFields01001I := | ??010010 | ??010011 . 
Definition LocalState01001L := [ ( XHMap (string*nat) BasicTypesClass.StateInitLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01001L LocalStateFields01001I . 
Opaque LocalState01001LRecord . 

Inductive LocalStateFields01010I := | ??010100 | ??010101 . 
Definition LocalState01010L := [ ( XHMap (string*nat) PriceXchgClassTypesModule.PayloadArgsLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01010L LocalStateFields01010I . 
Opaque LocalState01010LRecord . 

Inductive LocalStateFields01011I := | ??010110 | ??010111 . 
Definition LocalState01011L := [ ( XHMap (string*nat) XUInteger256 ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01011L LocalStateFields01011I . 
Opaque LocalState01011LRecord . 

Inductive LocalStateFields01100I := | ??011000 | ??011001 . 
Definition LocalState01100L := [ ( XHMap (string*nat) XBool ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01100L LocalStateFields01100I . 
Opaque LocalState01100LRecord . 

Inductive LocalStateFields01101I := | ??011010 | ??011011 . 
Definition LocalState01101L := [ ( XHMap (string*nat) XUInteger ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01101L LocalStateFields01101I . 
Opaque LocalState01101LRecord . 

Inductive LocalStateFields01110I := | ??011100 | ??011101 . 
Definition LocalState01110L := [ ( XHMap (string*nat) ( BasicTypesClass.StateInitLRecord * address * XUInteger256 ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01110L LocalStateFields01110I . 
Opaque LocalState01110LRecord . 

Inductive LocalStateFields01111I := | ??011110 | ??011111 . 
Definition LocalState01111L := [ ( XHMap (string*nat) PriceClassTypesModule.DPriceLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState01111L LocalStateFields01111I . 
Opaque LocalState01111LRecord . 

Inductive LocalStateFields10000I := | ??100000 | ??100001 . 
Definition LocalState10000L := [ ( XHMap (string*nat) PriceXchgClassTypesModule.DPriceXchgLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState10000L LocalStateFields10000I . 
Opaque LocalState10000LRecord . 

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

Inductive LocalStateFields00I := | ??000 | ??001 . 
Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
GeneratePruvendoRecord LocalState00L LocalStateFields00I . 
Opaque LocalState00LRecord . 

Inductive LocalStateFields01I := | ??010 | ??011 . 
Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
GeneratePruvendoRecord LocalState01L LocalStateFields01I . 
Opaque LocalState01LRecord . 

Inductive LocalStateFields0I := | ??00 | ??01 . 
Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
GeneratePruvendoRecord LocalState0L LocalStateFields0I . 
Opaque LocalState0LRecord . 

Inductive LocalStateFieldsI := | ??0 | ??1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState10000LRecord ] . 
GeneratePruvendoRecord LocalStateL LocalStateFieldsI . 
Opaque LocalStateLRecord . 

Definition LedgerL : list Type := 
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
Transparent LocalState00000LRecord LocalState00001LRecord LocalState00010LRecord LocalState00011LRecord LocalState00100LRecord LocalState00101LRecord LocalState00110LRecord LocalState00111LRecord LocalState01000LRecord LocalState01001LRecord LocalState01010LRecord LocalState01011LRecord LocalState01100LRecord LocalState01101LRecord LocalState01110LRecord LocalState01111LRecord LocalState10000LRecord LocalState0000LRecord LocalState0001LRecord LocalState0010LRecord LocalState0011LRecord LocalState0100LRecord LocalState0101LRecord LocalState0110LRecord LocalState0111LRecord LocalState10000LRecord LocalState000LRecord LocalState001LRecord LocalState010LRecord LocalState011LRecord LocalState00LRecord LocalState01LRecord LocalState0LRecord LocalStateLRecord .
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

#[global, program] Instance LocalStateField00000 : LocalStateField XUInteger128.
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
 #[global, program] Instance LocalStateField00001 : LocalStateField address.
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
 #[global, program] Instance LocalStateField00010 : LocalStateField TradingPairClassTypesModule.DTradingPairLRecord.
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
 #[global, program] Instance LocalStateField00011 : LocalStateField TokenWalletClassTypesModule.DTONTokenWalletInternalLRecord.
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
 #[global, program] Instance LocalStateField00100 : LocalStateField XchgPairClassTypesModule.DXchgPairLRecord.
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
 #[global, program] Instance LocalStateField00101 : LocalStateField cell.
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
 #[global, program] Instance LocalStateField00110 : LocalStateField PriceClassTypesModule.SellArgsLRecord.
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
 #[global, program] Instance LocalStateField00111 : LocalStateField BasicTypesClass.Tip3ConfigLRecord.
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
 #[global, program] Instance LocalStateField01000 : LocalStateField BasicTypesClass.TonsConfigLRecord.
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
 #[global, program] Instance LocalStateField01001 : LocalStateField BasicTypesClass.StateInitLRecord.
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
 #[global, program] Instance LocalStateField01010 : LocalStateField PriceXchgClassTypesModule.PayloadArgsLRecord.
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
 #[global, program] Instance LocalStateField01011 : LocalStateField XUInteger256.
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
 #[global, program] Instance LocalStateField01100 : LocalStateField XBool.
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
 #[global, program] Instance LocalStateField01101 : LocalStateField XUInteger.
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
 #[global, program] Instance LocalStateField01110 : LocalStateField ( BasicTypesClass.StateInitLRecord * address * XUInteger256 ).
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
 #[global, program] Instance LocalStateField01111 : LocalStateField PriceClassTypesModule.DPriceLRecord.
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
 #[global, program] Instance LocalStateField10000 : LocalStateField PriceXchgClassTypesModule.DPriceXchgLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply (LocalState10000LEmbeddedType ??100001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply (LocalState10000LEmbeddedType ??100000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField10000 : typeclass_instances. 

(* Definition LocalStateField_XUInteger := LocalStateField00000 .
Definition LocalStateField_XBool := LocalStateField01100 .
Definition LocalStateField_cell := LocalStateField00001 . *)

Definition GlobalParamsEmbedded := MessagesAndEventsLEmbeddedType _GlobalParams.
Definition OutgoingMessageParamsEmbedded := MessagesAndEventsLEmbeddedType _OutgoingMessageParams.


End Ledger .

