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

Require Import Flex.ClassTypes.
Require XchgPair.ClassTypes.
Require TradingPair.ClassTypes.
Require TONTokenWallet.ClassTypes.
Require Wrapper.ClassTypes.

Require Import Flex.Interface.
Require XchgPair.Interface.
Require TradingPair.Interface.
Require TONTokenWallet.Interface.
Require Wrapper.Interface.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Inductive MessagesAndEventsFields := | _OutgoingMessages_IListingAnswer
                                     | _OutgoingMessages_IXchgPair
                                     | _OutgoingMessages_ITradingPair
                                     | _OutgoingMessages_IWrapper
                                     | _OutgoingMessages_ITONTokenWallet
                                     | _EmittedEvents 
                                     | _GlobalParams
                                     | _OutgoingMessageParams
                                     | _MessagesLog.

Inductive LedgerFieldsI := | _Contract 
                           | _ContractCopy 
                           | _VMState 
                           | _MessagesAndEvents 
                           | _MessagesAndEventsCopy 
                           | _LocalState 
                           | _LocalStateCopy .

Definition ContractFields := DFlexFields.  

Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 

Module Export BasicTypesModule := BasicTypes xt sm.
Module Export VMStateModule := VMStateModule xt sm. 

Module Export ClassTypesModule := Flex.ClassTypes.ClassTypes xt sm .
Module TradingPairClassTypesModule := TradingPair.ClassTypes.ClassTypes xt sm .
Module XchgPairClassTypesModule := XchgPair.ClassTypes.ClassTypes xt sm .
Module TONTonkenWalletClassTypesModule := TONTokenWallet.ClassTypes.ClassTypes xt sm.
Module WrapperClassTypesModule := Wrapper.ClassTypes.ClassTypes xt sm.

Module FlexPublicInterfaceModule := Flex.Interface.PublicInterface xt sm.
Module TradingPairInterfaceModule := TradingPair.Interface.PublicInterface xt sm .
Module XchgPairInterfaceModule := XchgPair.Interface.PublicInterface xt sm .
Module TONTonkenWalletInterfaceModule := TONTokenWallet.Interface.PublicInterface xt sm.
Module WrapperInterfaceModule := Wrapper.Interface.PublicInterface xt sm.

Import xt. 

Definition MessagesAndEventsL : list Type := 
 [ ( XHMap address (XQueue (OutgoingMessage FlexPublicInterfaceModule.IListingAnswer )) ) : Type ;
   ( XHMap address (XQueue (OutgoingMessage XchgPairInterfaceModule.IXchgPair )) ) : Type ;
   ( XHMap address (XQueue (OutgoingMessage TradingPairInterfaceModule.ITradingPair )) ) : Type ;
   ( XHMap address (XQueue (OutgoingMessage WrapperInterfaceModule.IWrapper )) ) : Type ;
   ( XHMap address (XQueue (OutgoingMessage TONTonkenWalletInterfaceModule.ITONTokenWallet )) ) : Type ;
   ( XList TVMEvent ) : Type ; 
   GlobalParamsLRecord: Type ;
   OutgoingMessageParamsLRecord: Type ;
   XList XString : Type ] .
   
GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
Opaque MessagesAndEventsLRecord .
 
Definition ContractLRecord := DFlexLRecord . 
Definition ContractLEmbeddedType := DFlexLEmbeddedType.


Inductive LocalStateFields000000I := | ??0000000 | ??0000001 . 
Definition LocalState000000L := [ ( XHMap (string*nat) ( StateInitLRecord * XUInteger256 ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState000000L LocalStateFields000000I . 
Opaque LocalState000000LRecord . 

Inductive LocalStateFields000001I := | ??0000010 | ??0000011 . 
Definition LocalState000001L := [ ( XHMap (string*nat) cell_ ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState000001L LocalStateFields000001I . 
Opaque LocalState000001LRecord . 

Inductive LocalStateFields000010I := | ??0000100 | ??0000101 . 
Definition LocalState000010L := [ ( XHMap (string*nat) StateInitLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState000010L LocalStateFields000010I . 
Opaque LocalState000010LRecord . 

Inductive LocalStateFields000011I := | ??0000110 | ??0000111 . 
Definition LocalState000011L := [ ( XHMap (string*nat) XUInteger256 ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState000011L LocalStateFields000011I . 
Opaque LocalState000011LRecord . 

Inductive LocalStateFields000100I := | ??0001000 | ??0001001 . 
Definition LocalState000100L := [ ( XHMap (string*nat) ( XMaybe address ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState000100L LocalStateFields000100I . 
Opaque LocalState000100LRecord . 

Inductive LocalStateFields000101I := | ??0001010 | ??0001011 . 
Definition LocalState000101L := [ ( XHMap (string*nat) TONTonkenWalletClassTypesModule.DTONTokenWalletExternalLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState000101L LocalStateFields000101I . 
Opaque LocalState000101LRecord . 

Inductive LocalStateFields000110I := | ??0001100 | ??0001101 . 
Definition LocalState000110L := [ ( XHMap (string*nat) TONTonkenWalletClassTypesModule.DTONTokenWalletInternalLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState000110L LocalStateFields000110I . 
Opaque LocalState000110LRecord . 

Inductive LocalStateFields000111I := | ??0001110 | ??0001111 . 
Definition LocalState000111L := [ ( XHMap (string*nat) TradingPairClassTypesModule.DTradingPairLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState000111L LocalStateFields000111I . 
Opaque LocalState000111LRecord . 

Inductive LocalStateFields001000I := | ??0010000 | ??0010001 . 
Definition LocalState001000L := [ ( XHMap (string*nat) ( address * ( XHMap XUInteger256 TradingPairListingRequestLRecord ) ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState001000L LocalStateFields001000I . 
Opaque LocalState001000LRecord . 

Inductive LocalStateFields001001I := | ??0010010 | ??0010011 . 
Definition LocalState001001L := [ ( XHMap (string*nat) ( XHMap XUInteger256 TradingPairListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState001001L LocalStateFields001001I . 
Opaque LocalState001001LRecord . 

Inductive LocalStateFields001010I := | ??0010100 | ??0010101 . 
Definition LocalState001010L := [ ( XHMap (string*nat) ( address * ( XHMap XUInteger256 XchgPairListingRequestLRecord ) ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState001010L LocalStateFields001010I . 
Opaque LocalState001010LRecord . 

Inductive LocalStateFields001011I := | ??0010110 | ??0010111 . 
Definition LocalState001011L := [ ( XHMap (string*nat) ( XHMap XUInteger256 XchgPairListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState001011L LocalStateFields001011I . 
Opaque LocalState001011LRecord . 

Inductive LocalStateFields001100I := | ??0011000 | ??0011001 . 
Definition LocalState001100L := [ ( XHMap (string*nat) ( address * ( XHMap XUInteger256 WrapperListingRequestLRecord ) ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState001100L LocalStateFields001100I . 
Opaque LocalState001100LRecord . 

Inductive LocalStateFields001101I := | ??0011010 | ??0011011 . 
Definition LocalState001101L := [ ( XHMap (string*nat) ( XHMap XUInteger256 WrapperListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState001101L LocalStateFields001101I . 
Opaque LocalState001101LRecord . 

Inductive LocalStateFields001110I := | ??0011100 | ??0011101 . 
Definition LocalState001110L := [ ( XHMap (string*nat) address ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState001110L LocalStateFields001110I . 
Opaque LocalState001110LRecord . 

Inductive LocalStateFields001111I := | ??0011110 | ??0011111 . 
Definition LocalState001111L := [ ( XHMap (string*nat) slice_ ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState001111L LocalStateFields001111I . 
Opaque LocalState001111LRecord . 

Inductive LocalStateFields010000I := | ??0100000 | ??0100001 . 
Definition LocalState010000L := [ ( XHMap (string*nat) XBool ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState010000L LocalStateFields010000I . 
Opaque LocalState010000LRecord . 

Inductive LocalStateFields010001I := | ??0100010 | ??0100011 .
Definition LocalState010001L := [ ( XHMap (string*nat) XchgPairClassTypesModule.DXchgPairLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState010001L LocalStateFields010001I . 
Opaque LocalState010001LRecord . 

Inductive LocalStateFields010010I := | ??0100100 | ??0100101 . 
Definition LocalState010010L := [ ( XHMap (string*nat) WrapperClassTypesModule.DWrapperLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState010010L LocalStateFields010010I . 
Opaque LocalState010010LRecord . 

Inductive LocalStateFields010011I := | ??0100110 | ??0100111 . 
Definition LocalState010011L := [ ( XHMap (string*nat) FlexDetailsLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState010011L LocalStateFields010011I . 
Opaque LocalState010011LRecord . 

Inductive LocalStateFields010100I := | ??0101000 | ??0101001 . 
Definition LocalState010100L := [ ( XHMap (string*nat) TonsConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState010100L LocalStateFields010100I . 
Opaque LocalState010100LRecord . 

Inductive LocalStateFields010101I := | ??0101010 | ??0101011 . 
Definition LocalState010101L := [ ( XHMap (string*nat) ListingConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState010101L LocalStateFields010101I . 
Opaque LocalState010101LRecord . 

Inductive LocalStateFields010110I := | ??0101100 | ??0101101 . 
Definition LocalState010110L := [ ( XHMap (string*nat) Tip3ConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState010110L LocalStateFields010110I . 
Opaque LocalState010110LRecord . 

Inductive LocalStateFields010111I := | ??0101110 | ??0101111 . 
Definition LocalState010111L := [ ( XHMap (string*nat) XUInteger8 ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState010111L LocalStateFields010111I . 
Opaque LocalState010111LRecord . 

Inductive LocalStateFields011000I := | ??0110000 | ??0110001 . 
Definition LocalState011000L := [ ( XHMap (string*nat) FlexOwnershipInfoLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState011000L LocalStateFields011000I . 
Opaque LocalState011000LRecord . 

Inductive LocalStateFields011001I := | ??0110010 | ??0110011 . 
Definition LocalState011001L := [ ( XHMap (string*nat) ( XHMap XUInteger WrapperListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState011001L LocalStateFields011001I . 
Opaque LocalState011001LRecord . 

Inductive LocalStateFields011010I := | ??0110100 | ??0110101 . 
Definition LocalState011010L := [ ( XHMap (string*nat) ( XHMap XUInteger TradingPairListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState011010L LocalStateFields011010I . 
Opaque LocalState011010LRecord . 

Inductive LocalStateFields011011I := | ??0110110 | ??0110111 . 
Definition LocalState011011L := [ ( XHMap (string*nat) ( XHMap XUInteger XchgPairListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState011011L LocalStateFields011011I . 
Opaque LocalState011011LRecord . 

Inductive LocalStateFields011100I := | ??0111000 | ??0111001 . 
Definition LocalState011100L := [ ( XHMap (string*nat) XUInteger ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState011100L LocalStateFields011100I . 
Opaque LocalState011100LRecord . 

Inductive LocalStateFields011101I := | ??0111010 | ??0111011 . 
Definition LocalState011101L := [ ( XHMap (string*nat) ( address * address (* IWrapperPtrLRecord *) ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState011101L LocalStateFields011101I . 
Opaque LocalState011101LRecord . 

Inductive LocalStateFields011110I := | ??0111100 | ??0111101 . 
Definition LocalState011110L := [ ( XHMap (string*nat) address (* ITONTokenWalletPtrLRecord *) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState011110L LocalStateFields011110I . 
Opaque LocalState011110LRecord . 

Inductive LocalStateFields011111I := | ??0111110 | ??0111111 . 
Definition LocalState011111L := [ ( XHMap (string*nat) ( XMaybe WrapperListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState011111L LocalStateFields011111I . 
Opaque LocalState011111LRecord . 

Inductive LocalStateFields100000I := | ??1000000 | ??1000001 . 
Definition LocalState100000L := [ ( XHMap (string*nat) ( XMaybe TradingPairListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState100000L LocalStateFields100000I . 
Opaque LocalState100000LRecord . 

Inductive LocalStateFields100001I := | ??1000010 | ??1000011 . 
Definition LocalState100001L := [ ( XHMap (string*nat) ( XMaybe XchgPairListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState100001L LocalStateFields100001I . 
Opaque LocalState100001LRecord . 

Inductive LocalStateFields100010I := | ??1000100 | ??1000101 . 
Definition LocalState100010L := [ ( XHMap (string*nat) ( XMaybe WrapperListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState100010L LocalStateFields100010I . 
Opaque LocalState100010LRecord . 

Inductive LocalStateFields100011I := | ??1000110 | ??1000111 . 
Definition LocalState100011L := [ ( XHMap (string*nat) ( XMaybe TradingPairListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState100011L LocalStateFields100011I . 
Opaque LocalState100011LRecord . 

Inductive LocalStateFields100100I := | ??1001000 | ??1001001 . 
Definition LocalState100100L := [ ( XHMap (string*nat) ( XMaybe XchgPairListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState100100L LocalStateFields100100I . 
Opaque LocalState100100LRecord . 

Inductive LocalStateFields100101I := | ??1001010 | ??1001011 . 
Definition LocalState100101L := [ ( XHMap (string*nat) WrapperListingRequestWithPubkeyLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState100101L LocalStateFields100101I . 
Opaque LocalState100101LRecord . 

Inductive LocalStateFields100110I := | ??1001100 | ??1001101 . 
Definition LocalState100110L := [ ( XHMap (string*nat) TradingPairListingRequestWithPubkeyLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState100110L LocalStateFields100110I . 
Opaque LocalState100110LRecord . 

Inductive LocalStateFields100111I := | ??1001110 | ??1001111 . 
Definition LocalState100111L := [ ( XHMap (string*nat) XchgPairListingRequestWithPubkeyLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState100111L LocalStateFields100111I . 
Opaque LocalState100111LRecord . 

Inductive LocalStateFields101000I := | ??1010000 | ??1010001 . 
Definition LocalState101000L := [ ( XHMap (string*nat) WrapperListingRequestLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState101000L LocalStateFields101000I . 
Opaque LocalState101000LRecord . 

Inductive LocalStateFields101001I := | ??1010010 | ??1010011 . 
Definition LocalState101001L := [ ( XHMap (string*nat) TradingPairListingRequestLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState101001L LocalStateFields101001I . 
Opaque LocalState101001LRecord . 

Inductive LocalStateFields101010I := | ??1010100 | ??1010101 . 
Definition LocalState101010L := [ ( XHMap (string*nat) XchgPairListingRequestLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
GeneratePruvendoRecord LocalState101010L LocalStateFields101010I . 
Opaque LocalState101010LRecord . 


Inductive LocalStateFields00000I := | ??000000 | ??000001 . 
Definition LocalState00000L := [ LocalState000000LRecord ; LocalState000001LRecord ] . 
GeneratePruvendoRecord LocalState00000L LocalStateFields00000I . 
Opaque LocalState00000LRecord . 

Inductive LocalStateFields00001I := | ??000010 | ??000011 . 
Definition LocalState00001L := [ LocalState000010LRecord ; LocalState000011LRecord ] . 
GeneratePruvendoRecord LocalState00001L LocalStateFields00001I . 
Opaque LocalState00001LRecord . 

Inductive LocalStateFields00010I := | ??000100 | ??000101 . 
Definition LocalState00010L := [ LocalState000100LRecord ; LocalState000101LRecord ] . 
GeneratePruvendoRecord LocalState00010L LocalStateFields00010I . 
Opaque LocalState00010LRecord . 

Inductive LocalStateFields00011I := | ??000110 | ??000111 . 
Definition LocalState00011L := [ LocalState000110LRecord ; LocalState000111LRecord ] . 
GeneratePruvendoRecord LocalState00011L LocalStateFields00011I . 
Opaque LocalState00011LRecord . 

Inductive LocalStateFields00100I := | ??001000 | ??001001 . 
Definition LocalState00100L := [ LocalState001000LRecord ; LocalState001001LRecord ] . 
GeneratePruvendoRecord LocalState00100L LocalStateFields00100I . 
Opaque LocalState00100LRecord . 

Inductive LocalStateFields00101I := | ??001010 | ??001011 . 
Definition LocalState00101L := [ LocalState001010LRecord ; LocalState001011LRecord ] . 
GeneratePruvendoRecord LocalState00101L LocalStateFields00101I . 
Opaque LocalState00101LRecord . 

Inductive LocalStateFields00110I := | ??001100 | ??001101 . 
Definition LocalState00110L := [ LocalState001100LRecord ; LocalState001101LRecord ] . 
GeneratePruvendoRecord LocalState00110L LocalStateFields00110I . 
Opaque LocalState00110LRecord . 

Inductive LocalStateFields00111I := | ??001110 | ??001111 . 
Definition LocalState00111L := [ LocalState001110LRecord ; LocalState001111LRecord ] . 
GeneratePruvendoRecord LocalState00111L LocalStateFields00111I . 
Opaque LocalState00111LRecord . 

Inductive LocalStateFields01000I := | ??010000 | ??010001 . 
Definition LocalState01000L := [ LocalState010000LRecord ; LocalState010001LRecord ] . 
GeneratePruvendoRecord LocalState01000L LocalStateFields01000I . 
Opaque LocalState01000LRecord . 

Inductive LocalStateFields01001I := | ??010010 | ??010011 . 
Definition LocalState01001L := [ LocalState010010LRecord ; LocalState010011LRecord ] . 
GeneratePruvendoRecord LocalState01001L LocalStateFields01001I . 
Opaque LocalState01001LRecord . 

Inductive LocalStateFields01010I := | ??010100 | ??010101 . 
Definition LocalState01010L := [ LocalState010100LRecord ; LocalState010101LRecord ] . 
GeneratePruvendoRecord LocalState01010L LocalStateFields01010I . 
Opaque LocalState01010LRecord . 

Inductive LocalStateFields01011I := | ??010110 | ??010111 . 
Definition LocalState01011L := [ LocalState010110LRecord ; LocalState010111LRecord ] . 
GeneratePruvendoRecord LocalState01011L LocalStateFields01011I . 
Opaque LocalState01011LRecord . 

Inductive LocalStateFields01100I := | ??011000 | ??011001 . 
Definition LocalState01100L := [ LocalState011000LRecord ; LocalState011001LRecord ] . 
GeneratePruvendoRecord LocalState01100L LocalStateFields01100I . 
Opaque LocalState01100LRecord . 

Inductive LocalStateFields01101I := | ??011010 | ??011011 . 
Definition LocalState01101L := [ LocalState011010LRecord ; LocalState011011LRecord ] . 
GeneratePruvendoRecord LocalState01101L LocalStateFields01101I . 
Opaque LocalState01101LRecord . 

Inductive LocalStateFields01110I := | ??011100 | ??011101 . 
Definition LocalState01110L := [ LocalState011100LRecord ; LocalState011101LRecord ] . 
GeneratePruvendoRecord LocalState01110L LocalStateFields01110I . 
Opaque LocalState01110LRecord . 

Inductive LocalStateFields01111I := | ??011110 | ??011111 . 
Definition LocalState01111L := [ LocalState011110LRecord ; LocalState011111LRecord ] . 
GeneratePruvendoRecord LocalState01111L LocalStateFields01111I . 
Opaque LocalState01111LRecord . 

Inductive LocalStateFields10000I := | ??100000 | ??100001 . 
Definition LocalState10000L := [ LocalState100000LRecord ; LocalState100001LRecord ] . 
GeneratePruvendoRecord LocalState10000L LocalStateFields10000I . 
Opaque LocalState10000LRecord . 

Inductive LocalStateFields10001I := | ??100010 | ??100011 . 
Definition LocalState10001L := [ LocalState100010LRecord ; LocalState100011LRecord ] . 
GeneratePruvendoRecord LocalState10001L LocalStateFields10001I . 
Opaque LocalState10001LRecord . 

Inductive LocalStateFields10010I := | ??100100 | ??100101 . 
Definition LocalState10010L := [ LocalState100100LRecord ; LocalState100101LRecord ] . 
GeneratePruvendoRecord LocalState10010L LocalStateFields10010I . 
Opaque LocalState10010LRecord . 

Inductive LocalStateFields10011I := | ??100110 | ??100111 . 
Definition LocalState10011L := [ LocalState100110LRecord ; LocalState100111LRecord ] . 
GeneratePruvendoRecord LocalState10011L LocalStateFields10011I . 
Opaque LocalState10011LRecord . 

Inductive LocalStateFields10100I := | ??101000 | ??101001 . 
Definition LocalState10100L := [ LocalState101000LRecord ; LocalState101001LRecord ] . 
GeneratePruvendoRecord LocalState10100L LocalStateFields10100I . 
Opaque LocalState10100LRecord . 

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
Definition LocalState1010L := [ LocalState10100LRecord ; LocalState101010LRecord ] . 
GeneratePruvendoRecord LocalState1010L LocalStateFields1010I . 
Opaque LocalState1010LRecord . 

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

Inductive LocalStateFields00I := | ??000 | ??001 . 
Definition LocalState00L := [ LocalState000LRecord ; LocalState001LRecord ] . 
GeneratePruvendoRecord LocalState00L LocalStateFields00I . 
Opaque LocalState00LRecord . 

Inductive LocalStateFields01I := | ??010 | ??011 . 
Definition LocalState01L := [ LocalState010LRecord ; LocalState011LRecord ] . 
GeneratePruvendoRecord LocalState01L LocalStateFields01I . 
Opaque LocalState01LRecord . 

Inductive LocalStateFields10I := | ??100 | ??101 . 
Definition LocalState10L := [ LocalState100LRecord ; LocalState1010LRecord ] . 
GeneratePruvendoRecord LocalState10L LocalStateFields10I . 
Opaque LocalState10LRecord . 

Inductive LocalStateFields0I := | ??00 | ??01 . 
Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
GeneratePruvendoRecord LocalState0L LocalStateFields0I . 
Opaque LocalState0LRecord . 

Inductive LocalStateFieldsI := | ??0 | ??1 . 
Definition LocalStateL := [ LocalState0LRecord ; LocalState10LRecord ] . 
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
 Transparent LocalState000000LRecord LocalState000001LRecord LocalState000010LRecord LocalState000011LRecord LocalState000100LRecord LocalState000101LRecord LocalState000110LRecord LocalState000111LRecord LocalState001000LRecord LocalState001001LRecord LocalState001010LRecord LocalState001011LRecord LocalState001100LRecord LocalState001101LRecord LocalState001110LRecord LocalState001111LRecord LocalState010000LRecord LocalState010001LRecord LocalState010010LRecord LocalState010011LRecord LocalState010100LRecord LocalState010101LRecord LocalState010110LRecord LocalState010111LRecord LocalState011000LRecord LocalState011001LRecord LocalState011010LRecord LocalState011011LRecord LocalState011100LRecord LocalState011101LRecord LocalState011110LRecord LocalState011111LRecord LocalState100000LRecord LocalState100001LRecord LocalState100010LRecord LocalState100011LRecord LocalState100100LRecord LocalState100101LRecord LocalState100110LRecord LocalState100111LRecord LocalState101000LRecord LocalState101001LRecord LocalState101010LRecord LocalState00000LRecord LocalState00001LRecord LocalState00010LRecord LocalState00011LRecord LocalState00100LRecord LocalState00101LRecord LocalState00110LRecord LocalState00111LRecord LocalState01000LRecord LocalState01001LRecord LocalState01010LRecord LocalState01011LRecord LocalState01100LRecord LocalState01101LRecord LocalState01110LRecord LocalState01111LRecord LocalState10000LRecord LocalState10001LRecord LocalState10010LRecord LocalState10011LRecord LocalState10100LRecord LocalState101010LRecord LocalState0000LRecord LocalState0001LRecord LocalState0010LRecord LocalState0011LRecord LocalState0100LRecord LocalState0101LRecord LocalState0110LRecord LocalState0111LRecord LocalState1000LRecord LocalState1001LRecord LocalState1010LRecord LocalState000LRecord LocalState001LRecord LocalState010LRecord LocalState011LRecord LocalState100LRecord LocalState00LRecord LocalState01LRecord LocalState10LRecord LocalState0LRecord LocalStateLRecord .
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

Definition  VMState_IsCommittedEmbedded := VMStateLEmbeddedType VMState_??_IsCommitted.
Definition MainCopySameType : field_type  Ledger_MainState = field_type Ledger_MainStateCopy := eq_refl.
Definition MessagesCopySameType : field_type  Ledger_MessagesState = field_type Ledger_MessagesStateCopy := eq_refl.

#[local]
Obligation Tactic := idtac.


#[global, program] Instance LocalStateField000000 : LocalStateField ( StateInitLRecord * XUInteger256 ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00000). 
 eapply TransEmbedded. eapply (_ ??000000). 
 eapply (LocalState000000LEmbeddedType ??0000001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00000). 
 eapply TransEmbedded. eapply (_ ??000000). 
 eapply (LocalState000000LEmbeddedType ??0000000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000000 : typeclass_instances. 
 #[global, program] Instance LocalStateField000001 : LocalStateField cell.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00000). 
 eapply TransEmbedded. eapply (_ ??000001). 
 eapply (LocalState000001LEmbeddedType ??0000011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00000). 
 eapply TransEmbedded. eapply (_ ??000001). 
 eapply (LocalState000001LEmbeddedType ??0000010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000001 : typeclass_instances. 
 #[global, program] Instance LocalStateField000010 : LocalStateField StateInitLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00001). 
 eapply TransEmbedded. eapply (_ ??000010). 
 eapply (LocalState000010LEmbeddedType ??0000101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00001). 
 eapply TransEmbedded. eapply (_ ??000010). 
 eapply (LocalState000010LEmbeddedType ??0000100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000010 : typeclass_instances. 
 #[global, program] Instance LocalStateField000011 : LocalStateField XUInteger256.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00001). 
 eapply TransEmbedded. eapply (_ ??000011). 
 eapply (LocalState000011LEmbeddedType ??0000111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0000). 
 eapply TransEmbedded. eapply (_ ??00001). 
 eapply TransEmbedded. eapply (_ ??000011). 
 eapply (LocalState000011LEmbeddedType ??0000110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000011 : typeclass_instances. 
 #[global, program] Instance LocalStateField000100 : LocalStateField ( XMaybe address ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00010). 
 eapply TransEmbedded. eapply (_ ??000100). 
 eapply (LocalState000100LEmbeddedType ??0001001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00010). 
 eapply TransEmbedded. eapply (_ ??000100). 
 eapply (LocalState000100LEmbeddedType ??0001000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000100 : typeclass_instances. 
 #[global, program] Instance LocalStateField000101 : LocalStateField TONTonkenWalletClassTypesModule.DTONTokenWalletExternalLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00010). 
 eapply TransEmbedded. eapply (_ ??000101). 
 eapply (LocalState000101LEmbeddedType ??0001011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00010). 
 eapply TransEmbedded. eapply (_ ??000101). 
 eapply (LocalState000101LEmbeddedType ??0001010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000101 : typeclass_instances. 
 #[global, program] Instance LocalStateField000110 : LocalStateField TONTonkenWalletClassTypesModule.DTONTokenWalletInternalLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00011). 
 eapply TransEmbedded. eapply (_ ??000110). 
 eapply (LocalState000110LEmbeddedType ??0001101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00011). 
 eapply TransEmbedded. eapply (_ ??000110). 
 eapply (LocalState000110LEmbeddedType ??0001100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000110 : typeclass_instances. 
 #[global, program] Instance LocalStateField000111 : LocalStateField TradingPairClassTypesModule.DTradingPairLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00011). 
 eapply TransEmbedded. eapply (_ ??000111). 
 eapply (LocalState000111LEmbeddedType ??0001111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??000). 
 eapply TransEmbedded. eapply (_ ??0001). 
 eapply TransEmbedded. eapply (_ ??00011). 
 eapply TransEmbedded. eapply (_ ??000111). 
 eapply (LocalState000111LEmbeddedType ??0001110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000111 : typeclass_instances. 
 #[global, program] Instance LocalStateField001000 : LocalStateField ( address * ( XHMap XUInteger256 TradingPairListingRequestLRecord ) ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00100). 
 eapply TransEmbedded. eapply (_ ??001000). 
 eapply (LocalState001000LEmbeddedType ??0010001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00100). 
 eapply TransEmbedded. eapply (_ ??001000). 
 eapply (LocalState001000LEmbeddedType ??0010000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001000 : typeclass_instances. 
 #[global, program] Instance LocalStateField001001 : LocalStateField ( XHMap XUInteger256 TradingPairListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00100). 
 eapply TransEmbedded. eapply (_ ??001001). 
 eapply (LocalState001001LEmbeddedType ??0010011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00100). 
 eapply TransEmbedded. eapply (_ ??001001). 
 eapply (LocalState001001LEmbeddedType ??0010010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001001 : typeclass_instances. 
 #[global, program] Instance LocalStateField001010 : LocalStateField ( address * ( XHMap XUInteger256 XchgPairListingRequestLRecord ) ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00101). 
 eapply TransEmbedded. eapply (_ ??001010). 
 eapply (LocalState001010LEmbeddedType ??0010101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00101). 
 eapply TransEmbedded. eapply (_ ??001010). 
 eapply (LocalState001010LEmbeddedType ??0010100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001010 : typeclass_instances. 
 #[global, program] Instance LocalStateField001011 : LocalStateField ( XHMap XUInteger256 XchgPairListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00101). 
 eapply TransEmbedded. eapply (_ ??001011). 
 eapply (LocalState001011LEmbeddedType ??0010111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0010). 
 eapply TransEmbedded. eapply (_ ??00101). 
 eapply TransEmbedded. eapply (_ ??001011). 
 eapply (LocalState001011LEmbeddedType ??0010110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001011 : typeclass_instances. 
 #[global, program] Instance LocalStateField001100 : LocalStateField ( address * ( XHMap XUInteger256 WrapperListingRequestLRecord ) ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00110). 
 eapply TransEmbedded. eapply (_ ??001100). 
 eapply (LocalState001100LEmbeddedType ??0011001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00110). 
 eapply TransEmbedded. eapply (_ ??001100). 
 eapply (LocalState001100LEmbeddedType ??0011000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001100 : typeclass_instances. 
 #[global, program] Instance LocalStateField001101 : LocalStateField ( XHMap XUInteger256 WrapperListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00110). 
 eapply TransEmbedded. eapply (_ ??001101). 
 eapply (LocalState001101LEmbeddedType ??0011011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00110). 
 eapply TransEmbedded. eapply (_ ??001101). 
 eapply (LocalState001101LEmbeddedType ??0011010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001101 : typeclass_instances. 
 #[global, program] Instance LocalStateField001110 : LocalStateField address.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00111). 
 eapply TransEmbedded. eapply (_ ??001110). 
 eapply (LocalState001110LEmbeddedType ??0011101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00111). 
 eapply TransEmbedded. eapply (_ ??001110). 
 eapply (LocalState001110LEmbeddedType ??0011100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001110 : typeclass_instances. 
 #[global, program] Instance LocalStateField001111 : LocalStateField slice.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00111). 
 eapply TransEmbedded. eapply (_ ??001111). 
 eapply (LocalState001111LEmbeddedType ??0011111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??00). 
 eapply TransEmbedded. eapply (_ ??001). 
 eapply TransEmbedded. eapply (_ ??0011). 
 eapply TransEmbedded. eapply (_ ??00111). 
 eapply TransEmbedded. eapply (_ ??001111). 
 eapply (LocalState001111LEmbeddedType ??0011110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001111 : typeclass_instances. 
 #[global, program] Instance LocalStateField010000 : LocalStateField XBool.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01000). 
 eapply TransEmbedded. eapply (_ ??010000). 
 eapply (LocalState010000LEmbeddedType ??0100001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01000). 
 eapply TransEmbedded. eapply (_ ??010000). 
 eapply (LocalState010000LEmbeddedType ??0100000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010000 : typeclass_instances. 
 #[global, program] Instance LocalStateField010001 : LocalStateField  XchgPairClassTypesModule.DXchgPairLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01000). 
 eapply TransEmbedded. eapply (_ ??010001). 
 eapply (LocalState010001LEmbeddedType ??0100011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01000). 
 eapply TransEmbedded. eapply (_ ??010001). 
 eapply (LocalState010001LEmbeddedType ??0100010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010001 : typeclass_instances. 
 #[global, program] Instance LocalStateField010010 : LocalStateField WrapperClassTypesModule.DWrapperLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01001). 
 eapply TransEmbedded. eapply (_ ??010010). 
 eapply (LocalState010010LEmbeddedType ??0100101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01001). 
 eapply TransEmbedded. eapply (_ ??010010). 
 eapply (LocalState010010LEmbeddedType ??0100100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010010 : typeclass_instances. 
 #[global, program] Instance LocalStateField010011 : LocalStateField FlexDetailsLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01001). 
 eapply TransEmbedded. eapply (_ ??010011). 
 eapply (LocalState010011LEmbeddedType ??0100111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0100). 
 eapply TransEmbedded. eapply (_ ??01001). 
 eapply TransEmbedded. eapply (_ ??010011). 
 eapply (LocalState010011LEmbeddedType ??0100110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010011 : typeclass_instances. 
 #[global, program] Instance LocalStateField010100 : LocalStateField TonsConfigLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01010). 
 eapply TransEmbedded. eapply (_ ??010100). 
 eapply (LocalState010100LEmbeddedType ??0101001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01010). 
 eapply TransEmbedded. eapply (_ ??010100). 
 eapply (LocalState010100LEmbeddedType ??0101000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010100 : typeclass_instances. 
 #[global, program] Instance LocalStateField010101 : LocalStateField ListingConfigLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01010). 
 eapply TransEmbedded. eapply (_ ??010101). 
 eapply (LocalState010101LEmbeddedType ??0101011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01010). 
 eapply TransEmbedded. eapply (_ ??010101). 
 eapply (LocalState010101LEmbeddedType ??0101010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010101 : typeclass_instances. 
 #[global, program] Instance LocalStateField010110 : LocalStateField Tip3ConfigLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01011). 
 eapply TransEmbedded. eapply (_ ??010110). 
 eapply (LocalState010110LEmbeddedType ??0101101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01011). 
 eapply TransEmbedded. eapply (_ ??010110). 
 eapply (LocalState010110LEmbeddedType ??0101100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010110 : typeclass_instances. 
 #[global, program] Instance LocalStateField010111 : LocalStateField XUInteger8.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01011). 
 eapply TransEmbedded. eapply (_ ??010111). 
 eapply (LocalState010111LEmbeddedType ??0101111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??010). 
 eapply TransEmbedded. eapply (_ ??0101). 
 eapply TransEmbedded. eapply (_ ??01011). 
 eapply TransEmbedded. eapply (_ ??010111). 
 eapply (LocalState010111LEmbeddedType ??0101110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010111 : typeclass_instances. 
 #[global, program] Instance LocalStateField011000 : LocalStateField FlexOwnershipInfoLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01100). 
 eapply TransEmbedded. eapply (_ ??011000). 
 eapply (LocalState011000LEmbeddedType ??0110001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01100). 
 eapply TransEmbedded. eapply (_ ??011000). 
 eapply (LocalState011000LEmbeddedType ??0110000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011000 : typeclass_instances. 
 #[global, program] Instance LocalStateField011001 : LocalStateField ( XHMap XUInteger WrapperListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01100). 
 eapply TransEmbedded. eapply (_ ??011001). 
 eapply (LocalState011001LEmbeddedType ??0110011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01100). 
 eapply TransEmbedded. eapply (_ ??011001). 
 eapply (LocalState011001LEmbeddedType ??0110010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011001 : typeclass_instances. 
 #[global, program] Instance LocalStateField011010 : LocalStateField ( XHMap XUInteger TradingPairListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01101). 
 eapply TransEmbedded. eapply (_ ??011010). 
 eapply (LocalState011010LEmbeddedType ??0110101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01101). 
 eapply TransEmbedded. eapply (_ ??011010). 
 eapply (LocalState011010LEmbeddedType ??0110100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011010 : typeclass_instances. 
 #[global, program] Instance LocalStateField011011 : LocalStateField ( XHMap XUInteger XchgPairListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01101). 
 eapply TransEmbedded. eapply (_ ??011011). 
 eapply (LocalState011011LEmbeddedType ??0110111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0110). 
 eapply TransEmbedded. eapply (_ ??01101). 
 eapply TransEmbedded. eapply (_ ??011011). 
 eapply (LocalState011011LEmbeddedType ??0110110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011011 : typeclass_instances. 
 #[global, program] Instance LocalStateField011100 : LocalStateField XUInteger.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01110). 
 eapply TransEmbedded. eapply (_ ??011100). 
 eapply (LocalState011100LEmbeddedType ??0111001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01110). 
 eapply TransEmbedded. eapply (_ ??011100). 
 eapply (LocalState011100LEmbeddedType ??0111000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011100 : typeclass_instances. 
 #[global, program] Instance LocalStateField011101 : LocalStateField ( address * address ) (* IWrapperPtrLRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01110). 
 eapply TransEmbedded. eapply (_ ??011101). 
 eapply (LocalState011101LEmbeddedType ??0111011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01110). 
 eapply TransEmbedded. eapply (_ ??011101). 
 eapply (LocalState011101LEmbeddedType ??0111010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011101 : typeclass_instances. 
 #[global, program] Instance LocalStateField011110 : LocalStateField address (* ITONTokenWalletPtrLRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01111). 
 eapply TransEmbedded. eapply (_ ??011110). 
 eapply (LocalState011110LEmbeddedType ??0111101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01111). 
 eapply TransEmbedded. eapply (_ ??011110). 
 eapply (LocalState011110LEmbeddedType ??0111100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011110 : typeclass_instances. 
 #[global, program] Instance LocalStateField011111 : LocalStateField ( XMaybe WrapperListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01111). 
 eapply TransEmbedded. eapply (_ ??011111). 
 eapply (LocalState011111LEmbeddedType ??0111111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??0). 
 eapply TransEmbedded. eapply (_ ??01). 
 eapply TransEmbedded. eapply (_ ??011). 
 eapply TransEmbedded. eapply (_ ??0111). 
 eapply TransEmbedded. eapply (_ ??01111). 
 eapply TransEmbedded. eapply (_ ??011111). 
 eapply (LocalState011111LEmbeddedType ??0111110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011111 : typeclass_instances. 
 #[global, program] Instance LocalStateField100000 : LocalStateField ( XMaybe TradingPairListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10000). 
 eapply TransEmbedded. eapply (_ ??100000). 
 eapply (LocalState100000LEmbeddedType ??1000001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10000). 
 eapply TransEmbedded. eapply (_ ??100000). 
 eapply (LocalState100000LEmbeddedType ??1000000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100000 : typeclass_instances. 
 #[global, program] Instance LocalStateField100001 : LocalStateField ( XMaybe XchgPairListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10000). 
 eapply TransEmbedded. eapply (_ ??100001). 
 eapply (LocalState100001LEmbeddedType ??1000011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10000). 
 eapply TransEmbedded. eapply (_ ??100001). 
 eapply (LocalState100001LEmbeddedType ??1000010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100001 : typeclass_instances. 
 #[global, program] Instance LocalStateField100010 : LocalStateField ( XMaybe WrapperListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10001). 
 eapply TransEmbedded. eapply (_ ??100010). 
 eapply (LocalState100010LEmbeddedType ??1000101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10001). 
 eapply TransEmbedded. eapply (_ ??100010). 
 eapply (LocalState100010LEmbeddedType ??1000100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100010 : typeclass_instances. 
 #[global, program] Instance LocalStateField100011 : LocalStateField ( XMaybe TradingPairListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10001). 
 eapply TransEmbedded. eapply (_ ??100011). 
 eapply (LocalState100011LEmbeddedType ??1000111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1000). 
 eapply TransEmbedded. eapply (_ ??10001). 
 eapply TransEmbedded. eapply (_ ??100011). 
 eapply (LocalState100011LEmbeddedType ??1000110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100011 : typeclass_instances. 
 #[global, program] Instance LocalStateField100100 : LocalStateField ( XMaybe XchgPairListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10010). 
 eapply TransEmbedded. eapply (_ ??100100). 
 eapply (LocalState100100LEmbeddedType ??1001001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10010). 
 eapply TransEmbedded. eapply (_ ??100100). 
 eapply (LocalState100100LEmbeddedType ??1001000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100100 : typeclass_instances. 
 #[global, program] Instance LocalStateField100101 : LocalStateField WrapperListingRequestWithPubkeyLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10010). 
 eapply TransEmbedded. eapply (_ ??100101). 
 eapply (LocalState100101LEmbeddedType ??1001011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10010). 
 eapply TransEmbedded. eapply (_ ??100101). 
 eapply (LocalState100101LEmbeddedType ??1001010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100101 : typeclass_instances. 
 #[global, program] Instance LocalStateField100110 : LocalStateField TradingPairListingRequestWithPubkeyLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10011). 
 eapply TransEmbedded. eapply (_ ??100110). 
 eapply (LocalState100110LEmbeddedType ??1001101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10011). 
 eapply TransEmbedded. eapply (_ ??100110). 
 eapply (LocalState100110LEmbeddedType ??1001100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100110 : typeclass_instances. 
 #[global, program] Instance LocalStateField100111 : LocalStateField XchgPairListingRequestWithPubkeyLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10011). 
 eapply TransEmbedded. eapply (_ ??100111). 
 eapply (LocalState100111LEmbeddedType ??1001111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??100). 
 eapply TransEmbedded. eapply (_ ??1001). 
 eapply TransEmbedded. eapply (_ ??10011). 
 eapply TransEmbedded. eapply (_ ??100111). 
 eapply (LocalState100111LEmbeddedType ??1001110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100111 : typeclass_instances. 
 #[global, program] Instance LocalStateField101000 : LocalStateField WrapperListingRequestLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??10100). 
 eapply TransEmbedded. eapply (_ ??101000). 
 eapply (LocalState101000LEmbeddedType ??1010001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??10100). 
 eapply TransEmbedded. eapply (_ ??101000). 
 eapply (LocalState101000LEmbeddedType ??1010000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField101000 : typeclass_instances. 
 #[global, program] Instance LocalStateField101001 : LocalStateField TradingPairListingRequestLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??10100). 
 eapply TransEmbedded. eapply (_ ??101001). 
 eapply (LocalState101001LEmbeddedType ??1010011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??10100). 
 eapply TransEmbedded. eapply (_ ??101001). 
 eapply (LocalState101001LEmbeddedType ??1010010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField101001 : typeclass_instances. 
 #[global, program] Instance LocalStateField101010 : LocalStateField XchgPairListingRequestLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??10101). 
 eapply (LocalState101010LEmbeddedType ??1010101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ??1). 
 eapply TransEmbedded. eapply (_ ??101). 
 eapply TransEmbedded. eapply (_ ??10101). 
 eapply (LocalState101010LEmbeddedType ??1010100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField101010 : typeclass_instances. 


(* Definition LocalStateField_XUInteger := LocalStateField011100 .
Definition LocalStateField_XBool := LocalStateField010001 .
Definition LocalStateField_cell := LocalStateField000001 . *)

Definition GlobalParamsEmbedded := MessagesAndEventsLEmbeddedType _GlobalParams.
Definition OutgoingMessageParamsEmbedded := MessagesAndEventsLEmbeddedType _OutgoingMessageParams.


End Ledger .




