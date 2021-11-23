Require Import Coq.Program.Basics. 

Require Import String. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 

Require Import FinProof.ProgrammingWith.  
Require Import UMLang.UrsusLib. 
Require Import UMLang.BasicModuleTypes. 
Require Import UrsusTVM.Cpp.tvmFunc. 

Require Import Project.CommonTypes. 
Require Import Contracts.Flex.ClassTypes.
Require Contracts.TradingPair.ClassTypes.
Require Import Contracts.Flex.Interface.
Require Import UMLang.GlobalClassGenerator.ClassGenerator.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) Inductive MessagesAndEventsFields := | _OutgoingMessages_SelfDeployer | _EmittedEvents | _MessagesLog.
(* 1 *) Inductive ContractFields := 
| deployer_pubkey_ 
| workchain_id_ 
| ownership_description_ 
| owner_address_ 
| tons_cfg_ 
| listing_cfg_ 
| pair_code_ 
| xchg_pair_code_ 
| price_code_ 
| xchg_price_code_ 
| ext_wallet_code_ 
| flex_wallet_code_ 
| wrapper_code_ 
| deals_limit_ 
| wrapper_listing_requests_
| trading_pair_listing_requests_
| xchg_pair_listing_requests_ .

(* 1 *) Inductive LedgerFieldsI := | _Contract | _ContractCopy | _VMState | _MessagesAndEvents | _MessagesAndEventsCopy | _LocalState | _LocalStateCopy .

Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 

Module FlexPublicInterfaceModule := PublicInterface xt sm.

Module Export BasicTypesModule := BasicTypes xt sm.
Module Export VMStateModule := VMStateModule xt sm. 
Module Export ClassTypesModule := Flex.ClassTypes.ClassTypes xt sm .
Module TradingPairClassTypesModule := TradingPair.ClassTypes.ClassTypes xt sm .
Import xt. 


(* 2 *) Definition MessagesAndEventsL : list Type := 
 [ ( XQueue FlexPublicInterfaceModule.OutgoingMessage ) : Type ; 
 ( XList TVMEvent ) : Type ; 
 ( XString ) : Type ] .
GeneratePruvendoRecord MessagesAndEventsL MessagesAndEventsFields .
  Opaque MessagesAndEventsLRecord .
 
(* 2 *) Definition ContractL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XString ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( ListingConfigLRecord ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
  ( XUInteger8 ) : Type ;
 ( (XHMap XUInteger256 (XUInteger256 * WrapperListingRequestLRecord)) ) : Type ; 
 ( (XHMap XUInteger256 (XUInteger256 * TradingPairListingRequestLRecord)) ) : Type ; 
 ( (XHMap XUInteger256 (XUInteger256 * XchgPairListingRequestLRecord)) ) : Type ] .

Elpi GeneratePruvendoRecord ContractL ContractFields . 
 Opaque ContractLRecord . 


 Inductive LocalStateFields000000I := | ι0000000 | ι0000001 . 
 Definition LocalState000000L := [ ( XHMap (string*nat) ( StateInitLRecord * XUInteger256 ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState000000L LocalStateFields000000I . 
 Opaque LocalState000000LRecord . 
 
 Inductive LocalStateFields000001I := | ι0000010 | ι0000011 . 
 Definition LocalState000001L := [ ( XHMap (string*nat) XCell ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState000001L LocalStateFields000001I . 
 Opaque LocalState000001LRecord . 
 
 Inductive LocalStateFields000010I := | ι0000100 | ι0000101 . 
 Definition LocalState000010L := [ ( XHMap (string*nat) StateInitLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState000010L LocalStateFields000010I . 
 Opaque LocalState000010LRecord . 
 
 Inductive LocalStateFields000011I := | ι0000110 | ι0000111 . 
 Definition LocalState000011L := [ ( XHMap (string*nat) XUInteger256 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState000011L LocalStateFields000011I . 
 Opaque LocalState000011LRecord . 
 
 Inductive LocalStateFields000100I := | ι0001000 | ι0001001 . 
 Definition LocalState000100L := [ ( XHMap (string*nat) ( XMaybe XAddress ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState000100L LocalStateFields000100I . 
 Opaque LocalState000100LRecord . 
 
 Inductive LocalStateFields000101I := | ι0001010 | ι0001011 . 
 Definition LocalState000101L := [ ( XHMap (string*nat) DTONTokenWalletExternalLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState000101L LocalStateFields000101I . 
 Opaque LocalState000101LRecord . 
 
 Inductive LocalStateFields000110I := | ι0001100 | ι0001101 . 
 Definition LocalState000110L := [ ( XHMap (string*nat) DTONTokenWalletInternalLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState000110L LocalStateFields000110I . 
 Opaque LocalState000110LRecord . 
 
 Inductive LocalStateFields000111I := | ι0001110 | ι0001111 . 
 Definition LocalState000111L := [ ( XHMap (string*nat) TradingPairClassTypesModule.DTradingPairLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState000111L LocalStateFields000111I . 
 Opaque LocalState000111LRecord . 
 
 Inductive LocalStateFields001000I := | ι0010000 | ι0010001 . 
 Definition LocalState001000L := [ ( XHMap (string*nat) ( XAddress * ( XHMap XUInteger256 TradingPairListingRequestLRecord ) ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState001000L LocalStateFields001000I . 
 Opaque LocalState001000LRecord . 
 
 Inductive LocalStateFields001001I := | ι0010010 | ι0010011 . 
 Definition LocalState001001L := [ ( XHMap (string*nat) ( XHMap XUInteger256 TradingPairListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState001001L LocalStateFields001001I . 
 Opaque LocalState001001LRecord . 
 
 Inductive LocalStateFields001010I := | ι0010100 | ι0010101 . 
 Definition LocalState001010L := [ ( XHMap (string*nat) ( XAddress * ( XHMap XUInteger256 XchgPairListingRequestLRecord ) ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState001010L LocalStateFields001010I . 
 Opaque LocalState001010LRecord . 
 
 Inductive LocalStateFields001011I := | ι0010110 | ι0010111 . 
 Definition LocalState001011L := [ ( XHMap (string*nat) ( XHMap XUInteger256 XchgPairListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState001011L LocalStateFields001011I . 
 Opaque LocalState001011LRecord . 
 
 Inductive LocalStateFields001100I := | ι0011000 | ι0011001 . 
 Definition LocalState001100L := [ ( XHMap (string*nat) ( XAddress * ( XHMap XUInteger256 WrapperListingRequestLRecord ) ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState001100L LocalStateFields001100I . 
 Opaque LocalState001100LRecord . 
 
 Inductive LocalStateFields001101I := | ι0011010 | ι0011011 . 
 Definition LocalState001101L := [ ( XHMap (string*nat) ( XHMap XUInteger256 WrapperListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState001101L LocalStateFields001101I . 
 Opaque LocalState001101LRecord . 
 
 Inductive LocalStateFields001110I := | ι0011100 | ι0011101 . 
 Definition LocalState001110L := [ ( XHMap (string*nat) XAddress ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState001110L LocalStateFields001110I . 
 Opaque LocalState001110LRecord . 
 
 Inductive LocalStateFields001111I := | ι0011110 | ι0011111 . 
 Definition LocalState001111L := [ ( XHMap (string*nat) XSlice ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState001111L LocalStateFields001111I . 
 Opaque LocalState001111LRecord . 
 
 Inductive LocalStateFields010000I := | ι0100000 | ι0100001 . 
 Definition LocalState010000L := [ ( XHMap (string*nat) XBool ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState010000L LocalStateFields010000I . 
 Opaque LocalState010000LRecord . 
 
 Inductive LocalStateFields010001I := | ι0100010 | ι0100011 . 
 Definition LocalState010001L := [ ( XHMap (string*nat) DXchgPairLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState010001L LocalStateFields010001I . 
 Opaque LocalState010001LRecord . 
 
 Inductive LocalStateFields010010I := | ι0100100 | ι0100101 . 
 Definition LocalState010010L := [ ( XHMap (string*nat) DWrapperLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState010010L LocalStateFields010010I . 
 Opaque LocalState010010LRecord . 
 
 Inductive LocalStateFields010011I := | ι0100110 | ι0100111 . 
 Definition LocalState010011L := [ ( XHMap (string*nat) FlexDetailsLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState010011L LocalStateFields010011I . 
 Opaque LocalState010011LRecord . 
 
 Inductive LocalStateFields010100I := | ι0101000 | ι0101001 . 
 Definition LocalState010100L := [ ( XHMap (string*nat) TonsConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState010100L LocalStateFields010100I . 
 Opaque LocalState010100LRecord . 
 
 Inductive LocalStateFields010101I := | ι0101010 | ι0101011 . 
 Definition LocalState010101L := [ ( XHMap (string*nat) ListingConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState010101L LocalStateFields010101I . 
 Opaque LocalState010101LRecord . 
 
 Inductive LocalStateFields010110I := | ι0101100 | ι0101101 . 
 Definition LocalState010110L := [ ( XHMap (string*nat) Tip3ConfigLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState010110L LocalStateFields010110I . 
 Opaque LocalState010110LRecord . 
 
 Inductive LocalStateFields010111I := | ι0101110 | ι0101111 . 
 Definition LocalState010111L := [ ( XHMap (string*nat) XUInteger8 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState010111L LocalStateFields010111I . 
 Opaque LocalState010111LRecord . 
 
 Inductive LocalStateFields011000I := | ι0110000 | ι0110001 . 
 Definition LocalState011000L := [ ( XHMap (string*nat) FlexOwnershipInfoLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState011000L LocalStateFields011000I . 
 Opaque LocalState011000LRecord . 
 
 Inductive LocalStateFields011001I := | ι0110010 | ι0110011 . 
 Definition LocalState011001L := [ ( XHMap (string*nat) ( XHMap XUInteger WrapperListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState011001L LocalStateFields011001I . 
 Opaque LocalState011001LRecord . 
 
 Inductive LocalStateFields011010I := | ι0110100 | ι0110101 . 
 Definition LocalState011010L := [ ( XHMap (string*nat) ( XHMap XUInteger TradingPairListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState011010L LocalStateFields011010I . 
 Opaque LocalState011010LRecord . 
 
 Inductive LocalStateFields011011I := | ι0110110 | ι0110111 . 
 Definition LocalState011011L := [ ( XHMap (string*nat) ( XHMap XUInteger XchgPairListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState011011L LocalStateFields011011I . 
 Opaque LocalState011011LRecord . 
 
 Inductive LocalStateFields011100I := | ι0111000 | ι0111001 . 
 Definition LocalState011100L := [ ( XHMap (string*nat) XUInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState011100L LocalStateFields011100I . 
 Opaque LocalState011100LRecord . 
 
 Inductive LocalStateFields011101I := | ι0111010 | ι0111011 . 
 Definition LocalState011101L := [ ( XHMap (string*nat) ( XAddress * XAddress (* IWrapperPtrLRecord *) ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState011101L LocalStateFields011101I . 
 Opaque LocalState011101LRecord . 
 
 Inductive LocalStateFields011110I := | ι0111100 | ι0111101 . 
 Definition LocalState011110L := [ ( XHMap (string*nat) XAddress (* ITONTokenWalletPtrLRecord *) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState011110L LocalStateFields011110I . 
 Opaque LocalState011110LRecord . 
 
 Inductive LocalStateFields011111I := | ι0111110 | ι0111111 . 
 Definition LocalState011111L := [ ( XHMap (string*nat) ( XMaybe WrapperListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState011111L LocalStateFields011111I . 
 Opaque LocalState011111LRecord . 
 
 Inductive LocalStateFields100000I := | ι1000000 | ι1000001 . 
 Definition LocalState100000L := [ ( XHMap (string*nat) ( XMaybe TradingPairListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState100000L LocalStateFields100000I . 
 Opaque LocalState100000LRecord . 
 
 Inductive LocalStateFields100001I := | ι1000010 | ι1000011 . 
 Definition LocalState100001L := [ ( XHMap (string*nat) ( XMaybe XchgPairListingRequestWithPubkeyLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState100001L LocalStateFields100001I . 
 Opaque LocalState100001LRecord . 
 
 Inductive LocalStateFields100010I := | ι1000100 | ι1000101 . 
 Definition LocalState100010L := [ ( XHMap (string*nat) ( XMaybe WrapperListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState100010L LocalStateFields100010I . 
 Opaque LocalState100010LRecord . 
 
 Inductive LocalStateFields100011I := | ι1000110 | ι1000111 . 
 Definition LocalState100011L := [ ( XHMap (string*nat) ( XMaybe TradingPairListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState100011L LocalStateFields100011I . 
 Opaque LocalState100011LRecord . 
 
 Inductive LocalStateFields100100I := | ι1001000 | ι1001001 . 
 Definition LocalState100100L := [ ( XHMap (string*nat) ( XMaybe XchgPairListingRequestLRecord ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState100100L LocalStateFields100100I . 
 Opaque LocalState100100LRecord . 
 
 Inductive LocalStateFields100101I := | ι1001010 | ι1001011 . 
 Definition LocalState100101L := [ ( XHMap (string*nat) WrapperListingRequestWithPubkeyLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState100101L LocalStateFields100101I . 
 Opaque LocalState100101LRecord . 
 
 Inductive LocalStateFields100110I := | ι1001100 | ι1001101 . 
 Definition LocalState100110L := [ ( XHMap (string*nat) TradingPairListingRequestWithPubkeyLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState100110L LocalStateFields100110I . 
 Opaque LocalState100110LRecord . 
 
 Inductive LocalStateFields100111I := | ι1001110 | ι1001111 . 
 Definition LocalState100111L := [ ( XHMap (string*nat) XchgPairListingRequestWithPubkeyLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState100111L LocalStateFields100111I . 
 Opaque LocalState100111LRecord . 
 
 Inductive LocalStateFields101000I := | ι1010000 | ι1010001 . 
 Definition LocalState101000L := [ ( XHMap (string*nat) WrapperListingRequestLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState101000L LocalStateFields101000I . 
 Opaque LocalState101000LRecord . 
 
 Inductive LocalStateFields101001I := | ι1010010 | ι1010011 . 
 Definition LocalState101001L := [ ( XHMap (string*nat) TradingPairListingRequestLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState101001L LocalStateFields101001I . 
 Opaque LocalState101001LRecord . 
 
 Inductive LocalStateFields101010I := | ι1010100 | ι1010101 . 
 Definition LocalState101010L := [ ( XHMap (string*nat) XchgPairListingRequestLRecord ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord LocalState101010L LocalStateFields101010I . 
 Opaque LocalState101010LRecord . 
 
 
 Inductive LocalStateFields00000I := | ι000000 | ι000001 . 
 Definition LocalState00000L := [ LocalState000000LRecord ; LocalState000001LRecord ] . 
 GeneratePruvendoRecord LocalState00000L LocalStateFields00000I . 
 Opaque LocalState00000LRecord . 
 
 Inductive LocalStateFields00001I := | ι000010 | ι000011 . 
 Definition LocalState00001L := [ LocalState000010LRecord ; LocalState000011LRecord ] . 
 GeneratePruvendoRecord LocalState00001L LocalStateFields00001I . 
 Opaque LocalState00001LRecord . 
 
 Inductive LocalStateFields00010I := | ι000100 | ι000101 . 
 Definition LocalState00010L := [ LocalState000100LRecord ; LocalState000101LRecord ] . 
 GeneratePruvendoRecord LocalState00010L LocalStateFields00010I . 
 Opaque LocalState00010LRecord . 
 
 Inductive LocalStateFields00011I := | ι000110 | ι000111 . 
 Definition LocalState00011L := [ LocalState000110LRecord ; LocalState000111LRecord ] . 
 GeneratePruvendoRecord LocalState00011L LocalStateFields00011I . 
 Opaque LocalState00011LRecord . 
 
 Inductive LocalStateFields00100I := | ι001000 | ι001001 . 
 Definition LocalState00100L := [ LocalState001000LRecord ; LocalState001001LRecord ] . 
 GeneratePruvendoRecord LocalState00100L LocalStateFields00100I . 
 Opaque LocalState00100LRecord . 
 
 Inductive LocalStateFields00101I := | ι001010 | ι001011 . 
 Definition LocalState00101L := [ LocalState001010LRecord ; LocalState001011LRecord ] . 
 GeneratePruvendoRecord LocalState00101L LocalStateFields00101I . 
 Opaque LocalState00101LRecord . 
 
 Inductive LocalStateFields00110I := | ι001100 | ι001101 . 
 Definition LocalState00110L := [ LocalState001100LRecord ; LocalState001101LRecord ] . 
 GeneratePruvendoRecord LocalState00110L LocalStateFields00110I . 
 Opaque LocalState00110LRecord . 
 
 Inductive LocalStateFields00111I := | ι001110 | ι001111 . 
 Definition LocalState00111L := [ LocalState001110LRecord ; LocalState001111LRecord ] . 
 GeneratePruvendoRecord LocalState00111L LocalStateFields00111I . 
 Opaque LocalState00111LRecord . 
 
 Inductive LocalStateFields01000I := | ι010000 | ι010001 . 
 Definition LocalState01000L := [ LocalState010000LRecord ; LocalState010001LRecord ] . 
 GeneratePruvendoRecord LocalState01000L LocalStateFields01000I . 
 Opaque LocalState01000LRecord . 
 
 Inductive LocalStateFields01001I := | ι010010 | ι010011 . 
 Definition LocalState01001L := [ LocalState010010LRecord ; LocalState010011LRecord ] . 
 GeneratePruvendoRecord LocalState01001L LocalStateFields01001I . 
 Opaque LocalState01001LRecord . 
 
 Inductive LocalStateFields01010I := | ι010100 | ι010101 . 
 Definition LocalState01010L := [ LocalState010100LRecord ; LocalState010101LRecord ] . 
 GeneratePruvendoRecord LocalState01010L LocalStateFields01010I . 
 Opaque LocalState01010LRecord . 
 
 Inductive LocalStateFields01011I := | ι010110 | ι010111 . 
 Definition LocalState01011L := [ LocalState010110LRecord ; LocalState010111LRecord ] . 
 GeneratePruvendoRecord LocalState01011L LocalStateFields01011I . 
 Opaque LocalState01011LRecord . 
 
 Inductive LocalStateFields01100I := | ι011000 | ι011001 . 
 Definition LocalState01100L := [ LocalState011000LRecord ; LocalState011001LRecord ] . 
 GeneratePruvendoRecord LocalState01100L LocalStateFields01100I . 
 Opaque LocalState01100LRecord . 
 
 Inductive LocalStateFields01101I := | ι011010 | ι011011 . 
 Definition LocalState01101L := [ LocalState011010LRecord ; LocalState011011LRecord ] . 
 GeneratePruvendoRecord LocalState01101L LocalStateFields01101I . 
 Opaque LocalState01101LRecord . 
 
 Inductive LocalStateFields01110I := | ι011100 | ι011101 . 
 Definition LocalState01110L := [ LocalState011100LRecord ; LocalState011101LRecord ] . 
 GeneratePruvendoRecord LocalState01110L LocalStateFields01110I . 
 Opaque LocalState01110LRecord . 
 
 Inductive LocalStateFields01111I := | ι011110 | ι011111 . 
 Definition LocalState01111L := [ LocalState011110LRecord ; LocalState011111LRecord ] . 
 GeneratePruvendoRecord LocalState01111L LocalStateFields01111I . 
 Opaque LocalState01111LRecord . 
 
 Inductive LocalStateFields10000I := | ι100000 | ι100001 . 
 Definition LocalState10000L := [ LocalState100000LRecord ; LocalState100001LRecord ] . 
 GeneratePruvendoRecord LocalState10000L LocalStateFields10000I . 
 Opaque LocalState10000LRecord . 
 
 Inductive LocalStateFields10001I := | ι100010 | ι100011 . 
 Definition LocalState10001L := [ LocalState100010LRecord ; LocalState100011LRecord ] . 
 GeneratePruvendoRecord LocalState10001L LocalStateFields10001I . 
 Opaque LocalState10001LRecord . 
 
 Inductive LocalStateFields10010I := | ι100100 | ι100101 . 
 Definition LocalState10010L := [ LocalState100100LRecord ; LocalState100101LRecord ] . 
 GeneratePruvendoRecord LocalState10010L LocalStateFields10010I . 
 Opaque LocalState10010LRecord . 
 
 Inductive LocalStateFields10011I := | ι100110 | ι100111 . 
 Definition LocalState10011L := [ LocalState100110LRecord ; LocalState100111LRecord ] . 
 GeneratePruvendoRecord LocalState10011L LocalStateFields10011I . 
 Opaque LocalState10011LRecord . 
 
 Inductive LocalStateFields10100I := | ι101000 | ι101001 . 
 Definition LocalState10100L := [ LocalState101000LRecord ; LocalState101001LRecord ] . 
 GeneratePruvendoRecord LocalState10100L LocalStateFields10100I . 
 Opaque LocalState10100LRecord . 
 
 
 
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
 Definition LocalState1010L := [ LocalState10100LRecord ; LocalState101010LRecord ] . 
 GeneratePruvendoRecord LocalState1010L LocalStateFields1010I . 
 Opaque LocalState1010LRecord . 
 
 
 
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
 
 Inductive LocalStateFields10I := | ι100 | ι101 . 
 Definition LocalState10L := [ LocalState100LRecord ; LocalState1010LRecord ] . 
 GeneratePruvendoRecord LocalState10L LocalStateFields10I . 
 Opaque LocalState10LRecord . 
 
 
 
 Inductive LocalStateFields0I := | ι00 | ι01 . 
 Definition LocalState0L := [ LocalState00LRecord ; LocalState01LRecord ] . 
 GeneratePruvendoRecord LocalState0L LocalStateFields0I . 
 Opaque LocalState0LRecord . 
 
 
 
 Inductive LocalStateFieldsI := | ι0 | ι1 . 
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

Definition  VMState_IsCommittedEmbedded := VMStateLEmbeddedType VMState_ι_IsCommitted.
Definition MainCopySameType : field_type  Ledger_MainState = field_type Ledger_MainStateCopy := eq_refl.
Definition MessagesCopySameType : field_type  Ledger_MessagesState = field_type Ledger_MessagesStateCopy := eq_refl.

#[local]
Obligation Tactic := idtac.


#[global, program] Instance LocalStateField000000 : LocalStateField ( StateInitLRecord * XUInteger256 ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00000). 
 eapply TransEmbedded. eapply (_ ι000000). 
 eapply (LocalState000000LEmbeddedType ι0000001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00000). 
 eapply TransEmbedded. eapply (_ ι000000). 
 eapply (LocalState000000LEmbeddedType ι0000000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000000 : typeclass_instances. 
 #[global, program] Instance LocalStateField000001 : LocalStateField XCell.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00000). 
 eapply TransEmbedded. eapply (_ ι000001). 
 eapply (LocalState000001LEmbeddedType ι0000011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00000). 
 eapply TransEmbedded. eapply (_ ι000001). 
 eapply (LocalState000001LEmbeddedType ι0000010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000001 : typeclass_instances. 
 #[global, program] Instance LocalStateField000010 : LocalStateField StateInitLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00001). 
 eapply TransEmbedded. eapply (_ ι000010). 
 eapply (LocalState000010LEmbeddedType ι0000101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00001). 
 eapply TransEmbedded. eapply (_ ι000010). 
 eapply (LocalState000010LEmbeddedType ι0000100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000010 : typeclass_instances. 
 #[global, program] Instance LocalStateField000011 : LocalStateField XUInteger256.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00001). 
 eapply TransEmbedded. eapply (_ ι000011). 
 eapply (LocalState000011LEmbeddedType ι0000111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0000). 
 eapply TransEmbedded. eapply (_ ι00001). 
 eapply TransEmbedded. eapply (_ ι000011). 
 eapply (LocalState000011LEmbeddedType ι0000110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000011 : typeclass_instances. 
 #[global, program] Instance LocalStateField000100 : LocalStateField ( XMaybe XAddress ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00010). 
 eapply TransEmbedded. eapply (_ ι000100). 
 eapply (LocalState000100LEmbeddedType ι0001001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00010). 
 eapply TransEmbedded. eapply (_ ι000100). 
 eapply (LocalState000100LEmbeddedType ι0001000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000100 : typeclass_instances. 
 #[global, program] Instance LocalStateField000101 : LocalStateField DTONTokenWalletExternalLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00010). 
 eapply TransEmbedded. eapply (_ ι000101). 
 eapply (LocalState000101LEmbeddedType ι0001011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00010). 
 eapply TransEmbedded. eapply (_ ι000101). 
 eapply (LocalState000101LEmbeddedType ι0001010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000101 : typeclass_instances. 
 #[global, program] Instance LocalStateField000110 : LocalStateField DTONTokenWalletInternalLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00011). 
 eapply TransEmbedded. eapply (_ ι000110). 
 eapply (LocalState000110LEmbeddedType ι0001101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00011). 
 eapply TransEmbedded. eapply (_ ι000110). 
 eapply (LocalState000110LEmbeddedType ι0001100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000110 : typeclass_instances. 
 #[global, program] Instance LocalStateField000111 : LocalStateField DTradingPairLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00011). 
 eapply TransEmbedded. eapply (_ ι000111). 
 eapply (LocalState000111LEmbeddedType ι0001111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι000). 
 eapply TransEmbedded. eapply (_ ι0001). 
 eapply TransEmbedded. eapply (_ ι00011). 
 eapply TransEmbedded. eapply (_ ι000111). 
 eapply (LocalState000111LEmbeddedType ι0001110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField000111 : typeclass_instances. 
 #[global, program] Instance LocalStateField001000 : LocalStateField ( XAddress * ( XHMap XUInteger256 TradingPairListingRequestLRecord ) ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00100). 
 eapply TransEmbedded. eapply (_ ι001000). 
 eapply (LocalState001000LEmbeddedType ι0010001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00100). 
 eapply TransEmbedded. eapply (_ ι001000). 
 eapply (LocalState001000LEmbeddedType ι0010000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001000 : typeclass_instances. 
 #[global, program] Instance LocalStateField001001 : LocalStateField ( XHMap XUInteger256 TradingPairListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00100). 
 eapply TransEmbedded. eapply (_ ι001001). 
 eapply (LocalState001001LEmbeddedType ι0010011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00100). 
 eapply TransEmbedded. eapply (_ ι001001). 
 eapply (LocalState001001LEmbeddedType ι0010010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001001 : typeclass_instances. 
 #[global, program] Instance LocalStateField001010 : LocalStateField ( XAddress * ( XHMap XUInteger256 XchgPairListingRequestLRecord ) ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00101). 
 eapply TransEmbedded. eapply (_ ι001010). 
 eapply (LocalState001010LEmbeddedType ι0010101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00101). 
 eapply TransEmbedded. eapply (_ ι001010). 
 eapply (LocalState001010LEmbeddedType ι0010100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001010 : typeclass_instances. 
 #[global, program] Instance LocalStateField001011 : LocalStateField ( XHMap XUInteger256 XchgPairListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00101). 
 eapply TransEmbedded. eapply (_ ι001011). 
 eapply (LocalState001011LEmbeddedType ι0010111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0010). 
 eapply TransEmbedded. eapply (_ ι00101). 
 eapply TransEmbedded. eapply (_ ι001011). 
 eapply (LocalState001011LEmbeddedType ι0010110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001011 : typeclass_instances. 
 #[global, program] Instance LocalStateField001100 : LocalStateField ( XAddress * ( XHMap XUInteger256 WrapperListingRequestLRecord ) ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00110). 
 eapply TransEmbedded. eapply (_ ι001100). 
 eapply (LocalState001100LEmbeddedType ι0011001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00110). 
 eapply TransEmbedded. eapply (_ ι001100). 
 eapply (LocalState001100LEmbeddedType ι0011000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001100 : typeclass_instances. 
 #[global, program] Instance LocalStateField001101 : LocalStateField ( XHMap XUInteger256 WrapperListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00110). 
 eapply TransEmbedded. eapply (_ ι001101). 
 eapply (LocalState001101LEmbeddedType ι0011011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00110). 
 eapply TransEmbedded. eapply (_ ι001101). 
 eapply (LocalState001101LEmbeddedType ι0011010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001101 : typeclass_instances. 
 #[global, program] Instance LocalStateField001110 : LocalStateField XAddress.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00111). 
 eapply TransEmbedded. eapply (_ ι001110). 
 eapply (LocalState001110LEmbeddedType ι0011101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00111). 
 eapply TransEmbedded. eapply (_ ι001110). 
 eapply (LocalState001110LEmbeddedType ι0011100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001110 : typeclass_instances. 
 #[global, program] Instance LocalStateField001111 : LocalStateField XSlice.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00111). 
 eapply TransEmbedded. eapply (_ ι001111). 
 eapply (LocalState001111LEmbeddedType ι0011111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι00). 
 eapply TransEmbedded. eapply (_ ι001). 
 eapply TransEmbedded. eapply (_ ι0011). 
 eapply TransEmbedded. eapply (_ ι00111). 
 eapply TransEmbedded. eapply (_ ι001111). 
 eapply (LocalState001111LEmbeddedType ι0011110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField001111 : typeclass_instances. 
 #[global, program] Instance LocalStateField010000 : LocalStateField XBool.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01000). 
 eapply TransEmbedded. eapply (_ ι010000). 
 eapply (LocalState010000LEmbeddedType ι0100001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01000). 
 eapply TransEmbedded. eapply (_ ι010000). 
 eapply (LocalState010000LEmbeddedType ι0100000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010000 : typeclass_instances. 
 #[global, program] Instance LocalStateField010001 : LocalStateField DXchgPairLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01000). 
 eapply TransEmbedded. eapply (_ ι010001). 
 eapply (LocalState010001LEmbeddedType ι0100011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01000). 
 eapply TransEmbedded. eapply (_ ι010001). 
 eapply (LocalState010001LEmbeddedType ι0100010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010001 : typeclass_instances. 
 #[global, program] Instance LocalStateField010010 : LocalStateField DWrapperLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01001). 
 eapply TransEmbedded. eapply (_ ι010010). 
 eapply (LocalState010010LEmbeddedType ι0100101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01001). 
 eapply TransEmbedded. eapply (_ ι010010). 
 eapply (LocalState010010LEmbeddedType ι0100100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010010 : typeclass_instances. 
 #[global, program] Instance LocalStateField010011 : LocalStateField FlexDetailsLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01001). 
 eapply TransEmbedded. eapply (_ ι010011). 
 eapply (LocalState010011LEmbeddedType ι0100111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0100). 
 eapply TransEmbedded. eapply (_ ι01001). 
 eapply TransEmbedded. eapply (_ ι010011). 
 eapply (LocalState010011LEmbeddedType ι0100110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010011 : typeclass_instances. 
 #[global, program] Instance LocalStateField010100 : LocalStateField TonsConfigLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01010). 
 eapply TransEmbedded. eapply (_ ι010100). 
 eapply (LocalState010100LEmbeddedType ι0101001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01010). 
 eapply TransEmbedded. eapply (_ ι010100). 
 eapply (LocalState010100LEmbeddedType ι0101000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010100 : typeclass_instances. 
 #[global, program] Instance LocalStateField010101 : LocalStateField ListingConfigLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01010). 
 eapply TransEmbedded. eapply (_ ι010101). 
 eapply (LocalState010101LEmbeddedType ι0101011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01010). 
 eapply TransEmbedded. eapply (_ ι010101). 
 eapply (LocalState010101LEmbeddedType ι0101010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010101 : typeclass_instances. 
 #[global, program] Instance LocalStateField010110 : LocalStateField Tip3ConfigLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01011). 
 eapply TransEmbedded. eapply (_ ι010110). 
 eapply (LocalState010110LEmbeddedType ι0101101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01011). 
 eapply TransEmbedded. eapply (_ ι010110). 
 eapply (LocalState010110LEmbeddedType ι0101100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010110 : typeclass_instances. 
 #[global, program] Instance LocalStateField010111 : LocalStateField XUInteger8.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01011). 
 eapply TransEmbedded. eapply (_ ι010111). 
 eapply (LocalState010111LEmbeddedType ι0101111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι010). 
 eapply TransEmbedded. eapply (_ ι0101). 
 eapply TransEmbedded. eapply (_ ι01011). 
 eapply TransEmbedded. eapply (_ ι010111). 
 eapply (LocalState010111LEmbeddedType ι0101110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField010111 : typeclass_instances. 
 #[global, program] Instance LocalStateField011000 : LocalStateField FlexOwnershipInfoLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01100). 
 eapply TransEmbedded. eapply (_ ι011000). 
 eapply (LocalState011000LEmbeddedType ι0110001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01100). 
 eapply TransEmbedded. eapply (_ ι011000). 
 eapply (LocalState011000LEmbeddedType ι0110000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011000 : typeclass_instances. 
 #[global, program] Instance LocalStateField011001 : LocalStateField ( XHMap XUInteger WrapperListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01100). 
 eapply TransEmbedded. eapply (_ ι011001). 
 eapply (LocalState011001LEmbeddedType ι0110011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01100). 
 eapply TransEmbedded. eapply (_ ι011001). 
 eapply (LocalState011001LEmbeddedType ι0110010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011001 : typeclass_instances. 
 #[global, program] Instance LocalStateField011010 : LocalStateField ( XHMap XUInteger TradingPairListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01101). 
 eapply TransEmbedded. eapply (_ ι011010). 
 eapply (LocalState011010LEmbeddedType ι0110101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01101). 
 eapply TransEmbedded. eapply (_ ι011010). 
 eapply (LocalState011010LEmbeddedType ι0110100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011010 : typeclass_instances. 
 #[global, program] Instance LocalStateField011011 : LocalStateField ( XHMap XUInteger XchgPairListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01101). 
 eapply TransEmbedded. eapply (_ ι011011). 
 eapply (LocalState011011LEmbeddedType ι0110111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0110). 
 eapply TransEmbedded. eapply (_ ι01101). 
 eapply TransEmbedded. eapply (_ ι011011). 
 eapply (LocalState011011LEmbeddedType ι0110110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011011 : typeclass_instances. 
 #[global, program] Instance LocalStateField011100 : LocalStateField XUInteger.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01110). 
 eapply TransEmbedded. eapply (_ ι011100). 
 eapply (LocalState011100LEmbeddedType ι0111001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01110). 
 eapply TransEmbedded. eapply (_ ι011100). 
 eapply (LocalState011100LEmbeddedType ι0111000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011100 : typeclass_instances. 
 #[global, program] Instance LocalStateField011101 : LocalStateField ( XAddress * XAddress ) (* IWrapperPtrLRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01110). 
 eapply TransEmbedded. eapply (_ ι011101). 
 eapply (LocalState011101LEmbeddedType ι0111011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01110). 
 eapply TransEmbedded. eapply (_ ι011101). 
 eapply (LocalState011101LEmbeddedType ι0111010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011101 : typeclass_instances. 
 #[global, program] Instance LocalStateField011110 : LocalStateField XAddress (* ITONTokenWalletPtrLRecord *).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01111). 
 eapply TransEmbedded. eapply (_ ι011110). 
 eapply (LocalState011110LEmbeddedType ι0111101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01111). 
 eapply TransEmbedded. eapply (_ ι011110). 
 eapply (LocalState011110LEmbeddedType ι0111100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011110 : typeclass_instances. 
 #[global, program] Instance LocalStateField011111 : LocalStateField ( XMaybe WrapperListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01111). 
 eapply TransEmbedded. eapply (_ ι011111). 
 eapply (LocalState011111LEmbeddedType ι0111111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι0). 
 eapply TransEmbedded. eapply (_ ι01). 
 eapply TransEmbedded. eapply (_ ι011). 
 eapply TransEmbedded. eapply (_ ι0111). 
 eapply TransEmbedded. eapply (_ ι01111). 
 eapply TransEmbedded. eapply (_ ι011111). 
 eapply (LocalState011111LEmbeddedType ι0111110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField011111 : typeclass_instances. 
 #[global, program] Instance LocalStateField100000 : LocalStateField ( XMaybe TradingPairListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10000). 
 eapply TransEmbedded. eapply (_ ι100000). 
 eapply (LocalState100000LEmbeddedType ι1000001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10000). 
 eapply TransEmbedded. eapply (_ ι100000). 
 eapply (LocalState100000LEmbeddedType ι1000000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100000 : typeclass_instances. 
 #[global, program] Instance LocalStateField100001 : LocalStateField ( XMaybe XchgPairListingRequestWithPubkeyLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10000). 
 eapply TransEmbedded. eapply (_ ι100001). 
 eapply (LocalState100001LEmbeddedType ι1000011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10000). 
 eapply TransEmbedded. eapply (_ ι100001). 
 eapply (LocalState100001LEmbeddedType ι1000010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100001 : typeclass_instances. 
 #[global, program] Instance LocalStateField100010 : LocalStateField ( XMaybe WrapperListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10001). 
 eapply TransEmbedded. eapply (_ ι100010). 
 eapply (LocalState100010LEmbeddedType ι1000101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10001). 
 eapply TransEmbedded. eapply (_ ι100010). 
 eapply (LocalState100010LEmbeddedType ι1000100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100010 : typeclass_instances. 
 #[global, program] Instance LocalStateField100011 : LocalStateField ( XMaybe TradingPairListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10001). 
 eapply TransEmbedded. eapply (_ ι100011). 
 eapply (LocalState100011LEmbeddedType ι1000111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1000). 
 eapply TransEmbedded. eapply (_ ι10001). 
 eapply TransEmbedded. eapply (_ ι100011). 
 eapply (LocalState100011LEmbeddedType ι1000110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100011 : typeclass_instances. 
 #[global, program] Instance LocalStateField100100 : LocalStateField ( XMaybe XchgPairListingRequestLRecord ).
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10010). 
 eapply TransEmbedded. eapply (_ ι100100). 
 eapply (LocalState100100LEmbeddedType ι1001001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10010). 
 eapply TransEmbedded. eapply (_ ι100100). 
 eapply (LocalState100100LEmbeddedType ι1001000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100100 : typeclass_instances. 
 #[global, program] Instance LocalStateField100101 : LocalStateField WrapperListingRequestWithPubkeyLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10010). 
 eapply TransEmbedded. eapply (_ ι100101). 
 eapply (LocalState100101LEmbeddedType ι1001011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10010). 
 eapply TransEmbedded. eapply (_ ι100101). 
 eapply (LocalState100101LEmbeddedType ι1001010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100101 : typeclass_instances. 
 #[global, program] Instance LocalStateField100110 : LocalStateField TradingPairListingRequestWithPubkeyLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10011). 
 eapply TransEmbedded. eapply (_ ι100110). 
 eapply (LocalState100110LEmbeddedType ι1001101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10011). 
 eapply TransEmbedded. eapply (_ ι100110). 
 eapply (LocalState100110LEmbeddedType ι1001100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100110 : typeclass_instances. 
 #[global, program] Instance LocalStateField100111 : LocalStateField XchgPairListingRequestWithPubkeyLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10011). 
 eapply TransEmbedded. eapply (_ ι100111). 
 eapply (LocalState100111LEmbeddedType ι1001111). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι100). 
 eapply TransEmbedded. eapply (_ ι1001). 
 eapply TransEmbedded. eapply (_ ι10011). 
 eapply TransEmbedded. eapply (_ ι100111). 
 eapply (LocalState100111LEmbeddedType ι1001110). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField100111 : typeclass_instances. 
 #[global, program] Instance LocalStateField101000 : LocalStateField WrapperListingRequestLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι10100). 
 eapply TransEmbedded. eapply (_ ι101000). 
 eapply (LocalState101000LEmbeddedType ι1010001). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι10100). 
 eapply TransEmbedded. eapply (_ ι101000). 
 eapply (LocalState101000LEmbeddedType ι1010000). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField101000 : typeclass_instances. 
 #[global, program] Instance LocalStateField101001 : LocalStateField TradingPairListingRequestLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι10100). 
 eapply TransEmbedded. eapply (_ ι101001). 
 eapply (LocalState101001LEmbeddedType ι1010011). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι10100). 
 eapply TransEmbedded. eapply (_ ι101001). 
 eapply (LocalState101001LEmbeddedType ι1010010). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField101001 : typeclass_instances. 
 #[global, program] Instance LocalStateField101010 : LocalStateField XchgPairListingRequestLRecord.
Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι10101). 
 eapply (LocalState101010LEmbeddedType ι1010101). 
 Defined.
 Next Obligation. 
 eapply TransEmbedded. eapply (_ ι1). 
 eapply TransEmbedded. eapply (_ ι101). 
 eapply TransEmbedded. eapply (_ ι10101). 
 eapply (LocalState101010LEmbeddedType ι1010100). 
 Defined.
 Fail Next Obligation.
#[local]
Remove Hints LocalStateField101010 : typeclass_instances. 






Definition LocalStateField_XUInteger := LocalStateField011100 .
Definition LocalStateField_XBool := LocalStateField010001 .
Definition LocalStateField_XCell := LocalStateField000001 .


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




