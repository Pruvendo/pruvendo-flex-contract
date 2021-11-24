Require Import Coq.Program.Basics. 

Require Import String. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 

(* Require Import FinProof.ProgrammingWith.   *)
Require Import UMLang.UrsusLib. 
Require Import UMLang.BasicModuleTypes. 
Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UrsusTVM.Cpp.tvmFunc. 

Require Import Project.CommonTypes. 
Require Import Contracts.Flex.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XUInteger XAddress InternalMessageParamsLRecord TonsConfigLRecord XUInteger8 InitialState
           XCell XUInteger256 XUInteger128 XBool XString ListingConfigLRecord Tip3ConfigLRecord : Type.
Variable XMaybe : Type -> Type .

Inductive VarInitFields      := | VarInit_ι_DFlex | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance (*debug*).

Inductive PublicInterfaceP :=
(* __interface IListingAnswer *)
| onWrapperApproved : XUInteger256 -> XAddress -> PublicInterfaceP
| onWrapperRejected : XUInteger256 -> PublicInterfaceP
| onTradingPairApproved : XUInteger256 -> XAddress -> PublicInterfaceP
| onTradingPairRejected : XUInteger256 -> PublicInterfaceP
| onXchgPairApproved : XUInteger256 -> XAddress -> PublicInterfaceP
| onXchgPairRejected : XUInteger256 -> PublicInterfaceP

(* __interface IFlexNotify *)
| IonDealCompleted : XAddress -> XUInteger128 -> XUInteger128 -> PublicInterfaceP
| IonXchgDealCompleted: XAddress -> XAddress ->  XUInteger128 -> XUInteger128 -> XUInteger128 -> PublicInterfaceP
| IonOrderAdded : XBool -> XAddress -> XUInteger128 -> XUInteger128 -> XUInteger128 -> PublicInterfaceP
| IonOrderCanceled : XBool -> XAddress -> XUInteger128 -> XUInteger128 -> XUInteger128 -> PublicInterfaceP
| IonXchgOrderAdded : XBool -> XAddress -> XAddress -> 
                     XUInteger128 -> XUInteger128 -> XUInteger128 -> XUInteger128 -> PublicInterfaceP
| IonXchgOrderCanceled : XBool -> XAddress -> XAddress -> 
                     XUInteger128 -> XUInteger128 -> XUInteger128 -> XUInteger128 -> PublicInterfaceP

(* __interface IFlex *)
| Iconstructor : XUInteger256 -> XString -> XMaybe XAddress -> TonsConfigLRecord -> 
                                          XUInteger8 -> ListingConfigLRecord -> PublicInterfaceP
| IsetSpecificCode : XUInteger8 -> XCell -> PublicInterfaceP
| Itransfer : XAddress -> XUInteger128 -> PublicInterfaceP
| IregisterTradingPair : XUInteger256 -> XAddress -> XUInteger128 -> XAddress -> PublicInterfaceP
| IregisterXchgPair : XUInteger256 -> XAddress -> XAddress -> XUInteger128 -> XAddress -> PublicInterfaceP
| IregisterWrapper : XUInteger256 -> Tip3ConfigLRecord -> PublicInterfaceP
| IapproveTradingPair : XUInteger256 -> PublicInterfaceP
| IrejectTradingPair : XUInteger256 -> PublicInterfaceP
| IapproveXchgPair : XUInteger256 -> PublicInterfaceP
| IrejectXchgPair : XUInteger256 -> PublicInterfaceP
| IapproveWrapper : XUInteger256 -> PublicInterfaceP
| IrejectWrapper : XUInteger256 -> PublicInterfaceP 

| _Icreate : InitialState -> PublicInterfaceP
| _Itransfer : PublicInterfaceP .

Inductive OutgoingMessageP :=
| EmptyMessage : OutgoingMessageP
| OutgoingInternalMessage : XAddress -> InternalMessageParamsLRecord -> PublicInterfaceP -> OutgoingMessageP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).
Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import BasicTypesForInterface := BasicTypes xt sm. 
Module Import ClassTypesForInterface := ClassTypes xt sm.
  
Local Open Scope xlist_scope.

Definition VarInitL := [ DFlexLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Check (InitState_ι_code _). *)  

Print PublicInterfaceP.
Definition PublicInterface : Type
:= PublicInterfaceP XAddress TonsConfigLRecord
     XUInteger8
     InitialStateLRecord XCell
     XUInteger256
     XUInteger128 XBool
     XString ListingConfigLRecord
     Tip3ConfigLRecord XMaybe  .

Print OutgoingMessageP.
Definition OutgoingMessage : Type := OutgoingMessageP XAddress InternalMessageParamsLRecord 
 TonsConfigLRecord XUInteger8 InitialStateLRecord XCell XUInteger256 XUInteger128 XBool XString
     ListingConfigLRecord Tip3ConfigLRecord XMaybe.

(* Print Iconstructor. *)
Arguments onWrapperApproved {_} {_} .
Arguments onWrapperRejected {_}.
Arguments onTradingPairApproved {_} {_}.
Arguments onTradingPairRejected {_} .
Arguments onXchgPairApproved {_} {_} .
Arguments onXchgPairRejected {_} .

(* __interface IFlexNotify *)
Arguments IonDealCompleted {_} {_} {_} .
Arguments IonXchgDealCompleted {_} {_} {_} {_} {_} .
Arguments IonOrderAdded {_} {_} {_} {_} {_} .
Arguments IonOrderCanceled {_} {_} {_} {_} {_} .
Arguments IonXchgOrderAdded {_} {_} {_} {_} {_} {_} {_} .
Arguments IonXchgOrderCanceled {_} {_} {_} {_} {_} {_} {_} .

(* __interface IFlex *)
Arguments Iconstructor {_} {_} {_} {_} {_} {_} .
Arguments IsetSpecificCode {_} {_} .
Arguments Itransfer {_} {_} .
Arguments IregisterTradingPair {_} {_} {_} {_} .
Arguments IregisterXchgPair {_} {_} {_} {_} {_} .
Arguments IregisterWrapper {_} {_} .
Arguments IapproveTradingPair {_} .
Arguments IrejectTradingPair {_} .
Arguments IapproveXchgPair {_} .
Arguments IrejectXchgPair {_} .
Arguments IapproveWrapper {_} .
Arguments IrejectWrapper {_} .

Arguments _Icreate {_} {_}.
Arguments OutgoingInternalMessage {_} {_} {_} {_}.
(* About OutgoingInternalMessage. *)

Global Instance OutgoingMessage_default : XDefault OutgoingMessage :=
{
    default := EmptyMessage XAddress InternalMessageParamsLRecord 
 TonsConfigLRecord XUInteger8 InitialStateLRecord XCell XUInteger256 XUInteger128 XBool XString
     ListingConfigLRecord Tip3ConfigLRecord XMaybe
}.


End PublicInterface.

