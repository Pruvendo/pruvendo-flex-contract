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

Variables XUInteger XAddress InternalMessageParamsLRecord XCell: Type.

Inductive VarInitFields      := | VarInit_ι_DFlex | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance (*debug*).

Variable InitialState : Type.

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
| Iconstructor : XInteger256 -> XString -> XMaybe XAddress -> TonsConfig -> 
                                          XInteger8 -> ListingConfig -> PublicInterfaceP
| IsetSpecificCode : XInteger8 -> XCell -> PublicInterfaceP
| Itransfer XAddress -> XInteger128 -> PublicInterfaceP
| IregisterTradingPair : XInteger256 -> XAddress -> XInteger128 -> XAddress -> PublicInterfaceP
| IregisterXchgPair : XInteger256 -> XAddress -> XAddress -> XInteger128 -> XAddress -> PublicInterfaceP
| IregisterWrapper : XInteger256 -> Tip3Config -> PublicInterfaceP
| IapproveTradingPair : XInteger256 -> PublicInterfaceP
| IrejectTradingPair : XInteger256 -> PublicInterfaceP
| IapproveXchgPair : XInteger256 -> PublicInterfaceP
| IrejectXchgPair : XInteger256 -> PublicInterfaceP
| IapproveWrapper : XInteger256 -> PublicInterfaceP
| IrejectWrapper : XInteger256 -> PublicInterfaceP 

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

Definition VarInitL := [DFlex : Type; XInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Check (InitState_ι_code _). *)

(* Print PublicInterfaceP. *)
Definition PublicInterface : Type := PublicInterfaceP XUInteger8 XUInteger128 XUInteger256 XBool XAddress InitialStateLRecord.

(* Print OutgoingMessageP. *)
Definition OutgoingMessage : Type := OutgoingMessageP XUInteger8 XUInteger128 XUInteger256 XBool XAddress InternalMessageParamsLRecord InitialStateLRecord.

(* Print Iconstructor. *)
Arguments _Icreate {_} {_}.
Arguments Iconstructor {_} {_}.
Arguments Ideploy {_} {_}.
Arguments OutgoingInternalMessage {_} {_} {_} {_}.
(* About OutgoingInternalMessage. *)

Global Instance OutgoingMessage_default : XDefault OutgoingMessage :=
{
    default := EmptyMessage XUInteger8 XUInteger128 XUInteger256 XBool XAddress InternalMessageParamsLRecord InitialStateLRecord
}.


End PublicInterface.

