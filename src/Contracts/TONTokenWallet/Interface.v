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
Require Import Contracts.TONTokenWallet.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.


Variables XAddress XUInteger128 XUInteger32 XUInteger256 XCells InternalMessageParamsLRecord XCell: Type.

Inductive VarInitFields      := | VarInit_ι_DPrice | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive PublicInterfaceP :=
(* __interface ITONTokenWalletNotify *)
| IonTip3LendOwnership : XAddress -> XUInteger128 -> XUInteger32 -> XUInteger256 -> XAddress -> XCells -> PublicInterfaceP
| IonTip3Transfer : XAddress -> XUInteger128 -> XUInteger128 -> XUInteger256 -> XAddress -> XCells -> PublicInterfaceP

(* __interface ITONTokenWallet *)
| ItransferWithNotify : XAddress -> XAddress -> XUInteger128 -> XUInteger128 -> XBool -> XCell -> PublicInterfaceP
| ItransferToRecipient : XAddress -> XUInteger256 -> XAddress -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> PublicInterfaceP
| ItransferToRecipientWithNotify : XAddress -> XUInteger256 -> XAddress -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> XCell -> PublicInterfaceP
| IlendOwnership : XAddress -> XUInteger128 -> XUInteger256 -> XUInteger128 -> 
                         XUInteger32 -> XCell -> XCell -> PublicInterfaceP

| _Icreate : InitialState -> PublicInterfaceP
| _Itransfer : PublicInterfaceP .

Inductive OutgoingMessageP :=
| EmptyMessage : OutgoingMessageP
| OutgoingInternalMessage : XAddress -> InternalMessageParamsLRecord -> PublicInterfaceP -> OutgoingMessageP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).
Module Import VMStateModuleForInterface := VMStateModule xt sm.
(* Module Import BasicTypesForInterface := BasicTypes xt sm. *)
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [XUInteger : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Check (InitState_ι_code _). *)

(* Print PublicInterfaceP. *)
Definition PublicInterface : Type := PublicInterfaceP XUInteger32 XUInteger128 XUInteger256 XAddress XCell InitialStateLRecord.

(* Print OutgoingMessageP. *)
Definition OutgoingMessage : Type := OutgoingMessageP XUInteger32 XUInteger128 XUInteger256 XAddress XCell InternalMessageParamsLRecord InitialStateLRecord.

(* Print Iconstructor. *)
Arguments _Icreate {_} {_}.
Arguments Iconstructor {_} {_}.
Arguments Ideploy {_} {_}.
Arguments OutgoingInternalMessage {_} {_} {_} {_}.
(* About OutgoingInternalMessage. *)

Global Instance OutgoingMessage_default : XDefault OutgoingMessage :=
{
    default := EmptyMessage XUInteger32 XUInteger128 XUInteger256 XAddress XCell InternalMessageParamsLRecord InitialStateLRecord
}.


End PublicInterface.

