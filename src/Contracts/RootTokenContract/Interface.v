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
Require Import Contracts.RootTokenContract.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.


Variables XAddress XUInteger128 XUInteger32 XUInteger256 XCells XString XUInteger8
             InternalMessageParamsLRecord XCell: Type.

Inductive VarInitFields      := | VarInit_ι_DRootTokenContract | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive PublicInterfaceP :=
| Iconstructor : XString -> XString -> XUInteger8 -> XUInteger256 -> XAddress -> XUInteger128 -> PublicInterfaceP
| IdeployWallet : XUInteger256 -> XAddress -> XUInteger128 -> XUInteger128 -> PublicInterfaceP
| IdeployEmptyWallet : XUInteger256 -> XAddress -> XUInteger128 -> PublicInterfaceP
| Igrant : XAddress -> XUInteger128 -> XUInteger128 -> PublicInterfaceP
| Imint : XUInteger128 -> PublicInterfaceP
| IrequestTotalGranted : PublicInterfaceP

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

Definition VarInitL := [DRootTokenContractLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Check (InitState_ι_code _). *)

Print PublicInterfaceP.
Definition PublicInterface : Type := PublicInterfaceP XAddress XUInteger128 XUInteger256 XString XUInteger8 InitialStateLRecord .

Print OutgoingMessageP.
Definition OutgoingMessage : Type := OutgoingMessageP XAddress XUInteger128 XUInteger256 XString XUInteger8 InternalMessageParamsLRecord InitialStateLRecord.

(* Print Iconstructor. *)
Arguments Iconstructor {_} {_} {_} {_} {_} {_} .
Arguments IdeployWallet {_} {_} {_} {_}.
Arguments IdeployEmptyWallet {_} {_} {_}.
Arguments Igrant {_} {_} {_}.
Arguments Imint {_}.
Arguments _Icreate {_} {_}.
Arguments OutgoingInternalMessage {_} {_} {_} {_}.
(* About OutgoingInternalMessage. *)

Global Instance OutgoingMessage_default : XDefault OutgoingMessage :=
{
    default := EmptyMessage XAddress XUInteger128 XUInteger256 XString XUInteger8 InternalMessageParamsLRecord InitialStateLRecord
}.


End PublicInterface.

