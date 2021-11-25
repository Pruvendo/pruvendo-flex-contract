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
Require Import Contracts.Wrapper.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.


Variables XAddress XUInteger128 XUInteger32 XUInteger256 XCells InternalMessageParamsLRecord XCell: Type.

Inductive VarInitFields      := | VarInit_ι_DWrapper | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive PublicInterfaceP :=
| Iinit : XAddress -> PublicInterfaceP
| IsetInternalWalletCode : XCell -> PublicInterfaceP
| IdeployEmptyWallet : XUInteger256 -> XAddress -> XUInteger128 -> PublicInterfaceP
| IonTip3Transfer : XAddress -> XUInteger128 -> XUInteger128 -> XUInteger256 -> 
                                              XAddress -> XCell -> PublicInterfaceP
| Iburn : XAddress -> XUInteger256 -> XAddress -> XUInteger256 -> 
                                              XAddress -> XUInteger128 -> PublicInterfaceP
| IhasInternalWalletCode : PublicInterfaceP

| _Icreate : InitialState -> PublicInterfaceP
| _Itransfer : PublicInterfaceP .

Inductive OutgoingMessageP :=
| EmptyMessage : OutgoingMessageP
| OutgoingInternalMessage : XAddress -> InternalMessageParamsLRecord -> PublicInterfaceP -> OutgoingMessageP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).
Module Import VMStateModuleForInterface := VMStateModule xt sm.
(* Module Import BasicTypesForInterface := BasicTypes xt sm. *)
Module Import ClassTypesForInterface := Contracts.Wrapper.ClassTypes.ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [ClassTypesForInterface.DWrapperLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Check (InitState_ι_code _). *)

Print PublicInterfaceP.
Definition PublicInterface : Type := PublicInterfaceP XAddress XUInteger128 XUInteger256 XCell InitialStateLRecord.

Print OutgoingMessageP.
Definition OutgoingMessage : Type := OutgoingMessageP XAddress XUInteger128 XUInteger256 InternalMessageParamsLRecord XCell InitialStateLRecord.

(* Print Iconstructor. *)
Arguments _Icreate {_} {_}.
Arguments Iinit {_}.
Arguments IsetInternalWalletCode {_}.
Arguments IdeployEmptyWallet {_} {_} {_} .
Arguments IonTip3Transfer {_} {_} {_} {_} {_} {_}.
                                             
Arguments Iburn {_} {_} {_} {_} {_} {_}.
Arguments OutgoingInternalMessage {_} {_} {_} {_}.
(* About OutgoingInternalMessage. *)

Global Instance OutgoingMessage_default : XDefault OutgoingMessage :=
{
    default := EmptyMessage XAddress XUInteger128 XUInteger256 InternalMessageParamsLRecord XCell InitialStateLRecord
}.


End PublicInterface.

