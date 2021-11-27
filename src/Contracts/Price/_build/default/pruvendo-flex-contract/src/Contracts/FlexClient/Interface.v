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
Require Import Contracts.FlexClient.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XUInteger XAddress XUInteger256 InternalMessageParamsLRecord XCell TonsConfigLRecord: Type.

Inductive VarInitFields      := | VarInit_ι_DFlexClient  | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance (*debug*).

Variable InitialState : Type.

Inductive PublicInterfaceP :=
| Iconstructor : XUInteger256 -> XCell -> XCell -> PublicInterfaceP
| IsetFlexCfg   : TonsConfigLRecord -> XAddress -> PublicInterfaceP
| IsetExtWalletCode : XCell -> PublicInterfaceP
| IsetFlexWalletCode : XCell -> PublicInterfaceP
| IsetFlexWrapperCode : XCell -> PublicInterfaceP

| _Icreate : InitialState -> PublicInterfaceP
| _Itransfer : PublicInterfaceP .

Inductive OutgoingMessageP :=
| EmptyMessage : OutgoingMessageP
| OutgoingInternalMessage : XAddress -> InternalMessageParamsLRecord -> PublicInterfaceP -> OutgoingMessageP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).
Module Import VMStateModuleForInterface := VMStateModule xt sm.
(* Module Import BasicTypesForInterface := BasicTypes xt sm. *)
Module Import ClassTypesForInterface := Contracts.FlexClient.ClassTypes.ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [DFlexClientLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Check (InitState_ι_code _). *)

(* Print PublicInterfaceP. *)
Definition PublicInterface : Type := PublicInterfaceP XUInteger128 XUInteger256 XCell XAddress InitialStateLRecord.

(* Print OutgoingMessageP. *)
Definition OutgoingMessage : Type := OutgoingMessageP XUInteger128 XUInteger256 XCell XAddress InternalMessageParamsLRecord InitialStateLRecord.

(* Print Iconstructor. *)
Arguments _Icreate {_} {_}.
Arguments Iconstructor {_} {_} {_}.
Arguments IsetFlexCfg  {_} {_}.
Arguments IsetExtWalletCode {_}.
Arguments IsetFlexWalletCode {_}.
Arguments IsetFlexWrapperCode {_}.

Arguments OutgoingInternalMessage {_} {_} {_} {_}.
(* About OutgoingInternalMessage. *)

Global Instance OutgoingMessage_default : XDefault OutgoingMessage :=
{
    default := EmptyMessage XUInteger128 XUInteger256 XCell XAddress InternalMessageParamsLRecord InitialStateLRecord
}.


End PublicInterface.

