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
Require Import Contracts.PriceXchg.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.


Variables XUInteger XAddress InternalMessageParamsLRecord XCell: Type.

Inductive VarInitFields      := | VarInit_ι_value | VarInit_ι_parent | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive PublicInterfaceP :=
| _Icreate : InitialState -> PublicInterfaceP
| Iconstructor : XUInteger -> PublicInterfaceP
| Ideploy : XUInteger -> PublicInterfaceP.

Inductive OutgoingMessageP :=
| EmptyMessage : OutgoingMessageP
| OutgoingInternalMessage : XAddress -> InternalMessageParamsLRecord -> PublicInterfaceP -> OutgoingMessageP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).
Module Import VMStateModuleForInterface := VMStateModule xt sm.
(* Module Import BasicTypesForInterface := BasicTypes xt sm. *)
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [XUInteger : Type; XAddress : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Check (InitState_ι_code _). *)

(* Print PublicInterfaceP. *)
Definition PublicInterface : Type := PublicInterfaceP XUInteger InitialStateLRecord.

(* Print OutgoingMessageP. *)
Definition OutgoingMessage : Type := OutgoingMessageP XUInteger XAddress InternalMessageParamsLRecord InitialStateLRecord.

(* Print Iconstructor. *)
Arguments _Icreate {_} {_}.
Arguments Iconstructor {_} {_}.
Arguments Ideploy {_} {_}.
Arguments OutgoingInternalMessage {_} {_} {_} {_}.
(* About OutgoingInternalMessage. *)

Global Instance OutgoingMessage_default : XDefault OutgoingMessage :=
{
    default := EmptyMessage XUInteger XAddress InternalMessageParamsLRecord InitialStateLRecord
}.


End PublicInterface.

