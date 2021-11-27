Require Import Coq.Program.Basics. 

Require Import String. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 

Require Import UMLang.UrsusLib. 
Require Import UMLang.BasicModuleTypes. 
Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UrsusTVM.Cpp.tvmFunc. 

Require Import Project.CommonTypes. 
Require Import Contracts.XchgPair.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XAddress InternalMessageParamsLRecord XUInteger128 : Type.

Inductive VarInitFields      := | VarInit_ι_DXchgPair | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive PublicInterfaceP :=
| IonDeploy : XUInteger128 -> XUInteger128 -> XAddress -> PublicInterfaceP
| _Icreate : InitialState -> PublicInterfaceP
| _Itransfer : PublicInterfaceP .

Inductive OutgoingMessageP :=
| EmptyMessage : OutgoingMessageP
| OutgoingInternalMessage : XAddress -> InternalMessageParamsLRecord -> PublicInterfaceP -> OutgoingMessageP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).
Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [DXchgPairLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Print PublicInterfaceP.  *)
Definition PublicInterface: Type := PublicInterfaceP XAddress XUInteger128 InitialStateLRecord .

(* Print OutgoingMessageP. *)
Definition OutgoingMessage: Type := OutgoingMessageP XAddress InternalMessageParamsLRecord XUInteger128 InitialStateLRecord.

Arguments _Icreate {_} {_} {_}.
Arguments IonDeploy {_} {_} {_}.
Arguments _Itransfer {_} {_} {_}.

Arguments OutgoingInternalMessage {_} {_} {_} {_}.

Global Instance OutgoingMessage_default : XDefault OutgoingMessage :=
{
    default := EmptyMessage XAddress InternalMessageParamsLRecord XUInteger128 InitialStateLRecord
}.


End PublicInterface.

