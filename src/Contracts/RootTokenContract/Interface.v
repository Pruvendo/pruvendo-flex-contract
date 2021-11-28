Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import RootTokenContract.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XAddress XUInteger128  XUInteger256  XString XUInteger8 : Type.

Inductive VarInitFields      := | VarInit_ι_DRootTokenContract | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive IRootTokenContractP :=
| Iconstructor : XString -> XString -> XUInteger8 -> XUInteger256 -> XAddress -> XUInteger128 -> IRootTokenContractP
| IdeployWallet : XUInteger256 -> XAddress -> XUInteger128 -> XUInteger128 -> IRootTokenContractP
| IdeployEmptyWallet : XUInteger256 -> XAddress -> XUInteger128 -> IRootTokenContractP
| Igrant : XAddress -> XUInteger128 -> XUInteger128 -> IRootTokenContractP
| Imint : XUInteger128 -> IRootTokenContractP
| IrequestTotalGranted : IRootTokenContractP

| _Icreate : InitialState -> IRootTokenContractP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [DRootTokenContractLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Print IRootTokenContractP. *)
Definition IRootTokenContract : Type := IRootTokenContractP XAddress XUInteger128 XUInteger256 XString XUInteger8 InitialStateLRecord .

Arguments Iconstructor {_} {_} {_} {_} {_} {_} .
Arguments IdeployWallet {_} {_} {_} {_} {_} {_}.
Arguments IdeployEmptyWallet {_} {_} {_} {_} {_} {_}.
Arguments Igrant {_} {_} {_} {_} {_} {_}.
Arguments Imint {_} {_} {_} {_} {_} {_}.
Arguments IrequestTotalGranted {_} {_} {_} {_} {_} {_}.
Arguments _Icreate {_} {_} {_} {_} {_} {_}.

End PublicInterface.

