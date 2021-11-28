Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import Wrapper.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XAddress XUInteger128  XUInteger256   XCell: Type.

Inductive VarInitFields      := | VarInit_ι_DWrapper | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive IWrapperP :=
    | Iinit : XAddress -> IWrapperP
    | IsetInternalWalletCode : XCell -> IWrapperP
    | IdeployEmptyWallet : XUInteger256 -> XAddress -> XUInteger128 -> IWrapperP
    | IonTip3Transfer : XAddress -> XUInteger128 -> XUInteger128 -> XUInteger256 -> 
                                                XAddress -> XCell -> IWrapperP
    | Iburn : XAddress -> XUInteger256 -> XAddress -> XUInteger256 -> 
                                                XAddress -> XUInteger128 -> IWrapperP
    | IhasInternalWalletCode : IWrapperP

    | _Icreate : InitialState -> IWrapperP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [ClassTypesForInterface.DWrapperLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Print IWrapperP. *)
Definition IWrapper: Type := IWrapperP XAddress XUInteger128 XUInteger256 XCell InitialStateLRecord.


Arguments Iinit {_} {_} {_} {_} {_}.
Arguments IsetInternalWalletCode {_} {_} {_} {_} {_}.
Arguments IdeployEmptyWallet {_} {_} {_} {_} {_}.
Arguments IonTip3Transfer {_} {_} {_} {_} {_}.
Arguments Iburn {_} {_} {_} {_} {_}.
Arguments IhasInternalWalletCode {_} {_} {_} {_} {_}.
Arguments _Icreate {_} {_} {_} {_} {_}.

End PublicInterface.

