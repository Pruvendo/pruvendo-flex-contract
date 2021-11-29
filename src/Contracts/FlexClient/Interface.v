Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import FlexClient.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XAddress XUInteger256 XCell TonsConfigLRecord: Type.

Inductive VarInitFields      := | VarInit_ι_DFlexClient  | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance (*debug*).

Variable InitialState : Type.

Inductive IFlexClientP :=
| Iconstructor : XUInteger256 -> XCell -> XCell -> IFlexClientP
| IsetFlexCfg   : TonsConfigLRecord -> XAddress -> IFlexClientP
| IsetExtWalletCode : XCell -> IFlexClientP
| IsetFlexWalletCode : XCell -> IFlexClientP
| IsetFlexWrapperCode : XCell -> IFlexClientP
| _Icreate : InitialState -> IFlexClientP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [DFlexClientLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Print IFlexClientP. *)
Definition IFlexClient : Type := IFlexClientP XAddress XUInteger256 XCell TonsConfigLRecord StateInitLRecord.

(* Print Iconstructor. *)

Arguments Iconstructor {_} {_} {_} {_} {_}.
Arguments IsetFlexCfg  {_} {_} {_} {_} {_}.
Arguments IsetExtWalletCode {_} {_} {_} {_} {_}.
Arguments IsetFlexWalletCode {_} {_} {_} {_} {_}.
Arguments IsetFlexWrapperCode {_} {_} {_} {_} {_}.
Arguments _Icreate {_} {_} {_} {_} {_}.

End PublicInterface.

