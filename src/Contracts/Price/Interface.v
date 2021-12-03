Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonTypes. 
Require Import Price.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables address XUInteger128 XUInteger32 XUInteger256 cell XBool OrderRet: Type.

Inductive VarInitFields      := | VarInit_ι_DPrice | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive IPriceP :=
| IonTip3LendOwnership : address -> XUInteger128 -> XUInteger32 -> XUInteger256 -> address -> cell -> IPriceP
| IbuyTip3 : XUInteger128 -> address -> XUInteger32 -> IPriceP
| IprocessQueue : IPriceP
| IcancelSell : IPriceP
| IcancelBuy : IPriceP
| _Icreate : InitialState -> IPriceP.

Inductive IPriceCallbackP :=
| IonOrderFinished : OrderRet -> XBool -> IPriceCallbackP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [XUInteger : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [cell_ ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

Definition IPrice : Type := IPriceP address XUInteger128 XUInteger32 XUInteger256 cell StateInitLRecord.

Arguments IonTip3LendOwnership {_} {_} {_} {_} {_} {_} .
Arguments IbuyTip3 {_} {_} {_} {_} {_} {_} .
Arguments IprocessQueue  {_} {_} {_} {_} {_} {_}.
Arguments IcancelSell {_} {_} {_} {_} {_} {_}.
Arguments IcancelBuy {_} {_} {_} {_} {_} {_}.
Arguments _Icreate {_} {_} {_} {_} {_} {_} .

Definition IPriceCallback := IPriceCallbackP XBool OrderRetLRecord.

Arguments IonOrderFinished {_} {_}.


End PublicInterface.

