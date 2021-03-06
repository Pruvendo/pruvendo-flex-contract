Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonTypes. 
Require Import PriceXchg.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XUInteger128 XUInteger32 XUInteger256 address cell XBool OrderRet: Type.

Inductive VarInitFields      := | VarInit_ι_DPriceXchg | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive IPriceXchgP :=
| IonTip3LendOwnership : address -> XUInteger128 -> XUInteger32 -> XUInteger256 -> address -> cell -> IPriceXchgP
| IprocessQueue : IPriceXchgP
| IcancelSell : IPriceXchgP
| IcancelBuy : IPriceXchgP
| _Icreate : InitialState -> IPriceXchgP.

Inductive IPriceCallbackP :=
| IonOrderFinished : OrderRet -> XBool -> IPriceCallbackP.


End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [DPriceXchgLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [cell_ ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Print IPriceXchgP.  *)
Definition IPriceXchg : Type := IPriceXchgP XUInteger128 XUInteger32 XUInteger256 address cell StateInitLRecord.

Arguments IonTip3LendOwnership {_} {_} {_} {_} {_} {_} . 
Arguments IprocessQueue {_} {_} {_} {_} {_} {_} . 
Arguments IcancelSell {_} {_} {_} {_} {_} {_} . 
Arguments IcancelBuy {_} {_} {_} {_} {_} {_} . 
Arguments _Icreate {_} {_} {_} {_} {_} {_} . 

Definition IPriceCallBack := IPriceCallbackP XBool OrderRetLRecord.

Arguments IonOrderFinished {_} {_}.

End PublicInterface.

