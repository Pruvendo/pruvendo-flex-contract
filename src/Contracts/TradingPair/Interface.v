Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonTypes. 
Require Import TradingPair.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XUInteger128 address: Type.

Inductive VarInitFields      := | VarInit_ι_DTradingPair | VarInit_ι_pubkey. (* = DFlex *)
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance (*debug*).

Variable InitialState : Type.

Inductive ITradingPairP :=
    | IonDeploy : XUInteger128 -> XUInteger128 -> address -> ITradingPairP
    | IgetFlexAddr : ITradingPairP
    | IgetTip3Root : ITradingPairP
    | IgetMinAmount : ITradingPairP
    | IgetNotifyAddr : ITradingPairP
    | _Icreate : InitialState -> ITradingPairP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

Module Import BasicTypesForInterface := BasicTypes xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [DTradingPairLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [cell_ ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Print PublicInterfaceP. *)
Definition ITradingPair : Type := ITradingPairP XUInteger128 address StateInitLRecord.

(* Print Iconstructor. *)
Arguments IonDeploy {_} {_} {_}.
Arguments IgetFlexAddr {_} {_} {_}.
Arguments IgetTip3Root {_} {_} {_}.
Arguments IgetMinAmount {_} {_} {_}.
Arguments IgetNotifyAddr {_} {_} {_}.
Arguments _Icreate {_} {_} {_}.

End PublicInterface.

