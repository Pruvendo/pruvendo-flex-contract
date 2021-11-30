Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import XchgPair.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XAddress XUInteger128 : Type.

Inductive VarInitFields      := | VarInit_ι_DXchgPair | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive IXchgPairP :=
    | IonDeploy : XUInteger128 -> XUInteger128 -> XAddress -> IXchgPairP
    | IgetFlexAddr : IXchgPairP
    | IgetTip3MajorRoot : IXchgPairP
    | IgetTip3MinorRoot : IXchgPairP
    | IgetMinAmount : IXchgPairP
    | IgetNotifyAddr : IXchgPairP
    | _Icreate : InitialState -> IXchgPairP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [DXchgPairLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

Definition IXchgPair: Type := IXchgPairP XAddress XUInteger128 (* StateInitLRecord *) StateInitLRecord.

Arguments IonDeploy {_} {_} {_}.
Arguments IgetFlexAddr {_} {_} {_}.
Arguments IgetTip3MajorRoot {_} {_} {_}.
Arguments IgetMinAmount {_} {_} {_}.
Arguments IgetNotifyAddr {_} {_} {_}.
Arguments _Icreate {_} {_} {_}.

End PublicInterface.

