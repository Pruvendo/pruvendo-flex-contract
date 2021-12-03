Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonTypes. 
Require Import RootTokenContract.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables address cell XUInteger128  XUInteger256  XString XUInteger8 : Type.

Inductive VarInitFields      := | VarInit_ι_DRootTokenContract | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type.

Inductive IRootTokenContractP :=
| Iconstructor : XString -> XString -> XUInteger8 -> XUInteger256 -> address -> XUInteger128 -> IRootTokenContractP
| IsetWalletCode : cell -> IRootTokenContractP
| IdeployWallet : XUInteger256 -> address -> XUInteger128 -> XUInteger128 -> IRootTokenContractP
| IdeployEmptyWallet : XUInteger256 -> address -> XUInteger128 -> IRootTokenContractP
| Igrant : address -> XUInteger128 -> XUInteger128 -> IRootTokenContractP
| Imint : XUInteger128 -> IRootTokenContractP
| IrequestTotalGranted : IRootTokenContractP
| IgetName : IRootTokenContractP
| IgetSymbol : IRootTokenContractP
| IgetDecimals : IRootTokenContractP
| IgetRootKey : IRootTokenContractP
| IgetTotalSupply : IRootTokenContractP
| IgetTotalGranted : IRootTokenContractP
| IhasWalletCode : IRootTokenContractP
| IgetWalletCode : IRootTokenContractP
| IgetWalletCodeHash : IRootTokenContractP
| IgetWalletAddress : XUInteger256 -> address -> IRootTokenContractP
| _Icreate : InitialState -> IRootTokenContractP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [DRootTokenContractLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [cell_ ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

Print IRootTokenContractP.
Definition IRootTokenContract : Type := IRootTokenContractP address cell XUInteger128 XUInteger256 XString XUInteger8 StateInitLRecord .

Arguments Iconstructor {_} {_} {_} {_} {_} {_} {_}.
About Iconstructor.
Arguments IdeployWallet {_} {_} {_} {_} {_} {_} {_}.
Arguments IdeployEmptyWallet {_} {_} {_} {_} {_} {_} {_}.
Arguments Igrant {_} {_} {_} {_} {_} {_} {_}.
Arguments Imint {_} {_} {_} {_} {_} {_} {_}.
Arguments IrequestTotalGranted {_} {_} {_} {_} {_} {_} {_}.
Arguments IsetWalletCode {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetName {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetSymbol {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetDecimals {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetRootKey {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetTotalSupply {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetTotalGranted {_} {_} {_} {_} {_} {_} {_}.
Arguments IhasWalletCode {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetWalletCode {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetWalletCodeHash {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetWalletAddress {_} {_} {_} {_} {_} {_} {_}.
Arguments _Icreate {_} {_} {_} {_} {_} {_} {_}.

End PublicInterface.

