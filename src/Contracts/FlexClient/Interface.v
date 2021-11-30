Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import FlexClient.ClassTypes.

Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables address XBool XUInteger256 XUInteger128 XUInteger32 XUInteger8 XCell Tip3ConfigLRecord TonsConfigLRecord: Type.

Inductive VarInitFields      := | VarInit_ι_DFlexClient  | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance (*debug*).

Variable InitialState : Type.

Inductive IFlexClientP :=
| Iconstructor : XUInteger256 -> XCell -> XCell -> IFlexClientP
| IsetFlexCfg   : TonsConfigLRecord -> address -> IFlexClientP
| IsetExtWalletCode : XCell -> IFlexClientP
| IsetFlexWalletCode : XCell -> IFlexClientP
| IsetFlexWrapperCode : XCell -> IFlexClientP
| IdeployPriceWithSell : XUInteger128 -> XUInteger128 -> XUInteger32 -> XUInteger128 -> XUInteger8 -> XUInteger128 -> XCell -> address -> address -> Tip3ConfigLRecord -> address -> IFlexClientP
| IdeployPriceWithBuy : XUInteger128 -> XUInteger128 -> XUInteger32 -> XUInteger128 -> XUInteger8 -> XUInteger128 -> XCell -> address -> Tip3ConfigLRecord -> address -> IFlexClientP
| IdeployPriceXchg : XBool -> XUInteger128 -> XUInteger128 -> XUInteger128 -> XUInteger128 -> XUInteger32 -> XUInteger128 -> XUInteger8 -> XUInteger128 -> XCell -> address -> address -> Tip3ConfigLRecord -> Tip3ConfigLRecord -> address -> IFlexClientP
| IcancelSellOrder : XUInteger128 -> XUInteger128 -> XUInteger8 -> XUInteger128 -> XCell -> Tip3ConfigLRecord -> address -> IFlexClientP
| IcancelBuyOrder : XUInteger128 -> XUInteger128 -> XUInteger8 -> XUInteger128 -> XCell -> Tip3ConfigLRecord -> address -> IFlexClientP
| IcancelXchgOrder : XBool -> XUInteger128 -> XUInteger128 -> XUInteger128 -> XUInteger8 -> XUInteger128 -> XCell -> Tip3ConfigLRecord -> Tip3ConfigLRecord -> address -> IFlexClientP
| Itransfer : address -> XUInteger128 -> XBool -> IFlexClientP
| IregisterWrapper : XUInteger128 -> XUInteger128 -> Tip3ConfigLRecord -> IFlexClientP
| IregisterTradingPair : XUInteger256 -> XUInteger128 -> address -> XUInteger128 -> address -> IFlexClientP
| IregisterXchgPair : XUInteger256 -> XUInteger128 -> address -> address -> address -> XUInteger128 -> address -> IFlexClientP
| IdeployEmptyFlexWallet : XUInteger256 -> XUInteger128 -> Tip3ConfigLRecord -> IFlexClientP
| IburnWallet : XUInteger128 -> XUInteger256 -> address -> address -> IFlexClientP
| IgetOwner : IFlexClientP
| IgetFlex : IFlexClientP
| IhasExtWalletCode : IFlexClientP
| IhasFlexWalletCode : IFlexClientP
| IhasFlexWrapperCode : IFlexClientP
| IgetPayloadForDeployInternalWallet : XUInteger256 -> address -> XUInteger128 -> IFlexClientP
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

Print IFlexClientP.
Definition IFlexClient : Type := IFlexClientP address XBool XUInteger256 XUInteger128 XUInteger32 XUInteger8 XCell Tip3ConfigLRecord TonsConfigLRecord StateInitLRecord.

(* Print Iconstructor. *)

Arguments Iconstructor {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IsetFlexCfg  {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IsetExtWalletCode {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IsetFlexWalletCode {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IsetFlexWrapperCode {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IdeployPriceWithSell {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IdeployPriceWithBuy {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IdeployPriceXchg {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IcancelSellOrder {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IcancelBuyOrder {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IcancelXchgOrder {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments Itransfer {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IregisterWrapper {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IregisterTradingPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IregisterXchgPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IdeployEmptyFlexWallet {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}. 
Arguments IburnWallet {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetOwner {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetFlex {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IhasExtWalletCode {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IhasFlexWalletCode {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IhasFlexWrapperCode {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments IgetPayloadForDeployInternalWallet {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.
Arguments _Icreate {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.

End PublicInterface.

