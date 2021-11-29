Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import Flex.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables XAddress TonsConfigLRecord XUInteger8 StateInitLRecord
           XCell XUInteger256 XUInteger128 XBool XString ListingConfigLRecord Tip3ConfigLRecord : Type.
Variable XMaybe : Type -> Type .

Inductive VarInitFields      := | VarInit_ι_DFlex | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance (*debug*).

Inductive IFlexP :=
| Iconstructor : XUInteger256 -> XString -> XMaybe XAddress -> TonsConfigLRecord -> 
                                          XUInteger8 -> ListingConfigLRecord -> IFlexP
| IsetSpecificCode : XUInteger8 -> XCell -> IFlexP
| Itransfer : XAddress -> XUInteger128 -> IFlexP
| IregisterTradingPair : XUInteger256 -> XAddress -> XUInteger128 -> XAddress -> IFlexP
| IregisterXchgPair : XUInteger256 -> XAddress -> XAddress -> XUInteger128 -> XAddress -> IFlexP
| IregisterWrapper : XUInteger256 -> Tip3ConfigLRecord -> IFlexP
| IapproveTradingPair : XUInteger256 -> IFlexP
| IrejectTradingPair : XUInteger256 -> IFlexP
| IapproveXchgPair : XUInteger256 -> IFlexP
| IrejectXchgPair : XUInteger256 -> IFlexP
| IapproveWrapper : XUInteger256 -> IFlexP
| IrejectWrapper : XUInteger256 -> IFlexP 

| _Icreate : StateInitLRecord -> IFlexP
(* | _Itransfer : PublicInterfaceP  *).

Inductive IListingAnswerP :=
  | IonWrapperApproved : XUInteger256 -> XAddress -> IListingAnswerP
  | IonWrapperRejected : XUInteger256 -> IListingAnswerP
  | IonTradingPairApproved : XUInteger256 -> XAddress -> IListingAnswerP
  | IonTradingPairRejected : XUInteger256 -> IListingAnswerP
  | IonXchgPairApproved : XUInteger256 -> XAddress -> IListingAnswerP
  | IonXchgPairRejected : XUInteger256 -> IListingAnswerP.

Inductive IFlexNotifyP := 
| IonDealCompleted : XAddress -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonXchgDealCompleted: XAddress -> XAddress ->  XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonOrderAdded : XBool -> XAddress -> XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonOrderCanceled : XBool -> XAddress -> XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonXchgOrderAdded : XBool -> XAddress -> XAddress ->  XUInteger128 -> XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonXchgOrderCanceled : XBool -> XAddress -> XAddress -> XUInteger128 -> XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP  .

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

(* Module Import VMStateModuleForInterface := VMStateModule xt sm. *)
Module Import BasicTypesForInterface := BasicTypes xt sm. 
Module Import ClassTypesForInterface := ClassTypes xt sm.
  
Local Open Scope xlist_scope.

Definition VarInitL := [ DFlexLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Print IFlexP. *)
Definition IFlex : Type := IFlexP XAddress TonsConfigLRecord XUInteger8 StateInitLRecord XCell XUInteger256
     XUInteger128 XString ListingConfigLRecord Tip3ConfigLRecord XMaybe  .

(* __interface IFlex *)
(* Check Iconstructor. *)
Arguments Iconstructor {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IsetSpecificCode {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments Itransfer {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IregisterTradingPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IregisterXchgPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IregisterWrapper {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IapproveTradingPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IrejectTradingPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IapproveXchgPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IrejectXchgPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IapproveWrapper {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IrejectWrapper {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments _Icreate {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.   
(* Check   IregisterXchgPair. *)

(* Print IListingAnswerP. *)
Definition IListingAnswer := IListingAnswerP XAddress XUInteger256.
Arguments IonWrapperApproved {_} {_} .
Arguments IonWrapperRejected {_} {_}.
Arguments IonTradingPairApproved {_} {_}.
Arguments IonTradingPairRejected {_} {_}.
Arguments IonXchgPairApproved {_} {_} .
Arguments IonXchgPairRejected {_} {_}.

(* Check IonWrapperRejected. *)

(* __interface IFlexNotify *)
Print IFlexNotifyP.
Definition IFlexNotify := IFlexNotifyP XAddress XUInteger128 XBool.
Arguments IonDealCompleted {_} {_} {_} .
Arguments IonXchgDealCompleted {_} {_} {_} .
Arguments IonOrderAdded {_} {_} {_} .
Arguments IonOrderCanceled {_} {_} {_}  .
Arguments IonXchgOrderAdded {_} {_} {_} .
Arguments IonXchgOrderCanceled {_} {_} {_} .
(* Check IonOrderCanceled. *)

End PublicInterface.

