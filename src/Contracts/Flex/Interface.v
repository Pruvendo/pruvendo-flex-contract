Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonTypes. 
Require Import Flex.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables address TonsConfigLRecord XUInteger8 StateInitLRecord
           cell XUInteger256 XUInteger128 XBool XString ListingConfigLRecord Tip3ConfigLRecord : Type.
Variable XMaybe : Type -> Type .

Inductive VarInitFields      := | VarInit_ι_DFlex | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance (*debug*).

Inductive IFlexP :=
| Iconstructor : XUInteger256 -> XString -> XMaybe address -> TonsConfigLRecord -> 
                                          XUInteger8 -> ListingConfigLRecord -> IFlexP
| IsetSpecificCode : XUInteger8 -> cell -> IFlexP
| Itransfer : address -> XUInteger128 -> IFlexP
| IregisterTradingPair : XUInteger256 -> address -> XUInteger128 -> address -> IFlexP
| IregisterXchgPair : XUInteger256 -> address -> address -> XUInteger128 -> address -> IFlexP
| IregisterWrapper : XUInteger256 -> Tip3ConfigLRecord -> IFlexP
| IapproveTradingPair : XUInteger256 -> IFlexP
| IrejectTradingPair : XUInteger256 -> IFlexP
| IapproveXchgPair : XUInteger256 -> IFlexP
| IrejectXchgPair : XUInteger256 -> IFlexP
| IapproveWrapper : XUInteger256 -> IFlexP
| IrejectWrapper : XUInteger256 -> IFlexP
| IisFullyInitialized : IFlexP
| IgetDetails : IFlexP
| IgetSellPriceCode : address -> IFlexP
| IgetXchgPriceCode : address -> address ->  IFlexP
| IgetSellTradingPair : address -> IFlexP
| IgetXchgTradingPair : address -> address -> IFlexP
| _Icreate : StateInitLRecord -> IFlexP
(* | _Itransfer : PublicInterfaceP  *).

Inductive IListingAnswerP :=
  | IonWrapperApproved : XUInteger256 -> address -> IListingAnswerP
  | IonWrapperRejected : XUInteger256 -> IListingAnswerP
  | IonTradingPairApproved : XUInteger256 -> address -> IListingAnswerP
  | IonTradingPairRejected : XUInteger256 -> IListingAnswerP
  | IonXchgPairApproved : XUInteger256 -> address -> IListingAnswerP
  | IonXchgPairRejected : XUInteger256 -> IListingAnswerP.

Inductive IFlexNotifyP := 
| IonDealCompleted : address -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonXchgDealCompleted: address -> address ->  XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonOrderAdded : XBool -> address -> XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonOrderCanceled : XBool -> address -> XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonXchgOrderAdded : XBool -> address -> address ->  XUInteger128 -> XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP
| IonXchgOrderCanceled : XBool -> address -> address -> XUInteger128 -> XUInteger128 -> XUInteger128 -> XUInteger128 -> IFlexNotifyP  .

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

(* Module Import VMStateModuleForInterface := VMStateModule xt sm. *)
Module Import BasicTypesForInterface := BasicTypes xt sm. 
Module Import ClassTypesForInterface := ClassTypes xt sm.
  
Local Open Scope xlist_scope.

Definition VarInitL := [ DFlexLRecord : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [cell_ ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Print IFlexP. *)
Definition IFlex : Type := IFlexP address TonsConfigLRecord XUInteger8 StateInitLRecord cell XUInteger256
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
Arguments IisFullyInitialized {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IgetDetails {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IgetSellPriceCode {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IgetXchgPriceCode {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IgetSellTradingPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IgetXchgTradingPair {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments IrejectWrapper {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} .
Arguments _Icreate {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}.   
(* Check   IregisterXchgPair. *)

(* Print IListingAnswerP. *)
Definition IListingAnswer := IListingAnswerP address XUInteger256.
Arguments IonWrapperApproved {_} {_} .
Arguments IonWrapperRejected {_} {_}.
Arguments IonTradingPairApproved {_} {_}.
Arguments IonTradingPairRejected {_} {_}.
Arguments IonXchgPairApproved {_} {_} .
Arguments IonXchgPairRejected {_} {_}.

(* Check IonWrapperRejected. *)

(* __interface IFlexNotify *)
Print IFlexNotifyP.
Definition IFlexNotify := IFlexNotifyP address XUInteger128 XBool.
Arguments IonDealCompleted {_} {_} {_} .
Arguments IonXchgDealCompleted {_} {_} {_} .
Arguments IonOrderAdded {_} {_} {_} .
Arguments IonOrderCanceled {_} {_} {_}  .
Arguments IonXchgOrderAdded {_} {_} {_} .
Arguments IonXchgOrderCanceled {_} {_} {_} .
(* Check IonOrderCanceled. *)

End PublicInterface.

