Require Import FinProof.Common. 

Require Import UMLang.LocalClassGenerator.ClassGenerator.
Require Import UMLang.BasicModuleTypes. 

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonTypes. 
Require Import TONTokenWallet.ClassTypes.

(* Local Open Scope record.  *)
Local Open Scope program_scope.
Local Open Scope glist_scope. 

Section InterfaceDef.

Variables address XUInteger128 XUInteger32 XUInteger256 XCell XBool: Type.

Inductive VarInitFields      := | VarInit_ι_DPrice | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type. 

Inductive ITONTokenWalletNotifyP :=
| IonTip3LendOwnership : address -> XUInteger128 -> XUInteger32 -> XUInteger256 -> address -> XCell -> ITONTokenWalletNotifyP
| IonTip3Transfer : address -> XUInteger128 -> XUInteger128 -> XUInteger256 -> address -> XCell -> ITONTokenWalletNotifyP
| _IcreateNotify : InitialState -> ITONTokenWalletNotifyP.


Inductive ITONTokenWalletP :=
| Itransfer : address -> address -> XUInteger128 -> XUInteger128 -> XBool -> ITONTokenWalletP
| ItransferWithNotify : address -> address -> XUInteger128 -> XUInteger128 -> XBool -> XCell -> ITONTokenWalletP
| ItransferToRecipient : address -> XUInteger256 -> address -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> ITONTokenWalletP
| ItransferToRecipientWithNotify : address -> XUInteger256 -> address -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> XCell -> ITONTokenWalletP
| IrequestBalance : ITONTokenWalletP
| Iaccept : XUInteger128 -> address -> XUInteger128 -> ITONTokenWalletP
| IinternalTransfer : XUInteger128 -> address -> XUInteger256 -> address -> XBool -> XCell -> ITONTokenWalletP
| Idestroy : address -> ITONTokenWalletP
| Iburn : XUInteger256 -> address -> ITONTokenWalletP 
| IlendOwnership : address -> XUInteger128 -> XUInteger256 -> XUInteger128 -> 
                         XUInteger32 -> XCell -> XCell -> ITONTokenWalletP
| IreturnOwnership : XUInteger128 -> ITONTokenWalletP
| IgetDetails : ITONTokenWalletP
| IgetBalance : ITONTokenWalletP
| Iapprove : address -> XUInteger128 -> XUInteger128 -> ITONTokenWalletP
| ItransferFrom : address -> address -> XUInteger128 -> XBool -> XCell -> ITONTokenWalletP
| ItransferFromWithNotify : address -> address -> address -> XUInteger128 -> XCell -> ITONTokenWalletP
| IinternalTransferFrom : address -> address -> XUInteger128 -> XBool -> XCell -> ITONTokenWalletP
| Idisapprove : ITONTokenWalletP
| _Icreate : InitialState -> ITONTokenWalletP.

End InterfaceDef.

Module PublicInterface (xt: XTypesSig) (sm: StateMonadSig).

Module Import VMStateModuleForInterface := VMStateModule xt sm.
Module Import ClassTypesForInterface := ClassTypes xt sm.

Local Open Scope xlist_scope.

Definition VarInitL := [XUInteger : Type; XUInteger256: Type].
GeneratePruvendoRecord VarInitL VarInitFields.

Definition InitialStateL := [XCell ; VarInitLRecord ; XUInteger128: Type].
GeneratePruvendoRecord InitialStateL InitialStateFields.

(* Check (InitState_ι_code _). *)

Print ITONTokenWalletNotifyP.
Definition ITONTokenWalletNotify : Type := ITONTokenWalletNotifyP address XUInteger128 XUInteger32 XUInteger256 XCell StateInitLRecord.

Arguments IonTip3LendOwnership {_} {_} {_} {_} {_} {_}.
Arguments IonTip3Transfer {_} {_} {_} {_} {_} {_}.
Arguments _IcreateNotify {_} {_} {_} {_} {_} {_} .

(* Print ITONTokenWalletP. *)
Definition ITONTokenWallet : Type := ITONTokenWalletP address XUInteger128 XUInteger32 XUInteger256 XCell XBool StateInitLRecord.

Arguments ItransferWithNotify  {_} {_} {_} {_} {_} {_} {_}.
Arguments ItransferToRecipient {_} {_} {_} {_} {_} {_} {_}. 
Arguments ItransferToRecipientWithNotify {_} {_} {_} {_} {_} {_} {_}. 
Arguments IlendOwnership {_} {_} {_} {_} {_} {_} {_} .
Arguments Itransfer {_} {_} {_} {_} {_} {_} {_} .
Arguments IrequestBalance {_} {_} {_} {_} {_} {_} {_} .
Arguments Iaccept {_} {_} {_} {_} {_} {_} {_} .
Arguments IinternalTransfer {_} {_} {_} {_} {_} {_} {_} .
Arguments Idestroy {_} {_} {_} {_} {_} {_} {_} .
Arguments Iburn {_} {_} {_} {_} {_} {_} {_} .
Arguments IlendOwnership {_} {_} {_} {_} {_} {_} {_} .
Arguments IreturnOwnership {_} {_} {_} {_} {_} {_} {_} .
Arguments IgetDetails {_} {_} {_} {_} {_} {_} {_} .
Arguments IgetBalance {_} {_} {_} {_} {_} {_} {_} .
Arguments Iapprove {_} {_} {_} {_} {_} {_} {_} .
Arguments ItransferFrom {_} {_} {_} {_} {_} {_} {_} .
Arguments ItransferFromWithNotify {_} {_} {_} {_} {_} {_} {_} .
Arguments IinternalTransferFrom {_} {_} {_} {_} {_} {_} {_} .
Arguments Idisapprove {_} {_} {_} {_} {_} {_} {_} .
Arguments _Icreate {_} {_} {_} {_} {_} {_} {_} .


End PublicInterface.

