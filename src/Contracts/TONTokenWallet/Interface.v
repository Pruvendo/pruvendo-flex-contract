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

Variables XAddress XUInteger128 XUInteger32 XUInteger256 XCell XBool: Type.

Inductive VarInitFields      := | VarInit_ι_DPrice | VarInit_ι_pubkey. 
Inductive InitialStateFields := | InitState_ι_code | InitState_ι_varinit | InitState_ι_balance .

Variable InitialState : Type. 

Inductive ITONTokenWalletNotifyP :=
| IonTip3LendOwnership : XAddress -> XUInteger128 -> XUInteger32 -> XUInteger256 -> XAddress -> XCell -> ITONTokenWalletNotifyP
| IonTip3Transfer : XAddress -> XUInteger128 -> XUInteger128 -> XUInteger256 -> XAddress -> XCell -> ITONTokenWalletNotifyP.

Inductive ITONTokenWalletP :=
| ItransferWithNotify : XAddress -> XAddress -> XUInteger128 -> XUInteger128 -> XBool -> XCell -> ITONTokenWalletP
| ItransferToRecipient : XAddress -> XUInteger256 -> XAddress -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> ITONTokenWalletP
| ItransferToRecipientWithNotify : XAddress -> XUInteger256 -> XAddress -> 
                         XUInteger128 -> XUInteger128 -> XBool -> XBool -> XCell -> ITONTokenWalletP
| IlendOwnership : XAddress -> XUInteger128 -> XUInteger256 -> XUInteger128 -> 
                         XUInteger32 -> XCell -> XCell -> ITONTokenWalletP
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

(* Print ITONTokenWalletNotifyP. *)
Definition ITONTokenWalletNotify : Type := ITONTokenWalletNotifyP XAddress XUInteger128 XUInteger32 XUInteger256 XCell.

Arguments IonTip3LendOwnership {_} {_} {_} {_} {_}.
Arguments IonTip3Transfer {_} {_} {_} {_} {_}.

(* Print ITONTokenWalletP. *)
Definition ITONTokenWallet : Type := ITONTokenWalletP XAddress XUInteger128 XUInteger32 XUInteger256 XCell XBool StateInitLRecord.

Arguments ItransferWithNotify  {_} {_} {_} {_} {_} {_} {_}.
Arguments ItransferToRecipient {_} {_} {_} {_} {_} {_} {_}. 
Arguments ItransferToRecipientWithNotify {_} {_} {_} {_} {_} {_} {_}. 
Arguments IlendOwnership {_} {_} {_} {_} {_} {_} {_} .
Arguments _Icreate {_} {_} {_} {_} {_} {_} {_} .

End PublicInterface.

