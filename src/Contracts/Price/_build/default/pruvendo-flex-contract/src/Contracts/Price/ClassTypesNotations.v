Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Price.ClassTypes.

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

(********************************************************************)
(*dealer*)

Definition dealer_sells_amount__right {b} (x: URValue dealerLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {dealer_ι_sells_amount_} || : _.

Definition dealer_sells_amount__left (x: ULValue dealerLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {dealer_ι_sells_amount_} }} : _.

Notation " a '↑' 'dealer.sells_amount_' " := (dealer_sells_amount__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.sells_amount_' " := (dealer_sells_amount__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition dealer_sells__right {b} (x: URValue dealerLRecord b): URValue (XQueue OrderInfoLRecord) b :=
|| {x} ^^ {dealer_ι_sells_} || : _.

Definition dealer_sells__left (x: ULValue dealerLRecord): ULValue (XQueue OrderInfoLRecord) :=
{{ {x} ^^ {dealer_ι_sells_} }} : _.

Notation " a '↑' 'dealer.sells_' " := (dealer_sells__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.sells_' " := (dealer_sells__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition dealer_buys_amount__right {b} (x: URValue dealerLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {dealer_ι_buys_amount_} || : _.

Definition dealer_buys_amount__left (x: ULValue dealerLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {dealer_ι_buys_amount_} }} : _.

Notation " a '↑' 'dealer.buys_amount_' " := (dealer_buys_amount__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.buys_amount_' " := (dealer_buys_amount__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition dealer_buys__right {b} (x: URValue dealerLRecord b): URValue (XQueue OrderInfoLRecord) b :=
|| {x} ^^ {dealer_ι_buys_} || : _.

Definition dealer_buys__left (x: ULValue dealerLRecord): ULValue (XQueue OrderInfoLRecord) :=
{{ {x} ^^ {dealer_ι_buys_} }} : _.

Notation " a '↑' 'dealer.buys_' " := (dealer_buys__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.buys_' " := (dealer_buys__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition dealer_ret__right {b} (x: URValue dealerLRecord b): URValue (XMaybe OrderRetLRecord) b :=
|| {x} ^^ {dealer_ι_ret_} || : _.

Definition dealer_ret__left (x: ULValue dealerLRecord): ULValue (XMaybe OrderRetLRecord) :=
{{ {x} ^^ {dealer_ι_ret_} }} : _.

Notation " a '↑' 'dealer.ret_' " := (dealer_ret__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.ret_' " := (dealer_ret__left a ) (in custom ULValue at level 0) : ursus_scope.

(**************************************************************************************************************)
(*SellArgs*)

Definition SellArgs_amount_right {b} (x: URValue SellArgsLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {SellArgs_ι_amount} || : _.

Definition SellArgs_amount_left (x: ULValue SellArgsLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {SellArgs_ι_amount} }} : _.

Notation " a '↑' 'SellArgs.amount' " := (SellArgs_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'SellArgs.amount' " := (SellArgs_amount_left a ) (in custom ULValue at level 0) : ursus_scope.
 
Definition OrderInfo_amount_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
	|| {x} ^^ {OrderInfo_ι_amount} || : _.
	
Definition OrderInfo_amount_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_amount} }} : _.

(**************************************************************************************************************)
(*OrderInfo*)
	
Notation " a '↑' 'OrderInfo.amount' " := ( OrderInfo_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.amount' " := ( OrderInfo_amount_left a ) (in custom ULValue at level 0) : ursus_scope.
	
Definition OrderInfo_account_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfo_ι_account} || : _.

Definition OrderInfo_account_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_account} }} : _.

Notation " a '↑' 'OrderInfo.account' " := ( OrderInfo_account_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.account' " := ( OrderInfo_account_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition OrderInfo_order_finish_time_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfo_ι_order_finish_time} || : _.

Definition OrderInfo_order_finish_time_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_order_finish_time} }} : _.

Notation " a '↑' 'OrderInfo.order_finish_time' " := ( OrderInfo_order_finish_time_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.order_finish_time' " := ( OrderInfo_order_finish_time_left a ) (in custom ULValue at level 0) : ursus_scope.
	
Definition OrderInfo_original_amount_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfo_ι_original_amount} || : _.

Definition OrderInfo_original_amount_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_original_amount} }} : _.

Notation " a '↑' 'OrderInfo.original_amount' " := ( OrderInfo_original_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.original_amount' " := ( OrderInfo_original_amount_left a ) (in custom ULValue at level 0) : ursus_scope.


(**************************************************************************************************************)
(*process_ret*)

Definition process_ret_sells_amount_right {b} (x: URValue process_retLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {process_ret_ι_sells_amount} || : _ .

Definition process_ret_sells__right {b} (x: URValue process_retLRecord b): URValue ( XQueue OrderInfoLRecord ) b :=
    || {x} ^^ {process_ret_ι_sells_} || : _ .

Definition process_ret_buys_amount_right {b} (x: URValue process_retLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {process_ret_ι_buys_amount} || : _ .

Definition process_ret_buys__right {b} (x: URValue process_retLRecord b): URValue ( XQueue OrderInfoLRecord ) b :=
    || {x} ^^ {process_ret_ι_buys_} || : _ .

Definition process_ret_ret__right {b} (x: URValue process_retLRecord b): URValue ( XMaybe OrderRetLRecord ) b :=
    || {x} ^^ {process_ret_ι_ret_} || : _ .  

Definition process_ret_sells_amount_left  (x: ULValue process_retLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {process_ret_ι_sells_amount} }} : _ .

Definition process_ret_sells__left  (x: ULValue process_retLRecord): ULValue ( XQueue OrderInfoLRecord ) :=
    {{ {x} ^^ {process_ret_ι_sells_} }} : _ .

Definition process_ret_buys_amount_left  (x: ULValue process_retLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {process_ret_ι_buys_amount} }} : _ .

Definition process_ret_buys__left  (x: ULValue process_retLRecord): ULValue ( XQueue OrderInfoLRecord ) :=
    {{ {x} ^^ {process_ret_ι_buys_} }} : _ .

Definition process_ret_ret__left  (x: ULValue process_retLRecord): ULValue ( XMaybe OrderRetLRecord ) :=
    {{ {x} ^^ {process_ret_ι_ret_} }} : _ .              

Notation " a '↑' 'process_ret.sells_amount' " := ( process_ret_sells_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.sells_amount' " := ( process_ret_sells_amount_right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.sells_' " := ( process_ret_sells__left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.sells_' " := ( process_ret_sells__right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.buys_amount' " := ( process_ret_buys_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.buys_amount' " := ( process_ret_buys_amount_right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.buys_' " := ( process_ret_buys__left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.buys_' " := ( process_ret_buys__right a) (in custom URValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.ret_' " := ( process_ret_ret__left a) (in custom ULValue at level 0) : ursus_scope. 
Notation " a '↑' 'process_ret.ret_' " := ( process_ret_ret__right a) (in custom URValue at level 0) : ursus_scope. 
 
End ClassTypesNotations.

