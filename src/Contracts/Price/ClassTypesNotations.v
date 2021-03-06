Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonAxioms.

Require Import Price.ClassTypes.
Require Import Price.Interface.

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).

Module Export CommonAxiomsModule := CommonAxioms xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.
Module Export InterfaceModule := PublicInterface xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

(********************************************************************)
(*dealer*)

Definition dealer_tip3root__right {b} (x: URValue dealerLRecord b): URValue address b :=
|| {x} ^^ {dealer_ι_tip3root_} || : _.

Definition dealer_tip3root__left (x: ULValue dealerLRecord): ULValue address :=
{{ {x} ^^ {dealer_ι_tip3root_} }} : _.

Notation " a '↑' 'dealer.tip3root_' " := (dealer_tip3root__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.tip3root_' " := (dealer_tip3root__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition dealer_notify_addr__right {b} (x: URValue dealerLRecord b): URValue address b :=
|| {x} ^^ {dealer_ι_notify_addr_} || : _.

Definition dealer_notify_addr__left (x: ULValue dealerLRecord): ULValue address :=
{{ {x} ^^ {dealer_ι_notify_addr_} }} : _.

Notation " a '↑' 'dealer.notify_addr_' " := (dealer_notify_addr__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.notify_addr_' " := (dealer_notify_addr__left a ) (in custom ULValue at level 0) : ursus_scope.



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

Definition dealer_deals_limit__right {b} (x: URValue dealerLRecord b): URValue XUInteger b :=
|| {x} ^^ {dealer_ι_deals_limit_} || : _.

Definition dealer_deals_limit__left (x: ULValue dealerLRecord): ULValue XUInteger :=
{{ {x} ^^ {dealer_ι_deals_limit_} }} : _.

Notation " a '↑' 'dealer.deals_limit_' " := (dealer_deals_limit__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.deals_limit_' " := (dealer_deals_limit__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition dealer_tons_cfg__right {b} (x: URValue dealerLRecord b): URValue TonsConfigLRecord b :=
|| {x} ^^ {dealer_ι_tons_cfg_} || : _.

Definition dealer_tons_cfg__left (x: ULValue dealerLRecord): ULValue TonsConfigLRecord :=
{{ {x} ^^ {dealer_ι_tons_cfg_} }} : _.

Notation " a '↑' 'dealer.tons_cfg_' " := (dealer_tons_cfg__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.tons_cfg_' " := (dealer_tons_cfg__left a ) (in custom ULValue at level 0) : ursus_scope.


Definition dealer_price__right {b} (x: URValue dealerLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {dealer_ι_price_} || : _.

Definition dealer_price__left (x: ULValue dealerLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {dealer_ι_price_} }} : _.

Notation " a '↑' 'dealer.price_' " := (dealer_price__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'dealer.price_' " := (dealer_price__left a ) (in custom ULValue at level 0) : ursus_scope.


(**************************************************************************************************************)
(*SellArgs*)

Definition SellArgs_amount_right {b} (x: URValue SellArgsLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {SellArgs_ι_amount} || : _.

Definition SellArgs_amount_left (x: ULValue SellArgsLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {SellArgs_ι_amount} }} : _.

Notation " a '↑' 'SellArgs.amount' " := (SellArgs_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'SellArgs.amount' " := (SellArgs_amount_left a ) (in custom ULValue at level 0) : ursus_scope.
 
Definition SellArgs_receive_wallet_right {b} (x: URValue SellArgsLRecord b): URValue address b :=
|| {x} ^^ {SellArgs_ι_receive_wallet} || : _.

Definition SellArgs_receive_wallet_left (x: ULValue SellArgsLRecord): ULValue address :=
{{ {x} ^^ {SellArgs_ι_receive_wallet} }} : _.

Notation " a '↑' 'SellArgs.receive_wallet' " := (SellArgs_receive_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'SellArgs.receive_wallet' " := (SellArgs_receive_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.
 
(**************************************************************************************************************)
(*OrderInfo*)
	
Definition OrderInfo_amount_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
	|| {x} ^^ {OrderInfo_ι_amount} || : _.
	
Definition OrderInfo_amount_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_amount} }} : _.


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
	
Definition OrderInfo_tip3_wallet_right {b} (x: URValue OrderInfoLRecord b): URValue addr_std_fixed b :=
|| {x} ^^ {OrderInfo_ι_tip3_wallet} || : _.

Definition OrderInfo_tip3_wallet_left (x: ULValue OrderInfoLRecord): ULValue addr_std_fixed :=
{{ {x} ^^ {OrderInfo_ι_tip3_wallet} }} : _.

Notation " a '↑' 'OrderInfo.tip3_wallet' " := ( OrderInfo_tip3_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.tip3_wallet' " := ( OrderInfo_tip3_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition OrderInfo_original_amount_right {b} (x: URValue OrderInfoLRecord b): URValue XUInteger128 b :=
	|| {x} ^^ {OrderInfo_ι_original_amount} || : _.
	
Definition OrderInfo_original_amount_left (x: ULValue OrderInfoLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfo_ι_original_amount} }} : _.


Notation " a '↑' 'OrderInfo.original_amount' " := ( OrderInfo_original_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.original_amount' " := ( OrderInfo_original_amount_left a ) (in custom ULValue at level 0) : ursus_scope.
	
Definition OrderInfo_ι_client_addr_right {b} (x: URValue OrderInfoLRecord b): URValue addr_std_fixed b :=
	|| {x} ^^ {OrderInfo_ι_client_addr} || : _.
	
Definition OrderInfo_ι_client_addr_left (x: ULValue OrderInfoLRecord): ULValue addr_std_fixed :=
{{ {x} ^^ {OrderInfo_ι_client_addr} }} : _.


Notation " a '↑' 'OrderInfo.client_addr' " := ( OrderInfo_ι_client_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfo.client_addr' " := ( OrderInfo_ι_client_addr_left a ) (in custom ULValue at level 0) : ursus_scope.
	

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
 

(*interface*)

(* Inductive IPriceP :=
| IonTip3LendOwnership : address -> XUInteger128 -> XUInteger32 -> XUInteger256 -> address -> cell -> IPriceP
| IbuyTip3 : XUInteger128 -> address -> XUInteger32 -> IPriceP
| IprocessQueue : IPriceP
| IcancelSell : IPriceP
| IcancelBuy : IPriceP
| _Icreate : InitialState -> IPriceP.
 *)

Definition  IprocessQueue_right : URValue IPrice false.
 refine (#IprocessQueue).
Defined.

Notation " '.processQueue' '()' " := (IprocessQueue_right ) 
(in custom URValue at level 0 ) : ursus_scope .

Definition  IcancelSell_right : URValue IPrice false.
 refine (#IcancelSell).
Defined.

Notation " 'Price.cancelSell' '()' " := (IcancelSell_right ) 
(in custom URValue at level 0 ) : ursus_scope .

Definition  IcancelBuy_right : URValue IPrice false.
 refine (#IcancelBuy).
Defined.

Notation " 'Price.cancelBuy' '()' " := (IcancelBuy_right ) 
(in custom URValue at level 0 ) : ursus_scope .

Definition _Icreate_right { a1 }  ( x : URValue StateInitLRecord a1 ) : URValue IPrice a1.
 pose proof (urvalue_bind x (fun x' => #(_Icreate x' : IPrice)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'Price.deploy' ( x ) " := (_Icreate_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .
 
(* | IonTip3LendOwnership : address -> XUInteger128 -> XUInteger32 -> XUInteger256 -> address -> cell -> IPriceP *)

Definition IonTip3LendOwnership_right { a1 a2 a3 a4 a5 a6 }  (x : URValue address a1 ) 
                                                 (y : URValue XUInteger128 a2) 
                                                 (z : URValue XUInteger32 a3)
                                                 (t : URValue XUInteger256 a4)
                                                 (u : URValue address a5)
                                                 (v : URValue cell a6) : URValue IPrice (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 a6))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  #(IonTip3LendOwnership x' y' z' t' u' v' : IPrice))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.onTip3LendOwnership' ( x , y , z , t , u , v ) " := (IonTip3LendOwnership_right x y z t u v) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, v custom URValue at level 0 ) : ursus_scope .


(*| IbuyTip3 : XUInteger128 -> address -> XUInteger32 -> IPriceP*)
Definition IbuyTip3_right { a1 a2 a3 } (x : URValue XUInteger128 a1 ) 
                                       (y : URValue address a2) 
                                       (z : URValue XUInteger32 a3)
                                        : URValue IPrice (orb a1 (orb a2 a3)).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  #(IbuyTip3 x' y' z'  : IPrice)))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.buyTip3' ( x , y , z  ) " := (IbuyTip3_right x y z) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0) : ursus_scope .

Definition IonOrderFinished_right { a1 a2} (x : URValue OrderRetLRecord a1 ) 
                                       (y : URValue XBool a2) 
                                        : URValue IPriceCallback (orb a1 a2).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' => #(IonOrderFinished x' y'  : IPriceCallback))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'Price.onOrderFinished' ( x , y  ) " := (IonOrderFinished_right x y) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0) : ursus_scope .

End ClassTypesNotations.


