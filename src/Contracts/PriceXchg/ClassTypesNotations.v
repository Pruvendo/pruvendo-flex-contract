Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.PriceXchg.ClassTypes.
Require Import Contracts.PriceXchg.Ledger.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.



(**********************************************************************************************************************)
(* DetailsInfoXchg *)


Definition DetailsInfoXchg_price_num_right {b} (x: URValue DetailsInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DetailsInfoXchg_ι_price_num} || : _ .

Definition DetailsInfoXchg_price_denum_right {b} (x: URValue DetailsInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DetailsInfoXchg_ι_price_denum} || : _ .

Definition DetailsInfoXchg_min_amount_right {b} (x: URValue DetailsInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DetailsInfoXchg_ι_min_amount} || : _ .

Definition DetailsInfoXchg_sell_amount_right {b} (x: URValue DetailsInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DetailsInfoXchg_ι_sell_amount} || : _ .

Definition DetailsInfoXchg_buy_amount_right {b} (x: URValue DetailsInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DetailsInfoXchg_ι_buy_amount} || : _ .            

Definition DetailsInfoXchg_price_num_left  (x: ULValue DetailsInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DetailsInfoXchg_ι_price_num} }} : _ .

Definition DetailsInfoXchg_price_denum_left  (x: ULValue DetailsInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DetailsInfoXchg_ι_price_denum} }} : _ .

Definition DetailsInfoXchg_min_amount_left  (x: ULValue DetailsInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DetailsInfoXchg_ι_min_amount} }} : _ .

Definition DetailsInfoXchg_sell_amount_left  (x: ULValue DetailsInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DetailsInfoXchg_ι_sell_amount} }} : _ .

Definition DetailsInfoXchg_buy_amount_left  (x: ULValue DetailsInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DetailsInfoXchg_ι_buy_amount} }} : _ . 

 Notation "  a '↑' 'DetailsInfoXchg.price_num' " := ( DetailsInfoXchg_price_num_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'DetailsInfoXchg.price_num' " := ( DetailsInfoXchg_price_num_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'DetailsInfoXchg.price_denum' " := ( DetailsInfoXchg_price_denum_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'DetailsInfoXchg.price_denum' " := ( DetailsInfoXchg_price_denum_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'DetailsInfoXchg.min_amount' " := ( DetailsInfoXchg_min_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'DetailsInfoXchg.min_amount' " := ( DetailsInfoXchg_min_amount_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'DetailsInfoXchg.sell_amount' " := ( DetailsInfoXchg_sell_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'DetailsInfoXchg.sell_amount' " := ( DetailsInfoXchg_sell_amount_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'DetailsInfoXchg.buy_amount' " := ( DetailsInfoXchg_buy_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'DetailsInfoXchg.buy_amount' " := ( DetailsInfoXchg_buy_amount_right a) (in custom URValue at level 0) : ursus_scope. 
 
 (**********************************************************************************************************************)
 (* dealer *)


Definition dealer_tip3root_sell__right {b} (x: URValue dealerLRecord b): URValue XAddress b :=
    || {x} ^^ {dealer_ι_tip3root_sell_} || : _ .

Definition dealer_tip3root_buy__right {b} (x: URValue dealerLRecord b): URValue XAddress b :=
    || {x} ^^ {dealer_ι_tip3root_buy_} || : _ .

Definition dealer_notify_addr__right {b} (x: URValue dealerLRecord b): URValue XAddress b :=
    || {x} ^^ {dealer_ι_notify_addr_} || : _ .

Definition dealer_price__right {b} (x: URValue dealerLRecord b): URValue RationalPriceLRecord b :=
    || {x} ^^ {dealer_ι_price_} || : _ .

Definition dealer_deals_limit__right {b} (x: URValue dealerLRecord b): URValue XUInteger b :=
    || {x} ^^ {dealer_ι_deals_limit_} || : _ .

Definition dealer_tons_cfg__right {b} (x: URValue dealerLRecord b): URValue TonsConfigLRecord b :=
    || {x} ^^ {dealer_ι_tons_cfg_} || : _ .

Definition dealer_sells_amount__right {b} (x: URValue dealerLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {dealer_ι_sells_amount_} || : _ .

Definition dealer_sells__right {b} (x: URValue dealerLRecord b): URValue ( XQueue OrderInfoXchgLRecord ) b :=
    || {x} ^^ {dealer_ι_sells_} || : _ .

Definition dealer_buys_amount__right {b} (x: URValue dealerLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {dealer_ι_buys_amount_} || : _ .

Definition dealer_buys__right {b} (x: URValue dealerLRecord b): URValue ( XQueue OrderInfoXchgLRecord ) b :=
    || {x} ^^ {dealer_ι_buys_} || : _ .

Definition dealer_ret__right {b} (x: URValue dealerLRecord b): URValue  ( XMaybe OrderRetLRecord ) b :=
    || {x} ^^ {dealer_ι_ret_} || : _ .    

Definition dealer_tip3root_sell__left  (x: ULValue dealerLRecord): ULValue XAddress :=
    {{ {x} ^^ {dealer_ι_tip3root_sell_} }} : _ .

Definition dealer_tip3root_buy__left  (x: ULValue dealerLRecord): ULValue XAddress :=
    {{ {x} ^^ {dealer_ι_tip3root_buy_} }} : _ .

Definition dealer_notify_addr__left  (x: ULValue dealerLRecord): ULValue XAddress :=
    {{ {x} ^^ {dealer_ι_notify_addr_} }} : _ .

Definition dealer_price__left  (x: ULValue dealerLRecord): ULValue RationalPriceLRecord :=
    {{ {x} ^^ {dealer_ι_price_} }} : _ .

Definition dealer_deals_limit__left  (x: ULValue dealerLRecord): ULValue XUInteger :=
    {{ {x} ^^ {dealer_ι_deals_limit_} }} : _ .

Definition dealer_tons_cfg__left  (x: ULValue dealerLRecord): ULValue TonsConfigLRecord :=
    {{ {x} ^^ {dealer_ι_tons_cfg_} }} : _ .

Definition dealer_sells_amount__left  (x: ULValue dealerLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {dealer_ι_sells_amount_} }} : _ .

Definition dealer_sells__left  (x: ULValue dealerLRecord): ULValue ( XQueue OrderInfoXchgLRecord ) :=
    {{ {x} ^^ {dealer_ι_sells_} }} : _ .

Definition dealer_buys_amount__left  (x: ULValue dealerLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {dealer_ι_buys_amount_} }} : _ .

Definition dealer_buys__left  (x: ULValue dealerLRecord): ULValue ( XQueue OrderInfoXchgLRecord ) :=
    {{ {x} ^^ {dealer_ι_buys_} }} : _ .

Definition dealer_ret__left  (x: ULValue dealerLRecord): ULValue  ( XMaybe OrderRetLRecord ) :=
    {{ {x} ^^ {dealer_ι_ret_} }} : _ .      


 Notation " a '↑' 'dealer.tip3root_sell_' " := ( dealer_tip3root_sell__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.tip3root_sell_' " := ( dealer_tip3root_sell__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.tip3root_buy_' " := ( dealer_tip3root_buy__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.tip3root_buy_' " := ( dealer_tip3root_buy__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.notify_addr_' " := ( dealer_notify_addr__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.notify_addr_' " := ( dealer_notify_addr__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.price_' " := ( dealer_price__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.price_' " := ( dealer_price__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.deals_limit_' " := ( dealer_deals_limit__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.deals_limit_' " := ( dealer_deals_limit__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.tons_cfg_' " := ( dealer_tons_cfg__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.tons_cfg_' " := ( dealer_tons_cfg__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.sells_amount_' " := ( dealer_sells_amount__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.sells_amount_' " := ( dealer_sells_amount__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.sells_' " := ( dealer_sells__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.sells_' " := ( dealer_sells__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.buys_amount_' " := ( dealer_buys_amount__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.buys_amount_' " := ( dealer_buys_amount__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.buys_' " := ( dealer_buys__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.buys_' " := ( dealer_buys__right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.ret_' " := ( dealer_ret__left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'dealer.ret_' " := ( dealer_ret__right a) (in custom URValue at level 0) : ursus_scope. 

 Definition OrderInfoXchg_original_amount_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderInfoXchg_ι_original_amount} || : _ .

Definition OrderInfoXchg_amount_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderInfoXchg_ι_amount} || : _ .

Definition OrderInfoXchg_account_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderInfoXchg_ι_account} || : _ .

Definition OrderInfoXchg_tip3_wallet_provide_right {b} (x: URValue OrderInfoXchgLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {OrderInfoXchg_ι_tip3_wallet_provide} || : _ .  

Definition OrderInfoXchg_tip3_wallet_receive_right {b} (x: URValue OrderInfoXchgLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {OrderInfoXchg_ι_tip3_wallet_receive} || : _ .

Definition OrderInfoXchg_client_addr_right {b} (x: URValue OrderInfoXchgLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {OrderInfoXchg_ι_client_addr} || : _ .

Definition OrderInfoXchg_order_finish_time_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {OrderInfoXchg_ι_order_finish_time} || : _ .  

Definition OrderInfoXchg_original_amount_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderInfoXchg_ι_original_amount} }} : _ .

Definition OrderInfoXchg_amount_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderInfoXchg_ι_amount} }} : _ .

Definition OrderInfoXchg_account_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderInfoXchg_ι_account} }} : _ .

Definition OrderInfoXchg_tip3_wallet_provide_left  (x: ULValue OrderInfoXchgLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {OrderInfoXchg_ι_tip3_wallet_provide} }} : _ .  

Definition OrderInfoXchg_tip3_wallet_receive_left  (x: ULValue OrderInfoXchgLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {OrderInfoXchg_ι_tip3_wallet_receive} }} : _ .

Definition OrderInfoXchg_client_addr_left  (x: ULValue OrderInfoXchgLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {OrderInfoXchg_ι_client_addr} }} : _ .

Definition OrderInfoXchg_order_finish_time_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {OrderInfoXchg_ι_order_finish_time} }} : _ .     

 
 Notation "  a '↑' 'OrderInfoXchg.original_amount' " := ( OrderInfoXchg_original_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.original_amount' " := ( OrderInfoXchg_original_amount_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.amount' " := ( OrderInfoXchg_amount_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.amount' " := ( OrderInfoXchg_amount_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.account' " := ( OrderInfoXchg_account_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.account' " := ( OrderInfoXchg_account_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.tip3_wallet_provide' " := ( OrderInfoXchg_tip3_wallet_provide_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.tip3_wallet_provide' " := ( OrderInfoXchg_tip3_wallet_provide_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.tip3_wallet_receive' " := ( OrderInfoXchg_tip3_wallet_receive_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.tip3_wallet_receive' " := ( OrderInfoXchg_tip3_wallet_receive_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.client_addr' " := ( OrderInfoXchg_client_addr_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.client_addr' " := ( OrderInfoXchg_client_addr_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.order_finish_time' " := ( OrderInfoXchg_order_finish_time_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation "  a '↑' 'OrderInfoXchg.order_finish_time' " := ( OrderInfoXchg_order_finish_time_right a) (in custom URValue at level 0) : ursus_scope. 
 


End ClassTypesNotations.


