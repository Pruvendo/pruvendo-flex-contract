Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonAxioms.

Require Import PriceXchg.ClassTypes.
Require Import PriceXchg.Interface.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).

Module Export CommonAxiomsModule := CommonAxioms xt sm cs.
Module Export ClassTypesModule := (* PriceXchg.ClassTypes. *)ClassTypes xt sm.
Module Export InterfaceModule := (* PriceXchg.ClassTypes. *)PublicInterface xt sm.

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


Definition dealer_tip3root_sell__right {b} (x: URValue dealerLRecord b): URValue address b :=
    || {x} ^^ {dealer_ι_tip3root_sell_} || : _ .

Definition dealer_tip3root_buy__right {b} (x: URValue dealerLRecord b): URValue address b :=
    || {x} ^^ {dealer_ι_tip3root_buy_} || : _ .

Definition dealer_notify_addr__right {b} (x: URValue dealerLRecord b): URValue address b :=
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

Definition dealer_tip3root_sell__left  (x: ULValue dealerLRecord): ULValue address :=
    {{ {x} ^^ {dealer_ι_tip3root_sell_} }} : _ .

Definition dealer_tip3root_buy__left  (x: ULValue dealerLRecord): ULValue address :=
    {{ {x} ^^ {dealer_ι_tip3root_buy_} }} : _ .

Definition dealer_notify_addr__left  (x: ULValue dealerLRecord): ULValue address :=
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

Definition OrderInfoXchg_tip3_wallet_provide_right {b} (x: URValue OrderInfoXchgLRecord b): URValue addr_std_fixed b :=
    || {x} ^^ {OrderInfoXchg_ι_tip3_wallet_provide} || : _ .  

Definition OrderInfoXchg_tip3_wallet_receive_right {b} (x: URValue OrderInfoXchgLRecord b): URValue addr_std_fixed b :=
    || {x} ^^ {OrderInfoXchg_ι_tip3_wallet_receive} || : _ .

Definition OrderInfoXchg_client_addr_right {b} (x: URValue OrderInfoXchgLRecord b): URValue addr_std_fixed b :=
    || {x} ^^ {OrderInfoXchg_ι_client_addr} || : _ .

Definition OrderInfoXchg_order_finish_time_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {OrderInfoXchg_ι_order_finish_time} || : _ .  

Definition OrderInfoXchg_original_amount_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderInfoXchg_ι_original_amount} }} : _ .

Definition OrderInfoXchg_amount_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderInfoXchg_ι_amount} }} : _ .

Definition OrderInfoXchg_account_left  (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderInfoXchg_ι_account} }} : _ .

Definition OrderInfoXchg_tip3_wallet_provide_left  (x: ULValue OrderInfoXchgLRecord): ULValue addr_std_fixed :=
    {{ {x} ^^ {OrderInfoXchg_ι_tip3_wallet_provide} }} : _ .  

Definition OrderInfoXchg_tip3_wallet_receive_left  (x: ULValue OrderInfoXchgLRecord): ULValue addr_std_fixed :=
    {{ {x} ^^ {OrderInfoXchg_ι_tip3_wallet_receive} }} : _ .

Definition OrderInfoXchg_client_addr_left  (x: ULValue OrderInfoXchgLRecord): ULValue addr_std_fixed :=
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
 
 Definition process_ret_sells_amount_right {b} (x: URValue process_retLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {process_ret_ι_sells_amount} || : _ .

Definition process_ret_sells__right {b} (x: URValue process_retLRecord b): URValue ( XQueue OrderInfoXchgLRecord ) b :=
    || {x} ^^ {process_ret_ι_sells_} || : _ .

Definition process_ret_buys_amount_right {b} (x: URValue process_retLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {process_ret_ι_buys_amount} || : _ .

Definition process_ret_buys__right {b} (x: URValue process_retLRecord b): URValue ( XQueue OrderInfoXchgLRecord ) b :=
    || {x} ^^ {process_ret_ι_buys_} || : _ .

Definition process_ret_ret__right {b} (x: URValue process_retLRecord b): URValue ( XMaybe OrderRetLRecord ) b :=
    || {x} ^^ {process_ret_ι_ret_} || : _ .  

Definition process_ret_sells_amount_left  (x: ULValue process_retLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {process_ret_ι_sells_amount} }} : _ .

Definition process_ret_sells__left  (x: ULValue process_retLRecord): ULValue ( XQueue OrderInfoXchgLRecord ) :=
    {{ {x} ^^ {process_ret_ι_sells_} }} : _ .

Definition process_ret_buys_amount_left  (x: ULValue process_retLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {process_ret_ι_buys_amount} }} : _ .

Definition process_ret_buys__left  (x: ULValue process_retLRecord): ULValue ( XQueue OrderInfoXchgLRecord ) :=
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
 
Definition PayloadArgs_sell_right {b} (x: URValue PayloadArgsLRecord b): URValue XBool b :=
    || {x} ^^ {PayloadArgs_ι_sell} || : _ .

Definition PayloadArgs_amount_right {b} (x: URValue PayloadArgsLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {PayloadArgs_ι_amount} || : _ .

Definition PayloadArgs_receive_tip3_wallet_right {b} (x: URValue PayloadArgsLRecord b): URValue addr_std_fixed b :=
    || {x} ^^ {PayloadArgs_ι_receive_tip3_wallet} || : _ .

Definition PayloadArgs_client_addr_right {b} (x: URValue PayloadArgsLRecord b): URValue addr_std_fixed b :=
    || {x} ^^ {PayloadArgs_ι_client_addr} || : _ .

Definition PayloadArgs_sell_left (x: ULValue PayloadArgsLRecord): ULValue XBool :=
    {{ {x} ^^ {PayloadArgs_ι_sell} }} : _ .

Definition PayloadArgs_amount_left (x: ULValue PayloadArgsLRecord): ULValue XUInteger128:=
    {{ {x} ^^ {PayloadArgs_ι_amount} }} : _ .

Definition PayloadArgs_receive_tip3_wallet_left (x: ULValue PayloadArgsLRecord): ULValue addr_std_fixed :=
    {{ {x} ^^ {PayloadArgs_ι_receive_tip3_wallet} }} : _ .

Definition PayloadArgs_client_addr_left (x: ULValue PayloadArgsLRecord): ULValue addr_std_fixed :=
    {{ {x} ^^ {PayloadArgs_ι_client_addr} }} : _ .    


Notation " a '↑' 'PayloadArgs.sell' " := ( PayloadArgs_sell_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.sell' " := ( PayloadArgs_sell_left a ) (in custom ULValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.amount' " := ( PayloadArgs_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.amount' " := ( PayloadArgs_amount_left a ) (in custom ULValue at level 0) : ursus_scope.   
Notation " a '↑' 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_receive_tip3_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_receive_tip3_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.client_addr' " := ( PayloadArgs_client_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.client_addr' " := ( PayloadArgs_client_addr_left a ) (in custom ULValue at level 0) : ursus_scope.   

Definition RationalPrice_num_right {b} (x: URValue RationalPriceLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {RationalPrice_ι_num} || : _ .

Definition RationalPrice_denum_right {b} (x: URValue RationalPriceLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {RationalPrice_ι_denum} || : _ .
    
Definition RationalPrice_num_left (x: ULValue RationalPriceLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {RationalPrice_ι_num} }} : _ .

Definition RationalPrice_denum_left (x: ULValue RationalPriceLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {RationalPrice_ι_denum} }} : _ .    


Notation " a '↑' 'RationalPrice.num' " := ( RationalPrice_num_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'RationalPrice.num' " := ( RationalPrice_num_left a ) (in custom ULValue at level 0) : ursus_scope.
Notation " a '↑' 'RationalPrice.denum' " := ( RationalPrice_denum_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'RationalPrice.denum' " := ( RationalPrice_denum_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition DPriceXchg_ι_price__right {b} (x: URValue DPriceXchgLRecord b): URValue RationalPriceLRecord b :=
    || {x} ^^ {DPriceXchg_ι_price_} || : _ .

Definition DPriceXchg_ι_price__left (x: ULValue DPriceXchgLRecord): ULValue RationalPriceLRecord :=
    {{ {x} ^^ {DPriceXchg_ι_price_} }} : _ .

Notation " a '↑' 'DPriceXchg.price_' " := ( DPriceXchg_ι_price__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.price_' " := ( DPriceXchg_ι_price__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_sells_amount__right {b} (x: URValue DPriceXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DPriceXchg_ι_sells_amount_} || : _ .

Definition DPriceXchg_ι_sells_amount__left (x: ULValue DPriceXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DPriceXchg_ι_sells_amount_} }} : _ .

Notation " a '↑' 'DPriceXchg.sells_amount_' " := ( DPriceXchg_ι_sells_amount__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.sells_amount_' " := ( DPriceXchg_ι_sells_amount__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_buys_amount__right {b} (x: URValue DPriceXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DPriceXchg_ι_buys_amount_} || : _ .

Definition DPriceXchg_ι_buys_amount__left (x: ULValue DPriceXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DPriceXchg_ι_buys_amount_} }} : _ .

Notation " a '↑' 'DPriceXchg.buys_amount_' " := ( DPriceXchg_ι_buys_amount__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.buys_amount_' " := ( DPriceXchg_ι_buys_amount__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_flex__right {b} (x: URValue DPriceXchgLRecord b): URValue addr_std_fixed b :=
    || {x} ^^ {DPriceXchg_ι_flex_} || : _ .

Definition DPriceXchg_ι_flex__left (x: ULValue DPriceXchgLRecord): ULValue addr_std_fixed :=
    {{ {x} ^^ {DPriceXchg_ι_flex_} }} : _ .

Notation " a '↑' 'DPriceXchg.flex_' " := ( DPriceXchg_ι_flex__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.flex_' " := ( DPriceXchg_ι_flex__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_min_amount__right {b} (x: URValue DPriceXchgLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DPriceXchg_ι_min_amount_} || : _ .

Definition DPriceXchg_ι_min_amount__left (x: ULValue DPriceXchgLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DPriceXchg_ι_min_amount_} }} : _ .

Notation " a '↑' 'DPriceXchg.min_amount_' " := ( DPriceXchg_ι_min_amount__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXch.min_amount_' " := ( DPriceXchg_ι_min_amount__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_deals_limit__right {b} (x: URValue DPriceXchgLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DPriceXchg_ι_deals_limit_} || : _ .

Definition DPriceXchg_ι_deals_limit__left (x: ULValue DPriceXchgLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DPriceXchg_ι_deals_limit_} }} : _ .

Notation " a '↑' 'DPriceXchg.deals_limit_' " := ( DPriceXchg_ι_deals_limit__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.deals_limit_' " := ( DPriceXchg_ι_deals_limit__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_notify_addr__right {b} (x: URValue DPriceXchgLRecord b): URValue address b :=
    || {x} ^^ {DPriceXchg_ι_notify_addr_} || : _ .

Definition DPriceXchg_ι_notify_addr__left (x: ULValue DPriceXchgLRecord): ULValue address :=
    {{ {x} ^^ {DPriceXchg_ι_notify_addr_} }} : _ .

Notation " a '↑' 'DPriceXchg.notify_addr_' " := ( DPriceXchg_ι_notify_addr__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.notify_addr_' " := ( DPriceXchg_ι_notify_addr__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_workchain_id__right {b} (x: URValue DPriceXchgLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DPriceXchg_ι_workchain_id_} || : _ .

Definition DPriceXchg_ι_workchain_id__left (x: ULValue DPriceXchgLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DPriceXchg_ι_workchain_id_} }} : _ .

Notation " a '↑' 'DPriceXchg.workchain_id_' " := ( DPriceXchg_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.workchain_id_' " := ( DPriceXchg_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_tons_cfg__right {b} (x: URValue DPriceXchgLRecord b): URValue TonsConfigLRecord b :=
    || {x} ^^ {DPriceXchg_ι_tons_cfg_} || : _ .

Definition DPriceXchg_ι_tons_cfg__left (x: ULValue DPriceXchgLRecord): ULValue TonsConfigLRecord :=
    {{ {x} ^^ {DPriceXchg_ι_tons_cfg_} }} : _ .

Notation " a '↑' 'DPriceXchg.tons_cfg_' " := ( DPriceXchg_ι_tons_cfg__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.tons_cfg_' " := ( DPriceXchg_ι_tons_cfg__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_tip3_code__right {b} (x: URValue DPriceXchgLRecord b): URValue XCell b :=
    || {x} ^^ {DPriceXchg_ι_tip3_code_} || : _ .

Definition DPriceXchg_ι_tip3_code__left (x: ULValue DPriceXchgLRecord): ULValue XCell :=
    {{ {x} ^^ {DPriceXchg_ι_tip3_code_} }} : _ .

Notation " a '↑' 'DPriceXchg.tip3_code_' " := ( DPriceXchg_ι_tip3_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.tip3_code_' " := ( DPriceXchg_ι_tip3_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_major_tip3cfg__right {b} (x: URValue DPriceXchgLRecord b): URValue Tip3ConfigLRecord b :=
    || {x} ^^ {DPriceXchg_ι_major_tip3cfg_} || : _ .

Definition DPriceXchg_ι_major_tip3cfg__left (x: ULValue DPriceXchgLRecord): ULValue Tip3ConfigLRecord :=
    {{ {x} ^^ {DPriceXchg_ι_major_tip3cfg_} }} : _ .

Notation " a '↑' 'DPriceXchg.major_tip3cfg_' " := ( DPriceXchg_ι_major_tip3cfg__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.major_tip3cfg_' " := ( DPriceXchg_ι_major_tip3cfg__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_minor_tip3cfg__right {b} (x: URValue DPriceXchgLRecord b): URValue Tip3ConfigLRecord b :=
    || {x} ^^ {DPriceXchg_ι_minor_tip3cfg_} || : _ .

Definition DPriceXchg_ι_minor_tip3cfg__left (x: ULValue DPriceXchgLRecord): ULValue Tip3ConfigLRecord :=
    {{ {x} ^^ {DPriceXchg_ι_minor_tip3cfg_} }} : _ .

Notation " a '↑' 'DPriceXchg.minor_tip3cfg_' " := ( DPriceXchg_ι_minor_tip3cfg__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.minor_tip3cfg_' " := ( DPriceXchg_ι_minor_tip3cfg__left a ) (in custom ULValue at level 0) : ursus_scope.


Definition DPriceXchg_ι_sells__right {b} (x: URValue DPriceXchgLRecord b): URValue ( XQueue OrderInfoXchgLRecord ) b :=
    || {x} ^^ {DPriceXchg_ι_sells_} || : _ .

Definition DPriceXchg_ι_sells__left (x: ULValue DPriceXchgLRecord): ULValue ( XQueue OrderInfoXchgLRecord ) :=
    {{ {x} ^^ {DPriceXchg_ι_sells_} }} : _ .

Notation " a '↑' 'DPriceXchg.sells_' " := ( DPriceXchg_ι_sells__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.sells_' " := ( DPriceXchg_ι_sells__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DPriceXchg_ι_buys__right {b} (x: URValue DPriceXchgLRecord b): URValue ( XQueue OrderInfoXchgLRecord ) b :=
    || {x} ^^ {DPriceXchg_ι_buys_} || : _ .

Definition DPriceXchg_ι_buys__left (x: ULValue DPriceXchgLRecord): ULValue ( XQueue OrderInfoXchgLRecord ) :=
    {{ {x} ^^ {DPriceXchg_ι_buys_} }} : _ .

Notation " a '↑' 'DPriceXchg.buys_' " := ( DPriceXchg_ι_buys__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DPriceXchg.buys_' " := ( DPriceXchg_ι_buys__left a ) (in custom ULValue at level 0) : ursus_scope.


(*interface*)
(* Inductive IPriceXchgP :=
| IonTip3LendOwnership : address -> XUInteger128 -> XUInteger32 -> XUInteger256 -> address -> XCell -> IPriceXchgP
| IprocessQueue : IPriceXchgP
| IcancelSell : IPriceXchgP
| IcancelBuy : IPriceXchgP
| _Icreate : InitialState -> IPriceXchgP.
 *)

Definition  IprocessQueue_right : URValue IPriceXchg false.
 refine (#IprocessQueue).
Defined.

Notation " '.processQueue' '()' " := (IprocessQueue_right ) 
(in custom URValue at level 0 ) : ursus_scope .

Definition  IcancelSell_right : URValue IPriceXchg false.
 refine (#IcancelSell).
Defined.

Notation " 'PriceXchg.cancelSell' '()' " := (IcancelSell_right ) 
(in custom URValue at level 0 ) : ursus_scope .

Definition  IcancelBuy_right : URValue IPriceXchg false.
 refine (#IcancelBuy).
Defined.

Notation " 'PriceXchg.cancelBuy' '()' " := (IcancelBuy_right ) 
(in custom URValue at level 0 ) : ursus_scope .

Definition _Icreate_right { a1 }  ( x : URValue StateInitLRecord a1 ) : URValue IPriceXchg a1.
 pose proof (urvalue_bind x (fun x' => #(_Icreate x' : IPriceXchg)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'PriceXchg.deploy' ( x ) " := (_Icreate_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .
 
(* IonTip3LendOwnership : address -> XUInteger128 -> XUInteger32 -> XUInteger256 -> address -> XCell -> IPriceXchgP *)

Definition IonTip3LendOwnership_right { a1 a2 a3 a4 a5 a6 }  (x : URValue address a1 ) 
                                                 (y : URValue XUInteger128 a2) 
                                                 (z : URValue XUInteger32 a3)
                                                 (t : URValue XUInteger256 a4)
                                                 (u : URValue address a5)
                                                 (v : URValue XCell a6) : URValue IPriceXchg (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 a6))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  #(IonTip3LendOwnership x' y' z' t' u' v' : IPriceXchg))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.onTip3LendOwnership' ( x , y , z , t , u , v ) " := (IonTip3LendOwnership_right x y z t u v) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, v custom URValue at level 0 ) : ursus_scope .


End ClassTypesNotations.


