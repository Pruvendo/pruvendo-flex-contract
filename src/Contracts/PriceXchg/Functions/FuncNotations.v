Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.

Require Import Contracts.PriceXchg.Ledger.
Require Import Contracts.PriceXchg.Functions.FuncSig.

(* здесь инмпортируем все внешние интерфейсы *)
Require Import Contracts.PriceXchg.Interface.
Require Import Contracts.TONTokenWallet.Interface.
Require Import Contracts.PriceCallback.Interface.
Require Import Contracts.Flex.Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module PriceXchgPublicInterface := Contracts.PriceXchg.PublicInterface xt sm.
Module TONTokenWalletPublicInterface := Contracts.TONTokenWallet.PublicInterface xt sm.
Module PriceCallbackPublicInterface := Contracts.PriceCallback.PublicInterface xt sm.
Module FlexPublicInterface := Contracts.Flex.PublicInterface xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Fail Check OutgoingMessage_default.

Import UrsusNotations.
Local Open Scope ucpp_scope.
Local Open Scope ursus_scope.

(**********************************************************************************************************************)
(*RationalPrice*)

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

(**********************************************************************************************************************)
(* PayloadArgs *)

Definition PayloadArgs_sell_right {b} (x: URValue PayloadArgsLRecord b): URValue XBool b :=
    || {x} ^^ {PayloadArgs_ι_sell} || : _ .

Definition PayloadArgs_amount_right {b} (x: URValue PayloadArgsLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {PayloadArgs_ι_amount} || : _ .

Definition PayloadArgs_receive_tip3_wallet_right {b} (x: URValue PayloadArgsLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {PayloadArgs_ι_receive_tip3_wallet} || : _ .

Definition PayloadArgs_client_addr_right {b} (x: URValue PayloadArgsLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {PayloadArgs_ι_client_addr} || : _ .

Definition PayloadArgs_sell_left (x: ULValue PayloadArgsLRecord): ULValue XBool :=
    {{ {x} ^^ {PayloadArgs_ι_sell} }} : _ .

Definition PayloadArgs_amount_left (x: ULValue PayloadArgsLRecord): ULValue XUInteger128:=
    {{ {x} ^^ {PayloadArgs_ι_amount} }} : _ .

Definition PayloadArgs_receive_tip3_wallet_left (x: ULValue PayloadArgsLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {PayloadArgs_ι_receive_tip3_wallet} }} : _ .

Definition PayloadArgs_client_addr_left (x: ULValue PayloadArgsLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {PayloadArgs_ι_client_addr} }} : _ .    


Notation " a '↑' 'PayloadArgs.sell' " := ( PayloadArgs_sell_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.sell' " := ( PayloadArgs_sell_left a ) (in custom ULValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.amount' " := ( PayloadArgs_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.amount' " := ( PayloadArgs_amount_left a ) (in custom ULValue at level 0) : ursus_scope.   
Notation " a '↑' 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_receive_tip3_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_receive_tip3_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.client_addr' " := ( PayloadArgs_client_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.client_addr' " := ( PayloadArgs_client_addr_left a ) (in custom ULValue at level 0) : ursus_scope.   

(**********************************************************************************************************************)
(* OrderInfoXchg *)

(* Definition OrderInfoXchgL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XUInteger32 ) : Type ] . *)

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
 

(**********************************************************************************************************************)
(* DetailsInfoXchg *)
(* Definition DetailsInfoXchgL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] . *)

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

 (* Definition dealerL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress (* IFlexNotifyPtrLRecord *) ) : Type ; 
 ( RationalPriceLRecord ) : Type ; 
 ( XUInteger ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ; 
 ( XUInteger128 ) : Type ;
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ; 
 ( ( XMaybe OrderRetLRecord ) ) : Type ] . *)

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

 (**********************************************************************************************************************)
 (* OrderRet *)

 (* Definition OrderRetL : list Type := 
 [ ( XUInteger32 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] . *)

Definition OrderRet_err_code_right {b} (x: URValue OrderRetLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {OrderRet_ι_err_code} || : _ .

Definition OrderRet_processed_right {b} (x: URValue OrderRetLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderRet_ι_processed} || : _ .

Definition OrderRet_enqueued_right {b} (x: URValue OrderRetLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {OrderRet_ι_enqueued} || : _ .

Definition OrderRet_err_code_left  (x: ULValue OrderRetLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {OrderRet_ι_err_code} }} : _ .

Definition OrderRet_processed_left  (x: ULValue OrderRetLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderRet_ι_processed} }} : _ .

Definition OrderRet_enqueued_left  (x: ULValue OrderRetLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {OrderRet_ι_enqueued} }} : _ .    

 Notation " a '↑' 'OrderRet.err_code' " := ( OrderRet_err_code_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'OrderRet.err_code' " := ( OrderRet_err_code_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'OrderRet.processed' " := ( OrderRet_processed_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'OrderRet.processed' " := ( OrderRet_processed_right a) (in custom URValue at level 0) : ursus_scope. 
 Notation " a '↑' 'OrderRet.enqueued' " := ( OrderRet_enqueued_left a) (in custom ULValue at level 0) : ursus_scope. 
 Notation " a '↑' 'OrderRet.enqueued' " := ( OrderRet_enqueued_right a) (in custom URValue at level 0) : ursus_scope. 

(**********************************************************************************************************************)
(* process_ret *)
(* Definition process_retL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ; 
 ( ( XMaybe OrderRetLRecord ) ) : Type ] . *)
 
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


(**********************************************************************************************************************)
(*State fields*)

Definition price__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType price_ ) : ULValue RationalPriceLRecord ) . 
 Definition price__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType price_ ) : URValue RationalPriceLRecord false ) . 
 Notation " '_price_' " := ( price__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_price_' " := ( price__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition sells_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType sells_amount_ ) : ULValue uint128 ) . 
 Definition sells_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType sells_amount_ ) : URValue uint128 false ) . 
 Notation " '_sells_amount_' " := ( sells_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_sells_amount_' " := ( sells_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition buys_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType buys_amount_ ) : ULValue uint128 ) . 
 Definition buys_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType buys_amount_ ) : URValue uint128 false ) . 
 Notation " '_buys_amount_' " := ( buys_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_buys_amount_' " := ( buys_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : ULValue addr_std_fixedLRecord ) . 
 Definition flex__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : URValue addr_std_fixedLRecord false ) . 
 Notation " '_flex_' " := ( flex__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_' " := ( flex__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition min_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType min_amount_ ) : ULValue uint128 ) . 
 Definition min_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType min_amount_ ) : URValue uint128 false ) . 
 Notation " '_min_amount_' " := ( min_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_min_amount_' " := ( min_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition deals_limit__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : ULValue uint8 ) . 
 Definition deals_limit__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : URValue uint8 false ) . 
 Notation " '_deals_limit_' " := ( deals_limit__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_deals_limit_' " := ( deals_limit__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition notify_addr__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType notify_addr_ ) : ULValue XAddress (* IFlexNotifyPtrLRecord *) ) . 
 Definition notify_addr__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType notify_addr_ ) : URValue XAddress (* IFlexNotifyPtrLRecord *) false ) . 
 Notation " '_notify_addr_' " := ( notify_addr__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_notify_addr_' " := ( notify_addr__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : ULValue uint8 ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : URValue uint8 false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tons_cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : ULValue TonsConfigLRecord ) . 
 Definition tons_cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : URValue TonsConfigLRecord false ) . 
 Notation " '_tons_cfg_' " := ( tons_cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tons_cfg_' " := ( tons_cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tip3_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tip3_code_ ) : ULValue XCell ) . 
 Definition tip3_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tip3_code_ ) : URValue XCell false ) . 
 Notation " '_tip3_code_' " := ( tip3_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tip3_code_' " := ( tip3_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition major_tip3cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType major_tip3cfg_ ) : ULValue Tip3ConfigLRecord ) . 
 Definition major_tip3cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType major_tip3cfg_ ) : URValue Tip3ConfigLRecord false ) . 
 Notation " '_major_tip3cfg_' " := ( major_tip3cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_major_tip3cfg_' " := ( major_tip3cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition minor_tip3cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType minor_tip3cfg_ ) : ULValue Tip3ConfigLRecord ) . 
 Definition minor_tip3cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType minor_tip3cfg_ ) : URValue Tip3ConfigLRecord false ) . 
 Notation " '_minor_tip3cfg_' " := ( minor_tip3cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_minor_tip3cfg_' " := ( minor_tip3cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition sells__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType sells_ ) : ULValue ( XQueue OrderInfoXchgLRecord ) ) . 
 Definition sells__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType sells_ ) : URValue ( XQueue OrderInfoXchgLRecord ) false ) . 
 Notation " '_sells_' " := ( sells__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_sells_' " := ( sells__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition buys__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType buys_ ) : ULValue ( XQueue OrderInfoXchgLRecord ) ) . 
 Definition buys__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType buys_ ) : URValue ( XQueue OrderInfoXchgLRecord ) false ) . 
 Notation " '_buys_' " := ( buys__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_buys_' " := ( buys__right ) (in custom URValue at level 0) : ursus_scope. 
  

Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

(**************************************************************************************************)
Notation "'λ2LL'" := (@UExpression_Next_LedgerableWithLArgs _ _ _ _ _( @UExpression_Next_LedgerableWithLArgs _ _ _ _ _ λ0)) (at level 0) : ursus_scope.

Definition make_deal_right  
( sell : ULValue ( OrderInfoXchgLRecord ) ) 
( buy : ULValue ( OrderInfoXchgLRecord ) ) 
: URValue ( XBool # (XBool # uint128) ) 
false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2LL ) make_deal 
 sell buy ) . 
 
 Notation " 'make_deal_' '(' sell buy ')' " := 
 ( make_deal_right 
 sell buy ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , buy custom URValue at level 0 ) : ursus_scope . 

 (* Definition extract_active_order_right { a2 a3 a4 a5 }  
( cur_order : URValue ( XMaybe (uint # OrderInfoXchgLRecord ) ) a2 ) 
( orders : URValue ( XQueue OrderInfoXchgLRecord ) a3 ) 
( all_amount : URValue ( uint128 ) a4 ) 
( sell : URValue ( XBool ) a5 ) 
: URValue ( (XMaybe ( uint # OrderInfoXchgLRecord )) # ( (XQueue OrderInfoXchgLRecord) # uint128 ) ) false . 
 ( orb ( orb ( orb a5 a4 ) a3 ) a2 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) extract_active_order 
 unsigned cur_order orders all_amount sell ) . 
 
 Notation " 'extract_active_order_' '(' unsigned cur_order orders all_amount sell ')' " := 
 ( extract_active_order_right 
 unsigned cur_order orders all_amount sell ) 
 (in custom URValue at level 0 , unsigned custom URValue at level 0 
 , cur_order custom URValue at level 0 
 , orders custom URValue at level 0 
 , all_amount custom URValue at level 0 
 , sell custom URValue at level 0 ) : ursus_scope .  *)
 
 Definition process_queue_left { R a1 a2 }  ( sell_idx : URValue ( uint ) a1 ) ( buy_idx : URValue ( uint ) a2 ) : UExpression R ( orb a2 a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) process_queue 
 sell_idx buy_idx ) . 
 
 Notation " 'process_queue_' '(' sell_idx buy_idx ')' " := 
 ( process_queue_left 
 sell_idx buy_idx ) 
 (in custom ULValue at level 0 , sell_idx custom URValue at level 0 
 , buy_idx custom URValue at level 0 ) : ursus_scope . 
 Definition onTip3LendOwnership_right { a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( XAddress ) a1 ) ( balance : URValue ( uint128 ) a2 ) ( lend_finish_time : URValue ( uint32 ) a3 ) ( pubkey : URValue ( uint256 ) a4 ) ( internal_owner : URValue ( XAddress ) a5 ) ( payload : URValue ( XCell ) a6 ) : URValue OrderRetLRecord ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) onTip3LendOwnership 
 answer_addr balance lend_finish_time pubkey internal_owner payload ) . 
 
 Notation " 'onTip3LendOwnership_' '(' answer_addr balance lend_finish_time pubkey internal_owner payload ')' " := 
 ( onTip3LendOwnership_right 
 answer_addr balance lend_finish_time pubkey internal_owner payload ) 
 (in custom URValue at level 0 , answer_addr custom URValue at level 0 
 , balance custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope .
 
 Definition processQueue_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) processQueue 
 ) . 
 
 Notation " 'processQueue_' '(' ')' " := 
 ( processQueue_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition cancelSell_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) cancelSell 
 ) . 
 
 Notation " 'cancelSell_' '(' ')' " := 
 ( cancelSell_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition cancelBuy_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) cancelBuy 
 ) . 
 
 Notation " 'cancelBuy_' '(' ')' " := 
 ( cancelBuy_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 Definition getDetails_right  : URValue DetailsInfoXchgLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDetails 
 ) . 
 
 Notation " 'getDetails_' '(' ')' " := 
 ( getDetails_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getPriceNum_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPriceNum 
 ) . 
 
 Notation " 'getPriceNum_' '(' ')' " := 
 ( getPriceNum_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getPriceDenum_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPriceDenum 
 ) . 
 
 Notation " 'getPriceDenum_' '(' ')' " := 
 ( getPriceDenum_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getMinimumAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getMinimumAmount 
 ) . 
 
 Notation " 'getMinimumAmount_' '(' ')' " := 
 ( getMinimumAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getTonsCfg_right  : URValue TonsConfigLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTonsCfg 
 ) . 
 
 Notation " 'getTonsCfg_' '(' ')' " := 
 ( getTonsCfg_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getSells_right  : URValue ( XHMap uint OrderInfoXchgLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSells 
 ) . 
 
 Notation " 'getSells_' '(' ')' " := 
 ( getSells_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope .
 
 Definition getBuys_right  : URValue ( XHMap uint OrderInfoXchgLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuys 
 ) . 
 
 Notation " 'getBuys_' '(' ')' " := 
 ( getBuys_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getSellAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSellAmount 
 ) . 
 
 Notation " 'getSellAmount_' '(' ')' " := 
 ( getSellAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getBuyAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuyAmount 
 ) . 
 
 Notation " 'getBuyAmount_' '(' ')' " := 
 ( getBuyAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope .
 
 Definition _fallback_right { a1 a2 }  
( x : URValue XCell a1 )
( y : URValue XSlice a2 ) 
: URValue uint (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 x y ) . 
 
 Notation " '_fallback_' '(' x ',' y ')' " := 
 ( _fallback_right x y ) 
 (in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0 ) : ursus_scope . 

 Definition onTip3LendOwnershipMinValue_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) onTip3LendOwnershipMinValue 
 ) . 
 
 Notation " 'onTip3LendOwnershipMinValue_' '(' ')' " := 
 ( onTip3LendOwnershipMinValue_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition verify_tip3_addr_right { a1 a2 a3 a4 }  ( cfg : URValue ( Tip3ConfigLRecord ) a1 ) ( tip3_wallet : URValue ( XAddress ) a2 ) ( wallet_pubkey : URValue ( uint256 ) a3 ) ( internal_owner : URValue ( uint256 ) a4 ) : URValue XBool ( orb ( orb ( orb a4 a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) verify_tip3_addr 
 cfg tip3_wallet wallet_pubkey internal_owner ) . 
 
 Notation " 'verify_tip3_addr_' '(' cfg tip3_wallet wallet_pubkey internal_owner ')' " := 
 ( verify_tip3_addr_right 
 cfg tip3_wallet wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 
 , tip3_wallet custom URValue at level 0 
 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope . 

 Definition expected_wallet_address_right { a1 a2 a3 }  ( cfg : URValue ( Tip3ConfigLRecord ) a1 ) ( wallet_pubkey : URValue ( uint256 ) a2 ) ( internal_owner : URValue ( uint256 ) a3 ) : URValue uint256 ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) expected_wallet_address 
 cfg wallet_pubkey internal_owner ) . 
 
 Notation " 'expected_wallet_address_' '(' cfg wallet_pubkey internal_owner ')' " := 
 ( expected_wallet_address_right 
 cfg wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 
 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope .

 Definition on_ord_fail_right { a1 a2 a3 }  ( ec : URValue ( uint ) a1 ) ( wallet_in : URValue ( XAddress (* ITONTokenWalletPtrLRecord *) ) a2 ) ( amount : URValue ( uint128 ) a3 ) : URValue OrderRetLRecord ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) on_ord_fail 
 ec wallet_in amount ) . 
 
 Notation " 'on_ord_fail_' '(' ec wallet_in amount ')' " := 
 ( on_ord_fail_right 
 ec wallet_in amount ) 
 (in custom URValue at level 0 , ec custom URValue at level 0 
 , wallet_in custom URValue at level 0 
 , amount custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_price_xchg_state_init_and_addr_right { a1 a2 }  ( price_data : URValue ( ContractLRecord ) a1 ) ( price_code : URValue ( XCell ) a2 ) : URValue ( StateInitLRecord # uint256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_price_xchg_state_init_and_addr 
 price_data price_code ) . 
 
 Notation " 'prepare_price_xchg_state_init_and_addr_' '(' price_data price_code ')' " := 
 ( prepare_price_xchg_state_init_and_addr_right 
 price_data price_code ) 
 (in custom URValue at level 0 , price_data custom URValue at level 0 
 , price_code custom URValue at level 0 ) : ursus_scope . 

 Definition is_active_time_right { a1 }  ( order_finish_time : URValue ( uint32 ) a1 ) : URValue XBool a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) is_active_time 
 order_finish_time ) . 
 
 Notation " 'is_active_time_' '(' order_finish_time ')' " := 
 ( is_active_time_right 
 order_finish_time ) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope .

 Definition minor_cost_right { a1 a2 }  ( amount : URValue ( uint128 ) a1 ) ( price : URValue ( RationalPriceLRecord ) a2 ) : URValue (XMaybe uint128) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) minor_cost 
 amount price ) . 
 
 Notation " 'minor_cost_' '(' amount price ')' " := 
 ( minor_cost_right 
 amount price ) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom URValue at level 0 ) : ursus_scope . 

 Definition process_queue_impl_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 }  
( tip3root_sell : URValue ( XAddress ) a1 ) 
( tip3root_buy : URValue ( XAddress ) a2 ) 
( notify_addr : URValue ( XAddress (* IFlexNotifyPtrLRecord *) ) a3 ) 
( price : URValue ( RationalPriceLRecord ) a4 ) 
( deals_limit : URValue ( uint8 ) a5 ) 
( tons_cfg : URValue ( TonsConfigLRecord ) a6 ) 
( sell_idx : URValue ( uint ) a7 ) 
( buy_idx : URValue ( uint ) a8 ) 
( sells_amount : URValue ( uint128 ) a9 ) 
( sells : URValue ( XQueue OrderInfoXchgLRecord ) a10 ) 
( buys_amount : URValue ( uint128 ) a11 ) 
( buys : URValue ( XQueue OrderInfoXchgLRecord ) a12 ) 
: URValue process_retLRecord 
( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a12 a11 ) a10 ) a9 ) a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) 
:= 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ12 ) process_queue_impl 
 tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) . 
 
 Notation " 'process_queue_impl_' '(' tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ')' " := 
 ( process_queue_impl_right 
 tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) 
 (in custom URValue at level 0 , tip3root_sell custom URValue at level 0 
 , tip3root_buy custom URValue at level 0 
 , notify_addr custom URValue at level 0 
 , price custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_cfg custom URValue at level 0 
 , sell_idx custom URValue at level 0 
 , buy_idx custom URValue at level 0 
 , sells_amount custom URValue at level 0 
 , sells custom URValue at level 0 
 , buys_amount custom URValue at level 0 
 , buys custom URValue at level 0 ) : ursus_scope . 

 Definition cancel_order_impl_right { a1 a2 a3 a4 a5 a6 a7 }  
( orders : URValue ( XQueue OrderInfoXchgLRecord ) a1 ) 
( client_addr : URValue ( addr_std_fixedLRecord ) a2 ) 
( all_amount : URValue ( uint128 ) a3 ) 
( sell : URValue ( XBool ) a4 ) 
( return_ownership : URValue ( uint (* Grams *) ) a5 ) 
( process_queue : URValue ( uint (* Grams *) ) a6 ) 
( incoming_val : URValue ( uint (* Grams *) ) a7 ) 
: URValue ((XQueue OrderInfoXchgLRecord) # uint128) 
( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancel_order_impl 
 orders client_addr all_amount sell return_ownership process_queue incoming_val ) . 
 
 Notation " 'cancel_order_impl_' '(' orders client_addr all_amount sell return_ownership process_queue incoming_val ')' " := 
 ( cancel_order_impl_right 
 orders client_addr all_amount sell return_ownership process_queue incoming_val ) 
 (in custom URValue at level 0 , orders custom URValue at level 0 
 , client_addr custom URValue at level 0 
 , all_amount custom URValue at level 0 
 , sell custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , process_queue custom URValue at level 0 
 , incoming_val custom URValue at level 0 ) : ursus_scope .
 
 Definition int_sender_and_value_right  : URValue ( XAddress # uint (* Grams *) ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) int_sender_and_value 
 ) . 
 
 Notation " 'int_sender_and_value_' '(' ')' " := 
 ( int_sender_and_value_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

End Calls. 

End FuncNotations.

