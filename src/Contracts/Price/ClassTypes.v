Require Import FinProof.ProgrammingWith. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.

Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
Inductive DetailsInfoFields := | DetailsInfo_ι_price | DetailsInfo_ι_min_amount | DetailsInfo_ι_sell_amount | DetailsInfo_ι_buy_amount .
Inductive dealerFields := | dealer_ι_tip3root_ 
                          | dealer_ι_notify_addr_ 
                          | dealer_ι_price_ 
                          | dealer_ι_deals_limit_ 
                          | dealer_ι_tons_cfg_ 
                          | dealer_ι_sells_amount_ 
                          | dealer_ι_sells_ 
                          | dealer_ι_buys_amount_ 
                          | dealer_ι_buys_ 
                          | dealer_ι_ret_ .
Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .

(* struct DPrice {
  uint128 price_;
  uint128 sells_amount_;
  uint128 buys_amount_;
  addr_std_fixed flex_;
  uint128 min_amount_;
  uint8 deals_limit_; // limit for processed deals in one request

  IFlexNotifyPtr notify_addr_;

  int8 workchain_id_;

  TonsConfig tons_cfg_;
  cell tip3_code_;
  Tip3Config tip3cfg_;

  queue<OrderInfo> sells_;
  queue<OrderInfo> buys_;
}; *)

Inductive DPriceFields := | DPrice_ι_price_ 
                          | DPrice_ι_sells_amount_ 
                          | DPrice_ι_buys_amount_ 
                          | DPrice_ι_flex_ 
                          | DPrice_ι_min_amount_ 
                          | DPrice_ι_deals_limit_                           
                          | DPrice_ι_notify_addr_ 
                          | DPrice_ι_workchain_id_ 
                          | DPrice_ι_tons_cfg_ 
                          | DPrice_ι_tip3_code_ 
                          | DPrice_ι_tip3cfg_ 
                          | DPrice_ι_sells_ 
                          | DPrice_ι_buys_ .
Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_sells_ | process_ret_ι_buys_amount | process_ret_ι_buys_ | process_ret_ι_ret_ .

Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.
Local Open Scope ursus_scope.

Definition SellArgsL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( address ) : Type ] .
Elpi GeneratePruvendoRecord SellArgsL SellArgsFields . 

Definition DetailsInfoL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord DetailsInfoL DetailsInfoFields . 

Definition OrderInfoL : list Type := 
    [ ( XUInteger128 ) : Type ; 
    ( XUInteger128 ) : Type ; 
    ( XUInteger128 ) : Type ; 
    ( addr_std_fixed ) : Type ; 
    ( addr_std_fixed ) : Type ; 
    ( XUInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord OrderInfoL OrderInfoFields . 

Definition dealerL : list Type := 
 [ ( address ) : Type ; 
 ( address (* IFlexNotifyPtr *) ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( ( XMaybe OrderRetLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord dealerL dealerFields . 

Definition DPriceL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixed ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( address (* IFlexNotify *) ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord DPriceL DPriceFields . 

Definition process_retL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( ( XMaybe OrderRetLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord process_retL process_retFields . 

End ClassTypes .
 