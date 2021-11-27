Require Import FinProof.ProgrammingWith. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.

Inductive RationalPriceFields := | RationalPrice_ι_num | RationalPrice_ι_denum .
Inductive DetailsInfoXchgFields := | DetailsInfoXchg_ι_price_num | DetailsInfoXchg_ι_price_denum | DetailsInfoXchg_ι_min_amount | DetailsInfoXchg_ι_sell_amount | DetailsInfoXchg_ι_buy_amount .
Inductive dealerFields := | dealer_ι_tip3root_sell_ | dealer_ι_tip3root_buy_ | dealer_ι_notify_addr_ | dealer_ι_price_ | dealer_ι_deals_limit_ | dealer_ι_tons_cfg_ | dealer_ι_sells_amount_ | dealer_ι_sells_ | dealer_ι_buys_amount_ | dealer_ι_buys_ | dealer_ι_ret_ .
Inductive OrderInfoXchgFields := | OrderInfoXchg_ι_original_amount | OrderInfoXchg_ι_amount | OrderInfoXchg_ι_account | OrderInfoXchg_ι_tip3_wallet_provide | OrderInfoXchg_ι_tip3_wallet_receive | OrderInfoXchg_ι_client_addr | OrderInfoXchg_ι_order_finish_time .
Inductive DPriceXchgFields := | DPriceXchg_ι_price_ | DPriceXchg_ι_sells_amount_ | DPriceXchg_ι_buys_amount_ | DPriceXchg_ι_flex_ | DPriceXchg_ι_min_amount_ | DPriceXchg_ι_deals_limit_ | DPriceXchg_ι_notify_addr_ | DPriceXchg_ι_workchain_id_ | DPriceXchg_ι_tons_cfg_ | DPriceXchg_ι_tip3_code_ | DPriceXchg_ι_major_tip3cfg_ | DPriceXchg_ι_minor_tip3cfg_ | DPriceXchg_ι_sells_ | DPriceXchg_ι_buys_ .
Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_sells_ | process_ret_ι_buys_amount | process_ret_ι_buys_ | process_ret_ι_ret_ .
Inductive PayloadArgsFields := | PayloadArgs_ι_sell | PayloadArgs_ι_amount | PayloadArgs_ι_receive_tip3_wallet | PayloadArgs_ι_client_addr .

Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.
Local Open Scope ursus_scope.

Definition RationalPriceL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord RationalPriceL RationalPriceFields . 

Definition DetailsInfoXchgL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord DetailsInfoXchgL DetailsInfoXchgFields . 

Definition OrderInfoXchgL : list Type := 
    [ ( XUInteger128 ) : Type ; 
    ( XUInteger128 ) : Type ; 
    ( XUInteger128 ) : Type ; 
    ( addr_std_fixedLRecord ) : Type ; 
    ( addr_std_fixedLRecord ) : Type ; 
    ( addr_std_fixedLRecord ) : Type ; 
    ( XUInteger32 ) : Type ] .
GeneratePruvendoRecord OrderInfoXchgL OrderInfoXchgFields . 

(* using OrderInfoXchgWithIdx = std::pair<unsigned, OrderInfoXchg>; *)

Definition OrderInfoXchgWithIdx := XUInteger # OrderInfoXchgLRecord.

Definition dealerL : list Type := 
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
 ( ( XMaybe OrderRetLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord dealerL dealerFields . 

Definition DPriceXchgL : list Type := 
 [ ( RationalPriceLRecord ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( addr_std_fixedLRecord ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XAddress (* IFlexNotifyPtr *) ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord DPriceXchgL DPriceXchgFields . 

Definition process_retL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoXchgLRecord ) ) : Type ; 
 ( ( XMaybe OrderRetLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord process_retL process_retFields . 


Opaque addr_std_fixedLRecord.
Definition PayloadArgsL : list Type := 
[ ( XBool ) : Type ; 
( XUInteger128 ) : Type ; 
( addr_std_fixedLRecord ) : Type ; 
( addr_std_fixedLRecord ) : Type ] .
Elpi GeneratePruvendoRecord PayloadArgsL PayloadArgsFields . 

End ClassTypes .
