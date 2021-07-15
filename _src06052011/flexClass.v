Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import FinProof.ProgrammingWith.

Require Import String.

Local Open Scope record.
Local Open Scope program_scope. 
Require Import FinProof.Common.
Require Import FinProof.MonadTransformers21.
Require Import FinProof.StateMonad21.

(* Require Import FinProof.Lib.BasicModuleTypes. *)
Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG24.
(* Require Import flexTypes. *)

Section RecordsDefinitions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Variables I I8 I16 I32 I64 I128 I256 : Type.
Variables A B C S Bs : Type.
Variables L M H : Type -> Type. (* H - handle<type> *)
Variables HM P : Type -> Type -> Type.
Variables T G Sl Bt : Type.

Variables addr_std_fixedP IStockNotifyPtrP : Type. (******************************)

Notation " 'fst0' x " := ( x ) (at level 60, right associativity).
Notation " 'fst1' x " := ( fst ( fst0 x ) ) (at level 60, right associativity).
Notation " 'fst2' x " := ( fst ( fst1 x ) ) (at level 60, right associativity).
Notation " 'fst3' x " := ( fst ( fst2 x ) ) (at level 60, right associativity).
Notation " 'fst4' x " := ( fst ( fst3 x ) ) (at level 60, right associativity).
Notation " 'fst5' x " := ( fst ( fst4 x ) ) (at level 60, right associativity).
Notation " 'fst6' x " := ( fst ( fst5 x ) ) (at level 60, right associativity).
Notation " 'fst7' x " := ( fst ( fst6 x ) ) (at level 60, right associativity).
Notation " 'fst8' x " := ( fst ( fst7 x ) ) (at level 60, right associativity).
Notation " 'fst9' x " := ( fst ( fst8 x ) ) (at level 60, right associativity).
Notation " 'fst10' x " := ( fst ( fst9 x ) ) (at level 60, right associativity).
Notation " 'fst11' x " := ( fst ( fst10 x ) ) (at level 60, right associativity).
Notation " 'fst12' x " := ( fst ( fst11 x ) ) (at level 60, right associativity).
Notation " 'fst13' x " := ( fst ( fst12 x ) ) (at level 60, right associativity).





Inductive Tip3Config := 
| Tip3Config_ι_name 
| Tip3Config_ι_symbol 
| Tip3Config_ι_decimals 
| Tip3Config_ι_root_public_key 
| Tip3Config_ι_root_address 
| Tip3Config_ι_code 

. 
Definition Tip3ConfigP := ( 
S * S * I8 * I256 * A * C )%type . 

 
Definition Tip3Config_field_type f : Type :=  
match f with 
| Tip3Config_ι_name => S 
| Tip3Config_ι_symbol => S 
| Tip3Config_ι_decimals => I8 
| Tip3Config_ι_root_public_key => I256 
| Tip3Config_ι_root_address => A 
| Tip3Config_ι_code => C 

end . 

 
Definition Tip3Config_get (f: Tip3Config )(r: Tip3ConfigP ) :  Tip3Config_field_type f := 
 match f with 
| Tip3Config_ι_name => fst5 r 
 | Tip3Config_ι_symbol => snd ( fst4 r ) 
 | Tip3Config_ι_decimals => snd ( fst3 r ) 
 | Tip3Config_ι_root_public_key => snd ( fst2 r ) 
 | Tip3Config_ι_root_address => snd ( fst1 r ) 
 | Tip3Config_ι_code => snd r 
 end . 

 
Coercion Tip3Config_get : Tip3Config >-> Funclass. 

 
Definition Tip3Config_set (f: Tip3Config ) 
(v: Tip3Config_field_type f) (r: Tip3ConfigP ): Tip3ConfigP  :=
  match f, v with 
| Tip3Config_ι_name v' => ( v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Tip3Config_ι_symbol v' => ( fst5 , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Tip3Config_ι_decimals v' => ( fst5 , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Tip3Config_ι_root_public_key v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | Tip3Config_ι_root_address v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | Tip3Config_ι_code v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance Tip3Config_set_Record : PruvendoRecord Tip3ConfigP Tip3ConfigFields :=
{
  field_type := Tip3Config_field_type; 
  getPruvendoRecord := @Tip3Config_get ;
  setPruvendoRecord := @Tip3Config_set ;
}. 

 
Inductive OrderRet := 
| OrderRet_ι_err_code 
| OrderRet_ι_processed 
| OrderRet_ι_enqueued 

. 
Definition OrderRetP := ( 
I32 * I128 * I128 )%type . 

 
Definition OrderRet_field_type f : Type :=  
match f with 
| OrderRet_ι_err_code => I32 
| OrderRet_ι_processed => I128 
| OrderRet_ι_enqueued => I128 

end . 

 
Definition OrderRet_get (f: OrderRet )(r: OrderRetP ) :  OrderRet_field_type f := 
 match f with 
| OrderRet_ι_err_code => fst2 r 
 | OrderRet_ι_processed => snd ( fst1 r ) 
 | OrderRet_ι_enqueued => snd r 
 end . 

 
Coercion OrderRet_get : OrderRet >-> Funclass. 

 
Definition OrderRet_set (f: OrderRet ) 
(v: OrderRet_field_type f) (r: OrderRetP ): OrderRetP  :=
  match f, v with 
| OrderRet_ι_err_code v' => ( v' , snd ( fst1 r ) , snd r ) 
 | OrderRet_ι_processed v' => ( fst2 , v' , snd r ) 
 | OrderRet_ι_enqueued v' => ( fst2 , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance OrderRet_set_Record : PruvendoRecord OrderRetP OrderRetFields :=
{
  field_type := OrderRet_field_type; 
  getPruvendoRecord := @OrderRet_get ;
  setPruvendoRecord := @OrderRet_set ;
}. 

 
Inductive SellArgs := 
| SellArgs_ι_amount 
| SellArgs_ι_receive_wallet 

. 
Definition SellArgsP := ( 
I128 * addr_std_fixedP )%type . 

 
Definition SellArgs_field_type f : Type :=  
match f with 
| SellArgs_ι_amount => I128 
| SellArgs_ι_receive_wallet => addr_std_fixedP 

end . 

 
Definition SellArgs_get (f: SellArgs )(r: SellArgsP ) :  SellArgs_field_type f := 
 match f with 
| SellArgs_ι_amount => fst1 r 
 | SellArgs_ι_receive_wallet => snd r 
 end . 

 
Coercion SellArgs_get : SellArgs >-> Funclass. 

 
Definition SellArgs_set (f: SellArgs ) 
(v: SellArgs_field_type f) (r: SellArgsP ): SellArgsP  :=
  match f, v with 
| SellArgs_ι_amount v' => ( v' , snd r ) 
 | SellArgs_ι_receive_wallet v' => ( fst1 , v' ) 
 end . 

 
Global Instance SellArgs_set_Record : PruvendoRecord SellArgsP SellArgsFields :=
{
  field_type := SellArgs_field_type; 
  getPruvendoRecord := @SellArgs_get ;
  setPruvendoRecord := @SellArgs_set ;
}. 

 
Inductive SellInfo := 
| SellInfo_ι_original_amount 
| SellInfo_ι_amount 
| SellInfo_ι_account 
| SellInfo_ι_tip3_wallet 
| SellInfo_ι_receive_wallet 
| SellInfo_ι_lend_finish_time 

. 
Definition SellInfoP := ( 
I128 * I128 * I128 * addr_std_fixedP * addr_std_fixedP * I32 )%type . 

 
Definition SellInfo_field_type f : Type :=  
match f with 
| SellInfo_ι_original_amount => I128 
| SellInfo_ι_amount => I128 
| SellInfo_ι_account => I128 
| SellInfo_ι_tip3_wallet => addr_std_fixedP 
| SellInfo_ι_receive_wallet => addr_std_fixedP 
| SellInfo_ι_lend_finish_time => I32 

end . 

 
Definition SellInfo_get (f: SellInfo )(r: SellInfoP ) :  SellInfo_field_type f := 
 match f with 
| SellInfo_ι_original_amount => fst5 r 
 | SellInfo_ι_amount => snd ( fst4 r ) 
 | SellInfo_ι_account => snd ( fst3 r ) 
 | SellInfo_ι_tip3_wallet => snd ( fst2 r ) 
 | SellInfo_ι_receive_wallet => snd ( fst1 r ) 
 | SellInfo_ι_lend_finish_time => snd r 
 end . 

 
Coercion SellInfo_get : SellInfo >-> Funclass. 

 
Definition SellInfo_set (f: SellInfo ) 
(v: SellInfo_field_type f) (r: SellInfoP ): SellInfoP  :=
  match f, v with 
| SellInfo_ι_original_amount v' => ( v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | SellInfo_ι_amount v' => ( fst5 , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | SellInfo_ι_account v' => ( fst5 , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | SellInfo_ι_tip3_wallet v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | SellInfo_ι_receive_wallet v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | SellInfo_ι_lend_finish_time v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance SellInfo_set_Record : PruvendoRecord SellInfoP SellInfoFields :=
{
  field_type := SellInfo_field_type; 
  getPruvendoRecord := @SellInfo_get ;
  setPruvendoRecord := @SellInfo_set ;
}. 

 
Inductive BuyInfo := 
| BuyInfo_ι_original_amount 
| BuyInfo_ι_amount 
| BuyInfo_ι_account 
| BuyInfo_ι_receive_tip3_wallet 
| BuyInfo_ι_answer_addr 

. 
Definition BuyInfoP := ( 
I128 * I128 * I128 * addr_std_fixedP * addr_std_fixedP )%type . 

 
Definition BuyInfo_field_type f : Type :=  
match f with 
| BuyInfo_ι_original_amount => I128 
| BuyInfo_ι_amount => I128 
| BuyInfo_ι_account => I128 
| BuyInfo_ι_receive_tip3_wallet => addr_std_fixedP 
| BuyInfo_ι_answer_addr => addr_std_fixedP 

end . 

 
Definition BuyInfo_get (f: BuyInfo )(r: BuyInfoP ) :  BuyInfo_field_type f := 
 match f with 
| BuyInfo_ι_original_amount => fst4 r 
 | BuyInfo_ι_amount => snd ( fst3 r ) 
 | BuyInfo_ι_account => snd ( fst2 r ) 
 | BuyInfo_ι_receive_tip3_wallet => snd ( fst1 r ) 
 | BuyInfo_ι_answer_addr => snd r 
 end . 

 
Coercion BuyInfo_get : BuyInfo >-> Funclass. 

 
Definition BuyInfo_set (f: BuyInfo ) 
(v: BuyInfo_field_type f) (r: BuyInfoP ): BuyInfoP  :=
  match f, v with 
| BuyInfo_ι_original_amount v' => ( v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | BuyInfo_ι_amount v' => ( fst4 , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | BuyInfo_ι_account v' => ( fst4 , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | BuyInfo_ι_receive_tip3_wallet v' => ( fst4 , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | BuyInfo_ι_answer_addr v' => ( fst4 , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance BuyInfo_set_Record : PruvendoRecord BuyInfoP BuyInfoFields :=
{
  field_type := BuyInfo_field_type; 
  getPruvendoRecord := @BuyInfo_get ;
  setPruvendoRecord := @BuyInfo_set ;
}. 

 
Inductive DetailsInfo := 
| DetailsInfo_ι_price 
| DetailsInfo_ι_min_amount 
| DetailsInfo_ι_sell_amount 
| DetailsInfo_ι_buy_amount 

. 
Definition DetailsInfoP := ( 
I128 * I128 * I128 * I128 )%type . 

 
Definition DetailsInfo_field_type f : Type :=  
match f with 
| DetailsInfo_ι_price => I128 
| DetailsInfo_ι_min_amount => I128 
| DetailsInfo_ι_sell_amount => I128 
| DetailsInfo_ι_buy_amount => I128 

end . 

 
Definition DetailsInfo_get (f: DetailsInfo )(r: DetailsInfoP ) :  DetailsInfo_field_type f := 
 match f with 
| DetailsInfo_ι_price => fst3 r 
 | DetailsInfo_ι_min_amount => snd ( fst2 r ) 
 | DetailsInfo_ι_sell_amount => snd ( fst1 r ) 
 | DetailsInfo_ι_buy_amount => snd r 
 end . 

 
Coercion DetailsInfo_get : DetailsInfo >-> Funclass. 

 
Definition DetailsInfo_set (f: DetailsInfo ) 
(v: DetailsInfo_field_type f) (r: DetailsInfoP ): DetailsInfoP  :=
  match f, v with 
| DetailsInfo_ι_price v' => ( v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DetailsInfo_ι_min_amount v' => ( fst3 , v' , snd ( fst1 r ) , snd r ) 
 | DetailsInfo_ι_sell_amount v' => ( fst3 , snd ( fst2 r ) , v' , snd r ) 
 | DetailsInfo_ι_buy_amount v' => ( fst3 , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance DetailsInfo_set_Record : PruvendoRecord DetailsInfoP DetailsInfoFields :=
{
  field_type := DetailsInfo_field_type; 
  getPruvendoRecord := @DetailsInfo_get ;
  setPruvendoRecord := @DetailsInfo_set ;
}. 

 
Inductive DPrice := 
| DPrice_ι_price_ 
| DPrice_ι_sells_amount_ 
| DPrice_ι_buys_amount_ 
| DPrice_ι_stock_ 
| DPrice_ι_min_amount_ 
| DPrice_ι_deals_limit_ 
| DPrice_ι_notify_addr_ 
| DPrice_ι_workchain_id_ 
| DPrice_ι_tons_cfg_ 
| DPrice_ι_tip3cfg_ 
| DPrice_ι_sells_ 
| DPrice_ι_buys_ 

. 
Definition DPriceP := ( 
I128 * I128 * I128 * addr_std_fixedP * I128 * I8 * IStockNotifyPtrP * I8 * TonsConfigP * Tip3ConfigP * Q SellInfoP * Q BuyInfoP )%type . 

 
Definition DPrice_field_type f : Type :=  
match f with 
| DPrice_ι_price_ => I128 
| DPrice_ι_sells_amount_ => I128 
| DPrice_ι_buys_amount_ => I128 
| DPrice_ι_stock_ => addr_std_fixedP 
| DPrice_ι_min_amount_ => I128 
| DPrice_ι_deals_limit_ => I8 
| DPrice_ι_notify_addr_ => IStockNotifyPtrP 
| DPrice_ι_workchain_id_ => I8 
| DPrice_ι_tons_cfg_ => TonsConfigP 
| DPrice_ι_tip3cfg_ => Tip3ConfigP 
| DPrice_ι_sells_ => Q SellInfoP 
| DPrice_ι_buys_ => Q BuyInfoP 

end . 

 
Definition DPrice_get (f: DPrice )(r: DPriceP ) :  DPrice_field_type f := 
 match f with 
| DPrice_ι_price_ => fst11 r 
 | DPrice_ι_sells_amount_ => snd ( fst10 r ) 
 | DPrice_ι_buys_amount_ => snd ( fst9 r ) 
 | DPrice_ι_stock_ => snd ( fst8 r ) 
 | DPrice_ι_min_amount_ => snd ( fst7 r ) 
 | DPrice_ι_deals_limit_ => snd ( fst6 r ) 
 | DPrice_ι_notify_addr_ => snd ( fst5 r ) 
 | DPrice_ι_workchain_id_ => snd ( fst4 r ) 
 | DPrice_ι_tons_cfg_ => snd ( fst3 r ) 
 | DPrice_ι_tip3cfg_ => snd ( fst2 r ) 
 | DPrice_ι_sells_ => snd ( fst1 r ) 
 | DPrice_ι_buys_ => snd r 
 end . 

 
Coercion DPrice_get : DPrice >-> Funclass. 

 
Definition DPrice_set (f: DPrice ) 
(v: DPrice_field_type f) (r: DPriceP ): DPriceP  :=
  match f, v with 
| DPrice_ι_price_ v' => ( v' , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_sells_amount_ v' => ( fst11 , v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_buys_amount_ v' => ( fst11 , snd ( fst10 r ) , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_stock_ v' => ( fst11 , snd ( fst10 r ) , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_min_amount_ v' => ( fst11 , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_deals_limit_ v' => ( fst11 , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_notify_addr_ v' => ( fst11 , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_workchain_id_ v' => ( fst11 , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_tons_cfg_ v' => ( fst11 , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_tip3cfg_ v' => ( fst11 , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_sells_ v' => ( fst11 , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | DPrice_ι_buys_ v' => ( fst11 , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance DPrice_set_Record : PruvendoRecord DPriceP DPriceFields :=
{
  field_type := DPrice_field_type; 
  getPruvendoRecord := @DPrice_get ;
  setPruvendoRecord := @DPrice_set ;
}. 

 
Inductive TonsConfig := 
| TonsConfig_ι_transfer_tip3 
| TonsConfig_ι_return_ownership 
| TonsConfig_ι_trading_pair_deploy 
| TonsConfig_ι_order_answer 
| TonsConfig_ι_process_queue 
| TonsConfig_ι_send_notify 

. 
Definition TonsConfigP := ( 
I128 * I128 * I128 * I128 * I128 * I128 )%type . 

 
Definition TonsConfig_field_type f : Type :=  
match f with 
| TonsConfig_ι_transfer_tip3 => I128 
| TonsConfig_ι_return_ownership => I128 
| TonsConfig_ι_trading_pair_deploy => I128 
| TonsConfig_ι_order_answer => I128 
| TonsConfig_ι_process_queue => I128 
| TonsConfig_ι_send_notify => I128 

end . 

 
Definition TonsConfig_get (f: TonsConfig )(r: TonsConfigP ) :  TonsConfig_field_type f := 
 match f with 
| TonsConfig_ι_transfer_tip3 => fst5 r 
 | TonsConfig_ι_return_ownership => snd ( fst4 r ) 
 | TonsConfig_ι_trading_pair_deploy => snd ( fst3 r ) 
 | TonsConfig_ι_order_answer => snd ( fst2 r ) 
 | TonsConfig_ι_process_queue => snd ( fst1 r ) 
 | TonsConfig_ι_send_notify => snd r 
 end . 

 
Coercion TonsConfig_get : TonsConfig >-> Funclass. 

 
Definition TonsConfig_set (f: TonsConfig ) 
(v: TonsConfig_field_type f) (r: TonsConfigP ): TonsConfigP  :=
  match f, v with 
| TonsConfig_ι_transfer_tip3 v' => ( v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_return_ownership v' => ( fst5 , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_trading_pair_deploy v' => ( fst5 , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_order_answer v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_process_queue v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | TonsConfig_ι_send_notify v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance TonsConfig_set_Record : PruvendoRecord TonsConfigP TonsConfigFields :=
{
  field_type := TonsConfig_field_type; 
  getPruvendoRecord := @TonsConfig_get ;
  setPruvendoRecord := @TonsConfig_set ;
}. 

 
Inductive DStock := 
| DStock_ι_deployer_pubkey_ 
| DStock_ι_tons_cfg_ 
| DStock_ι_pair_code_ 
| DStock_ι_price_code_ 
| DStock_ι_min_amount_ 
| DStock_ι_deals_limit_ 
| DStock_ι_notify_addr_ 

. 
Definition DStockP := ( 
I256 * TonsConfigP * M C * M C * I128 * I8 * A )%type . 

 
Definition DStock_field_type f : Type :=  
match f with 
| DStock_ι_deployer_pubkey_ => I256 
| DStock_ι_tons_cfg_ => TonsConfigP 
| DStock_ι_pair_code_ => M C 
| DStock_ι_price_code_ => M C 
| DStock_ι_min_amount_ => I128 
| DStock_ι_deals_limit_ => I8 
| DStock_ι_notify_addr_ => A 

end . 

 
Definition DStock_get (f: DStock )(r: DStockP ) :  DStock_field_type f := 
 match f with 
| DStock_ι_deployer_pubkey_ => fst6 r 
 | DStock_ι_tons_cfg_ => snd ( fst5 r ) 
 | DStock_ι_pair_code_ => snd ( fst4 r ) 
 | DStock_ι_price_code_ => snd ( fst3 r ) 
 | DStock_ι_min_amount_ => snd ( fst2 r ) 
 | DStock_ι_deals_limit_ => snd ( fst1 r ) 
 | DStock_ι_notify_addr_ => snd r 
 end . 

 
Coercion DStock_get : DStock >-> Funclass. 

 
Definition DStock_set (f: DStock ) 
(v: DStock_field_type f) (r: DStockP ): DStockP  :=
  match f, v with 
| DStock_ι_deployer_pubkey_ v' => ( v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DStock_ι_tons_cfg_ v' => ( fst6 , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DStock_ι_pair_code_ v' => ( fst6 , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DStock_ι_price_code_ v' => ( fst6 , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DStock_ι_min_amount_ v' => ( fst6 , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | DStock_ι_deals_limit_ v' => ( fst6 , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | DStock_ι_notify_addr_ v' => ( fst6 , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance DStock_set_Record : PruvendoRecord DStockP DStockFields :=
{
  field_type := DStock_field_type; 
  getPruvendoRecord := @DStock_get ;
  setPruvendoRecord := @DStock_set ;
}. 

 
Inductive DTradingPair := 
| DTradingPair_ι_stock_addr_ 
| DTradingPair_ι_tip3_root_ 
| DTradingPair_ι_deploy_value_ 

. 
Definition DTradingPairP := ( 
A * A * I128 )%type . 

 
Definition DTradingPair_field_type f : Type :=  
match f with 
| DTradingPair_ι_stock_addr_ => A 
| DTradingPair_ι_tip3_root_ => A 
| DTradingPair_ι_deploy_value_ => I128 

end . 

 
Definition DTradingPair_get (f: DTradingPair )(r: DTradingPairP ) :  DTradingPair_field_type f := 
 match f with 
| DTradingPair_ι_stock_addr_ => fst2 r 
 | DTradingPair_ι_tip3_root_ => snd ( fst1 r ) 
 | DTradingPair_ι_deploy_value_ => snd r 
 end . 

 
Coercion DTradingPair_get : DTradingPair >-> Funclass. 

 
Definition DTradingPair_set (f: DTradingPair ) 
(v: DTradingPair_field_type f) (r: DTradingPairP ): DTradingPairP  :=
  match f, v with 
| DTradingPair_ι_stock_addr_ v' => ( v' , snd ( fst1 r ) , snd r ) 
 | DTradingPair_ι_tip3_root_ v' => ( fst2 , v' , snd r ) 
 | DTradingPair_ι_deploy_value_ v' => ( fst2 , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance DTradingPair_set_Record : PruvendoRecord DTradingPairP DTradingPairFields :=
{
  field_type := DTradingPair_field_type; 
  getPruvendoRecord := @DTradingPair_get ;
  setPruvendoRecord := @DTradingPair_set ;
}. 

 
Inductive FLeXSellArgsAddrs := 
| FLeXSellArgsAddrs_ι_my_tip3_addr 
| FLeXSellArgsAddrs_ι_receive_wallet 

. 
Definition FLeXSellArgsAddrsP := ( 
A * A )%type . 

 
Definition FLeXSellArgsAddrs_field_type f : Type :=  
match f with 
| FLeXSellArgsAddrs_ι_my_tip3_addr => A 
| FLeXSellArgsAddrs_ι_receive_wallet => A 

end . 

 
Definition FLeXSellArgsAddrs_get (f: FLeXSellArgsAddrs )(r: FLeXSellArgsAddrsP ) :  FLeXSellArgsAddrs_field_type f := 
 match f with 
| FLeXSellArgsAddrs_ι_my_tip3_addr => fst1 r 
 | FLeXSellArgsAddrs_ι_receive_wallet => snd r 
 end . 

 
Coercion FLeXSellArgsAddrs_get : FLeXSellArgsAddrs >-> Funclass. 

 
Definition FLeXSellArgsAddrs_set (f: FLeXSellArgsAddrs ) 
(v: FLeXSellArgsAddrs_field_type f) (r: FLeXSellArgsAddrsP ): FLeXSellArgsAddrsP  :=
  match f, v with 
| FLeXSellArgsAddrs_ι_my_tip3_addr v' => ( v' , snd r ) 
 | FLeXSellArgsAddrs_ι_receive_wallet v' => ( fst1 , v' ) 
 end . 

 
Global Instance FLeXSellArgsAddrs_set_Record : PruvendoRecord FLeXSellArgsAddrsP FLeXSellArgsAddrsFields :=
{
  field_type := FLeXSellArgsAddrs_field_type; 
  getPruvendoRecord := @FLeXSellArgsAddrs_get ;
  setPruvendoRecord := @FLeXSellArgsAddrs_set ;
}. 

 
Inductive FLeXSellArgs := 
| FLeXSellArgs_ι_price 
| FLeXSellArgs_ι_amount 
| FLeXSellArgs_ι_lend_finish_time 
| FLeXSellArgs_ι_min_amount 
| FLeXSellArgs_ι_deals_limit 
| FLeXSellArgs_ι_tons_value 
| FLeXSellArgs_ι_price_code 
| FLeXSellArgs_ι_addrs 
| FLeXSellArgs_ι_tip3cfg 

. 
Definition FLeXSellArgsP := ( 
I128 * I128 * I32 * I128 * I8 * I128 * C * ref FLeXSellArgsAddrsP * ref Tip3ConfigP )%type . 

 
Definition FLeXSellArgs_field_type f : Type :=  
match f with 
| FLeXSellArgs_ι_price => I128 
| FLeXSellArgs_ι_amount => I128 
| FLeXSellArgs_ι_lend_finish_time => I32 
| FLeXSellArgs_ι_min_amount => I128 
| FLeXSellArgs_ι_deals_limit => I8 
| FLeXSellArgs_ι_tons_value => I128 
| FLeXSellArgs_ι_price_code => C 
| FLeXSellArgs_ι_addrs => ref FLeXSellArgsAddrsP 
| FLeXSellArgs_ι_tip3cfg => ref Tip3ConfigP 

end . 

 
Definition FLeXSellArgs_get (f: FLeXSellArgs )(r: FLeXSellArgsP ) :  FLeXSellArgs_field_type f := 
 match f with 
| FLeXSellArgs_ι_price => fst8 r 
 | FLeXSellArgs_ι_amount => snd ( fst7 r ) 
 | FLeXSellArgs_ι_lend_finish_time => snd ( fst6 r ) 
 | FLeXSellArgs_ι_min_amount => snd ( fst5 r ) 
 | FLeXSellArgs_ι_deals_limit => snd ( fst4 r ) 
 | FLeXSellArgs_ι_tons_value => snd ( fst3 r ) 
 | FLeXSellArgs_ι_price_code => snd ( fst2 r ) 
 | FLeXSellArgs_ι_addrs => snd ( fst1 r ) 
 | FLeXSellArgs_ι_tip3cfg => snd r 
 end . 

 
Coercion FLeXSellArgs_get : FLeXSellArgs >-> Funclass. 

 
Definition FLeXSellArgs_set (f: FLeXSellArgs ) 
(v: FLeXSellArgs_field_type f) (r: FLeXSellArgsP ): FLeXSellArgsP  :=
  match f, v with 
| FLeXSellArgs_ι_price v' => ( v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_amount v' => ( fst8 , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_lend_finish_time v' => ( fst8 , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_min_amount v' => ( fst8 , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_deals_limit v' => ( fst8 , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_tons_value v' => ( fst8 , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_price_code v' => ( fst8 , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_addrs v' => ( fst8 , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXSellArgs_ι_tip3cfg v' => ( fst8 , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance FLeXSellArgs_set_Record : PruvendoRecord FLeXSellArgsP FLeXSellArgsFields :=
{
  field_type := FLeXSellArgs_field_type; 
  getPruvendoRecord := @FLeXSellArgs_get ;
  setPruvendoRecord := @FLeXSellArgs_set ;
}. 

 
Inductive FLeXBuyArgs := 
| FLeXBuyArgs_ι_price 
| FLeXBuyArgs_ι_amount 
| FLeXBuyArgs_ι_min_amount 
| FLeXBuyArgs_ι_deals_limit 
| FLeXBuyArgs_ι_deploy_value 
| FLeXBuyArgs_ι_price_code 
| FLeXBuyArgs_ι_my_tip3_addr 
| FLeXBuyArgs_ι_tip3cfg 

. 
Definition FLeXBuyArgsP := ( 
I128 * I128 * I128 * I8 * I128 * C * A * ref Tip3ConfigP )%type . 

 
Definition FLeXBuyArgs_field_type f : Type :=  
match f with 
| FLeXBuyArgs_ι_price => I128 
| FLeXBuyArgs_ι_amount => I128 
| FLeXBuyArgs_ι_min_amount => I128 
| FLeXBuyArgs_ι_deals_limit => I8 
| FLeXBuyArgs_ι_deploy_value => I128 
| FLeXBuyArgs_ι_price_code => C 
| FLeXBuyArgs_ι_my_tip3_addr => A 
| FLeXBuyArgs_ι_tip3cfg => ref Tip3ConfigP 

end . 

 
Definition FLeXBuyArgs_get (f: FLeXBuyArgs )(r: FLeXBuyArgsP ) :  FLeXBuyArgs_field_type f := 
 match f with 
| FLeXBuyArgs_ι_price => fst7 r 
 | FLeXBuyArgs_ι_amount => snd ( fst6 r ) 
 | FLeXBuyArgs_ι_min_amount => snd ( fst5 r ) 
 | FLeXBuyArgs_ι_deals_limit => snd ( fst4 r ) 
 | FLeXBuyArgs_ι_deploy_value => snd ( fst3 r ) 
 | FLeXBuyArgs_ι_price_code => snd ( fst2 r ) 
 | FLeXBuyArgs_ι_my_tip3_addr => snd ( fst1 r ) 
 | FLeXBuyArgs_ι_tip3cfg => snd r 
 end . 

 
Coercion FLeXBuyArgs_get : FLeXBuyArgs >-> Funclass. 

 
Definition FLeXBuyArgs_set (f: FLeXBuyArgs ) 
(v: FLeXBuyArgs_field_type f) (r: FLeXBuyArgsP ): FLeXBuyArgsP  :=
  match f, v with 
| FLeXBuyArgs_ι_price v' => ( v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_amount v' => ( fst7 , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_min_amount v' => ( fst7 , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_deals_limit v' => ( fst7 , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_deploy_value v' => ( fst7 , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_price_code v' => ( fst7 , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_my_tip3_addr v' => ( fst7 , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXBuyArgs_ι_tip3cfg v' => ( fst7 , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance FLeXBuyArgs_set_Record : PruvendoRecord FLeXBuyArgsP FLeXBuyArgsFields :=
{
  field_type := FLeXBuyArgs_field_type; 
  getPruvendoRecord := @FLeXBuyArgs_get ;
  setPruvendoRecord := @FLeXBuyArgs_set ;
}. 

 
Inductive FLeXCancelArgs := 
| FLeXCancelArgs_ι_price 
| FLeXCancelArgs_ι_min_amount 
| FLeXCancelArgs_ι_deals_limit 
| FLeXCancelArgs_ι_value 
| FLeXCancelArgs_ι_price_code 
| FLeXCancelArgs_ι_tip3cfg 

. 
Definition FLeXCancelArgsP := ( 
I128 * I128 * I8 * I128 * C * ref Tip3ConfigP )%type . 

 
Definition FLeXCancelArgs_field_type f : Type :=  
match f with 
| FLeXCancelArgs_ι_price => I128 
| FLeXCancelArgs_ι_min_amount => I128 
| FLeXCancelArgs_ι_deals_limit => I8 
| FLeXCancelArgs_ι_value => I128 
| FLeXCancelArgs_ι_price_code => C 
| FLeXCancelArgs_ι_tip3cfg => ref Tip3ConfigP 

end . 

 
Definition FLeXCancelArgs_get (f: FLeXCancelArgs )(r: FLeXCancelArgsP ) :  FLeXCancelArgs_field_type f := 
 match f with 
| FLeXCancelArgs_ι_price => fst5 r 
 | FLeXCancelArgs_ι_min_amount => snd ( fst4 r ) 
 | FLeXCancelArgs_ι_deals_limit => snd ( fst3 r ) 
 | FLeXCancelArgs_ι_value => snd ( fst2 r ) 
 | FLeXCancelArgs_ι_price_code => snd ( fst1 r ) 
 | FLeXCancelArgs_ι_tip3cfg => snd r 
 end . 

 
Coercion FLeXCancelArgs_get : FLeXCancelArgs >-> Funclass. 

 
Definition FLeXCancelArgs_set (f: FLeXCancelArgs ) 
(v: FLeXCancelArgs_field_type f) (r: FLeXCancelArgsP ): FLeXCancelArgsP  :=
  match f, v with 
| FLeXCancelArgs_ι_price v' => ( v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_min_amount v' => ( fst5 , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_deals_limit v' => ( fst5 , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_value v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_price_code v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXCancelArgs_ι_tip3cfg v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance FLeXCancelArgs_set_Record : PruvendoRecord FLeXCancelArgsP FLeXCancelArgsFields :=
{
  field_type := FLeXCancelArgs_field_type; 
  getPruvendoRecord := @FLeXCancelArgs_get ;
  setPruvendoRecord := @FLeXCancelArgs_set ;
}. 

 
Inductive DFLeXClient := 
| DFLeXClient_ι_owner_ 
| DFLeXClient_ι_trading_pair_code_ 
| DFLeXClient_ι_workchain_id_ 
| DFLeXClient_ι_tons_cfg_ 
| DFLeXClient_ι_stock_ 
| DFLeXClient_ι_notify_addr_ 

. 
Definition DFLeXClientP := ( 
I256 * C * I8 * TonsConfigP * A * A )%type . 

 
Definition DFLeXClient_field_type f : Type :=  
match f with 
| DFLeXClient_ι_owner_ => I256 
| DFLeXClient_ι_trading_pair_code_ => C 
| DFLeXClient_ι_workchain_id_ => I8 
| DFLeXClient_ι_tons_cfg_ => TonsConfigP 
| DFLeXClient_ι_stock_ => A 
| DFLeXClient_ι_notify_addr_ => A 

end . 

 
Definition DFLeXClient_get (f: DFLeXClient )(r: DFLeXClientP ) :  DFLeXClient_field_type f := 
 match f with 
| DFLeXClient_ι_owner_ => fst5 r 
 | DFLeXClient_ι_trading_pair_code_ => snd ( fst4 r ) 
 | DFLeXClient_ι_workchain_id_ => snd ( fst3 r ) 
 | DFLeXClient_ι_tons_cfg_ => snd ( fst2 r ) 
 | DFLeXClient_ι_stock_ => snd ( fst1 r ) 
 | DFLeXClient_ι_notify_addr_ => snd r 
 end . 

 
Coercion DFLeXClient_get : DFLeXClient >-> Funclass. 

 
Definition DFLeXClient_set (f: DFLeXClient ) 
(v: DFLeXClient_field_type f) (r: DFLeXClientP ): DFLeXClientP  :=
  match f, v with 
| DFLeXClient_ι_owner_ v' => ( v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DFLeXClient_ι_trading_pair_code_ v' => ( fst5 , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DFLeXClient_ι_workchain_id_ v' => ( fst5 , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DFLeXClient_ι_tons_cfg_ v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | DFLeXClient_ι_stock_ v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | DFLeXClient_ι_notify_addr_ v' => ( fst5 , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance DFLeXClient_set_Record : PruvendoRecord DFLeXClientP DFLeXClientFields :=
{
  field_type := DFLeXClient_field_type; 
  getPruvendoRecord := @DFLeXClient_get ;
  setPruvendoRecord := @DFLeXClient_set ;
}. 

 
Inductive process_ret := 
| process_ret_ι_sells_amount 
| process_ret_ι_sells_ 
| process_ret_ι_buys_amount 
| process_ret_ι_buys_ 
| process_ret_ι_ret_ 

. 
Definition process_retP := ( 
I128 * Q SellInfoP * I128 * Q BuyInfoP * M OrderRetP )%type . 

 
Definition process_ret_field_type f : Type :=  
match f with 
| process_ret_ι_sells_amount => I128 
| process_ret_ι_sells_ => Q SellInfoP 
| process_ret_ι_buys_amount => I128 
| process_ret_ι_buys_ => Q BuyInfoP 
| process_ret_ι_ret_ => M OrderRetP 

end . 

 
Definition process_ret_get (f: process_ret )(r: process_retP ) :  process_ret_field_type f := 
 match f with 
| process_ret_ι_sells_amount => fst4 r 
 | process_ret_ι_sells_ => snd ( fst3 r ) 
 | process_ret_ι_buys_amount => snd ( fst2 r ) 
 | process_ret_ι_buys_ => snd ( fst1 r ) 
 | process_ret_ι_ret_ => snd r 
 end . 

 
Coercion process_ret_get : process_ret >-> Funclass. 

 
Definition process_ret_set (f: process_ret ) 
(v: process_ret_field_type f) (r: process_retP ): process_retP  :=
  match f, v with 
| process_ret_ι_sells_amount v' => ( v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | process_ret_ι_sells_ v' => ( fst4 , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | process_ret_ι_buys_amount v' => ( fst4 , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | process_ret_ι_buys_ v' => ( fst4 , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | process_ret_ι_ret_ v' => ( fst4 , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance process_ret_set_Record : PruvendoRecord process_retP process_retFields :=
{
  field_type := process_ret_field_type; 
  getPruvendoRecord := @process_ret_get ;
  setPruvendoRecord := @process_ret_set ;
}. 

 
Inductive dealer := 
| dealer_ι_tip3root_ 
| dealer_ι_notify_addr_ 
| dealer_ι_price_ 
| dealer_ι_deals_limit_ 
| dealer_ι_tons_cfg_ 
| dealer_ι_sells_amount_ 
| dealer_ι_buys_amount_ 

. 
Definition dealerP := ( 
A * IStockNotifyPtrP * I128 * I * TonsConfigP * I128 * I128 )%type . 

 
Definition dealer_field_type f : Type :=  
match f with 
| dealer_ι_tip3root_ => A 
| dealer_ι_notify_addr_ => IStockNotifyPtrP 
| dealer_ι_price_ => I128 
| dealer_ι_deals_limit_ => I 
| dealer_ι_tons_cfg_ => TonsConfigP 
| dealer_ι_sells_amount_ => I128 
| dealer_ι_buys_amount_ => I128 

end . 

 
Definition dealer_get (f: dealer )(r: dealerP ) :  dealer_field_type f := 
 match f with 
| dealer_ι_tip3root_ => fst6 r 
 | dealer_ι_notify_addr_ => snd ( fst5 r ) 
 | dealer_ι_price_ => snd ( fst4 r ) 
 | dealer_ι_deals_limit_ => snd ( fst3 r ) 
 | dealer_ι_tons_cfg_ => snd ( fst2 r ) 
 | dealer_ι_sells_amount_ => snd ( fst1 r ) 
 | dealer_ι_buys_amount_ => snd r 
 end . 

 
Coercion dealer_get : dealer >-> Funclass. 

 
Definition dealer_set (f: dealer ) 
(v: dealer_field_type f) (r: dealerP ): dealerP  :=
  match f, v with 
| dealer_ι_tip3root_ v' => ( v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_notify_addr_ v' => ( fst6 , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_price_ v' => ( fst6 , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_deals_limit_ v' => ( fst6 , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_tons_cfg_ v' => ( fst6 , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | dealer_ι_sells_amount_ v' => ( fst6 , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | dealer_ι_buys_amount_ v' => ( fst6 , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end . 

 
Global Instance dealer_set_Record : PruvendoRecord dealerP dealerFields :=
{
  field_type := dealer_field_type; 
  getPruvendoRecord := @dealer_get ;
  setPruvendoRecord := @dealer_set ;
}. 

 
Class PruvendoRecord R F :=
{
  field_type: F -> Type;
  getPruvendoRecord: forall (f: F), R -> field_type f;
  setPruvendoRecord: forall (f: F), field_type f -> R -> R;
}. 
(* LocalState *) 
Notation "'{$$' r 'With' y ':=' v '$$}'" := (@setPruvendoRecord _ _ _ y v r) : struct_scope.
 
Lemma no_Tip3Config_eq : forall (f1 f2: Tip3Config) (v2: field_type f2) (r : Tip3ConfigP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma Tip3Config_eq : forall (f2: Tip3Config) (v2: field_type f2) (r : Tip3ConfigP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_OrderRet_eq : forall (f1 f2: OrderRet) (v2: field_type f2) (r : OrderRetP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma OrderRet_eq : forall (f2: OrderRet) (v2: field_type f2) (r : OrderRetP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_SellArgs_eq : forall (f1 f2: SellArgs) (v2: field_type f2) (r : SellArgsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma SellArgs_eq : forall (f2: SellArgs) (v2: field_type f2) (r : SellArgsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_SellInfo_eq : forall (f1 f2: SellInfo) (v2: field_type f2) (r : SellInfoP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma SellInfo_eq : forall (f2: SellInfo) (v2: field_type f2) (r : SellInfoP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_BuyInfo_eq : forall (f1 f2: BuyInfo) (v2: field_type f2) (r : BuyInfoP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma BuyInfo_eq : forall (f2: BuyInfo) (v2: field_type f2) (r : BuyInfoP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DetailsInfo_eq : forall (f1 f2: DetailsInfo) (v2: field_type f2) (r : DetailsInfoP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DetailsInfo_eq : forall (f2: DetailsInfo) (v2: field_type f2) (r : DetailsInfoP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DPrice_eq : forall (f1 f2: DPrice) (v2: field_type f2) (r : DPriceP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DPrice_eq : forall (f2: DPrice) (v2: field_type f2) (r : DPriceP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_TonsConfig_eq : forall (f1 f2: TonsConfig) (v2: field_type f2) (r : TonsConfigP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma TonsConfig_eq : forall (f2: TonsConfig) (v2: field_type f2) (r : TonsConfigP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DStock_eq : forall (f1 f2: DStock) (v2: field_type f2) (r : DStockP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DStock_eq : forall (f2: DStock) (v2: field_type f2) (r : DStockP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DTradingPair_eq : forall (f1 f2: DTradingPair) (v2: field_type f2) (r : DTradingPairP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DTradingPair_eq : forall (f2: DTradingPair) (v2: field_type f2) (r : DTradingPairP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_FLeXSellArgsAddrs_eq : forall (f1 f2: FLeXSellArgsAddrs) (v2: field_type f2) (r : FLeXSellArgsAddrsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma FLeXSellArgsAddrs_eq : forall (f2: FLeXSellArgsAddrs) (v2: field_type f2) (r : FLeXSellArgsAddrsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_FLeXSellArgs_eq : forall (f1 f2: FLeXSellArgs) (v2: field_type f2) (r : FLeXSellArgsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma FLeXSellArgs_eq : forall (f2: FLeXSellArgs) (v2: field_type f2) (r : FLeXSellArgsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_FLeXBuyArgs_eq : forall (f1 f2: FLeXBuyArgs) (v2: field_type f2) (r : FLeXBuyArgsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma FLeXBuyArgs_eq : forall (f2: FLeXBuyArgs) (v2: field_type f2) (r : FLeXBuyArgsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_FLeXCancelArgs_eq : forall (f1 f2: FLeXCancelArgs) (v2: field_type f2) (r : FLeXCancelArgsP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma FLeXCancelArgs_eq : forall (f2: FLeXCancelArgs) (v2: field_type f2) (r : FLeXCancelArgsP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 
Lemma no_DFLeXClient_eq : forall (f1 f2: DFLeXClient) (v2: field_type f2) (r : DFLeXClientP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma DFLeXClient_eq : forall (f2: DFLeXClient) (v2: field_type f2) (r : DFLeXClientP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 

Lemma no_process_ret_eq : forall (f1 f2: process_ret) (v2: field_type f2) (r : process_retP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma process_ret_eq : forall (f2: process_ret) (v2: field_type f2) (r : process_retP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 



Lemma no_dealer_eq : forall (f1 f2: dealer) (v2: field_type f2) (r : dealerP ) ,  
f1 <> f2 -> 
f1 {$$ r With f2 := v2 $$} = f1 r.
Proof.
intros.
destruct r. destruct p.
destruct f1; destruct f2; auto; try contradiction.
Qed.

Lemma dealer_eq : forall (f2: dealer) (v2: field_type f2) (r : dealerP ) ,  
f2 {$$ r With f2 := v2 $$} = v2.
Proof.
intros.
destruct r. destruct p.
destruct f2; auto.
Qed. 





