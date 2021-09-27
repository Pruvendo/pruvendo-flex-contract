
 
 Require Import Coq.Program.Basics. 
 Require Import Coq.Logic.FunctionalExtensionality. 
 Require Import Coq.Program.Combinators. 
 Require Import FinProof.ProgrammingWith. 
 Require Import String. 
 
 Require Import FinProof.ProgrammingWith. 
 Require Import FinProof.Types.IsoTypes. 
 Require Import FinProof.Common. 
 Require Import FinProof.MonadTransformers21. 
 Require Import FinProof.StateMonad21. 
 Require Import FinProof.EpsilonMonad. 
 
 Require Import UMLang.SolidityNotations2. 
 Require Import UMLang.SML_NG28. 
 Require Import UrsusTVM.tvmFunc. 
 
 Local Open Scope record. 
 Local Open Scope program_scope. 
 
 Require Import UMLang.ProofEnvironment2. 
 
 
 Module LedgerPriceClass (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 
 
 
 Module Export SolidityNotationsClass := SolidityNotations xt sm. 
 Module Export VMStateModule := VMStateModule xt sm. 
 
 Import xt. 
 Existing Instance monadStateT. 
 Existing Instance monadStateStateT. 
 
 Definition IFLeXNotifyPtr := XAddress. 
 Definition ITONTokenWalletPtr := XAddress. 
 Definition IPricePtr := XAddress. 
 Definition TokensType := XInteger128. 
 Definition WalletGramsType := XInteger128. 
 Definition Grams := XInteger16 . 
 Definition auto := XInteger . 
 Definition addr_std_compact := XAddress . 
 

(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 2 *) Definition TickTock := 
 ( XBool * 
 XBool )%type .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 2 *) Definition StateInit := 
 ( XMaybe XInteger * 
 XMaybe TickTock * 
 XMaybe XCell * 
 XMaybe XCell * 
 XMaybe XCell )%type .
(* 1 *) Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address .
(* 2 *) Definition addr_std_fixed := 
 ( XInteger8 * 
 XInteger256 )%type .
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 2 *) Definition TonsConfig := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 )%type .
(* 1 *) Inductive OrderRetFields := | OrderRet_ι_err_code | OrderRet_ι_processed | OrderRet_ι_enqueued .
(* 2 *) Definition OrderRet := 
 ( XInteger32 * 
 XInteger128 * 
 XInteger128 )%type .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
(* 2 *) Definition SellArgs := 
 ( XInteger128 * 
 XAddress )%type .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 2 *) Definition OrderInfo := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 addr_std_fixed * 
 addr_std_fixed * 
 XInteger32 )%type .
(* 1 *) Inductive DetailsInfoFields := | DetailsInfo_ι_price | DetailsInfo_ι_min_amount | DetailsInfo_ι_sell_amount | DetailsInfo_ι_buy_amount .
(* 2 *) Definition DetailsInfo := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 )%type .
(* 1 *) Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address .
(* 2 *) Definition Tip3Config := 
 ( XString * 
 XString * 
 XInteger8 * 
 XInteger256 * 
 XAddress )%type .
(* 1 *) Inductive PriceFields := | Price_ι_price_ | Price_ι_sells_amount_ | Price_ι_buys_amount_ | Price_ι_flex_ | Price_ι_min_amount_ | Price_ι_deals_limit_ | Price_ι_notify_addr_ | Price_ι_workchain_id_ | Price_ι_tons_cfg_ | Price_ι_tip3_code_ | Price_ι_tip3cfg_ | Price_ι_sells_ | Price_ι_buys_ .
(* 2 *) Definition Price := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 addr_std_fixed * 
 XInteger128 * 
 XInteger8 * 
 XAddress * 
 XInteger8 * 
 TonsConfig * 
 XCell * 
 Tip3Config * 
 XList OrderInfo * 
 XList OrderInfo )%type .
(* 1 *) Inductive dealerFields := | dealer_ι_tip3root_ | dealer_ι_notify_addr_ | dealer_ι_price_ | dealer_ι_deals_limit_ | dealer_ι_tons_cfg_ | dealer_ι_sells_amount_ | dealer_ι_sells_ | dealer_ι_buys_amount_ | dealer_ι_buys_ | dealer_ι_ret_ .
(* 2 *) Definition dealer := 
 ( XAddress * 
 XAddress * 
 XInteger128 * 
 XInteger * 
 TonsConfig * 
 XInteger128 * 
 XList OrderInfo * 
 XInteger128 * 
 XList OrderInfo * 
 XMaybe OrderRet )%type .
(* 1 *) Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_sells_ | process_ret_ι_buys_amount | process_ret_ι_buys_ | process_ret_ι_ret_ .
(* 2 *) Definition process_ret := 
 ( XInteger128 * 
 XList OrderInfo * 
 XInteger128 * 
 XList OrderInfo * 
 XMaybe OrderRet )%type .
(* 1 *) Inductive lend_ownership_infoFields := | lend_ownership_info_ι_owner | lend_ownership_info_ι_lend_balance | lend_ownership_info_ι_lend_finish_time .
(* 2 *) Definition lend_ownership_info := 
 ( XAddress * 
 TokensType * 
 XInteger32 )%type .
(* 1 *) Inductive allowance_infoFields := | allowance_info_ι_spender | allowance_info_ι_remainingTokens .
(* 2 *) Definition allowance_info := 
 ( XAddress * 
 TokensType )%type .
(* 1 *) Inductive TONTokenWalletFields := | TONTokenWallet_ι_name_ | TONTokenWallet_ι_symbol_ | TONTokenWallet_ι_decimals_ | TONTokenWallet_ι_balance_ | TONTokenWallet_ι_root_public_key_ | TONTokenWallet_ι_wallet_public_key_ | TONTokenWallet_ι_root_address_ | TONTokenWallet_ι_owner_address_ | TONTokenWallet_ι_lend_ownership_ | TONTokenWallet_ι_code_ | TONTokenWallet_ι_allowance_ | TONTokenWallet_ι_workchain_id_ .
(* 2 *) Definition TONTokenWallet := 
 ( XList XInteger8 * 
 XList XInteger8 * 
 XInteger8 * 
 TokensType * 
 XInteger256 * 
 XInteger256 * 
 XAddress * 
 XMaybe XAddress * 
 XMaybe lend_ownership_info * 
 XCell * 
 XMaybe allowance_info * 
 XInteger8 )%type .
(* 1 *) Inductive OrderInfoXchgFields := | OrderInfoXchg_ι_original_amount | OrderInfoXchg_ι_amount | OrderInfoXchg_ι_account | OrderInfoXchg_ι_tip3_wallet_provide | OrderInfoXchg_ι_tip3_wallet_receive | OrderInfoXchg_ι_client_addr | OrderInfoXchg_ι_order_finish_time .
(* 2 *) Definition OrderInfoXchg := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 addr_std_fixed * 
 addr_std_fixed * 
 addr_std_fixed * 
 XInteger32 )%type .
(* 1 *) Inductive LocalStateFields := | LocalState_ι_cell | LocalState_ι_StateInit | LocalState_ι_tplStateInituint256 | LocalState_ι_bool | LocalState_ι_uint32 | LocalState_ι_Price | LocalState_ι_optuint128 | LocalState_ι_uint128 | LocalState_ι_tplboolbool | LocalState_ι_OrderInfo | LocalState_ι_int | LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfo | LocalState_ι_optpair_unsigned_OrderInfo__ | LocalState_ι_queueOrderInfo | LocalState_ι_OrderRet | LocalState_ι_unsigned | LocalState_ι_dealer | LocalState_ι_process_ret | LocalState_ι_uint8 | LocalState_ι_TonsConfig | LocalState_ι_tplqueue_OrderInfouint128 | LocalState_ι_addr_std_fixed | LocalState_ι_Grams | LocalState_ι_SellArgs | LocalState_ι_address | LocalState_ι_DetailsInfo | LocalState_ι_dict_arrayOrderInfo | LocalState_ι_optaddress | LocalState_ι_TONTokenWallet | LocalState_ι_tpladdressGrams | LocalState_ι_XSlice | LocalState_ι_optOrderRet | LocalState_ι_cellIndex | LocalState_ι_StateInitIndex | LocalState_ι_tplStateInituint256Index | LocalState_ι_boolIndex | LocalState_ι_uint32Index | LocalState_ι_PriceIndex | LocalState_ι_optuint128Index | LocalState_ι_uint128Index | LocalState_ι_tplboolboolIndex | LocalState_ι_OrderInfoIndex | LocalState_ι_intIndex | LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex | LocalState_ι_optpair_unsigned_OrderInfo__Index | LocalState_ι_queueOrderInfoIndex | LocalState_ι_OrderRetIndex | LocalState_ι_unsignedIndex | LocalState_ι_dealerIndex | LocalState_ι_process_retIndex | LocalState_ι_uint8Index | LocalState_ι_TonsConfigIndex | LocalState_ι_tplqueue_OrderInfouint128Index | LocalState_ι_addr_std_fixedIndex | LocalState_ι_GramsIndex | LocalState_ι_SellArgsIndex | LocalState_ι_addressIndex | LocalState_ι_DetailsInfoIndex | LocalState_ι_dict_arrayOrderInfoIndex | LocalState_ι_optaddressIndex | LocalState_ι_TONTokenWalletIndex | LocalState_ι_tpladdressGramsIndex | LocalState_ι_XSliceIndex | LocalState_ι_optOrderRetIndex .
(* 2 *) Definition LocalState := 
 ( XHMap (string*nat) XCell * 
 XHMap (string*nat) StateInit * 
 XHMap (string*nat) ( StateInit * XInteger256 ) * 
 XHMap (string*nat) XBool * 
 XHMap (string*nat) XInteger32 * 
 XHMap (string*nat) Price * 
 XHMap (string*nat) ( XMaybe XInteger128 ) * 
 XHMap (string*nat) XInteger128 * 
 XHMap (string*nat) ( XBool * XBool * XInteger128 ) * 
 XHMap (string*nat) OrderInfo * 
 XHMap (string*nat) XInteger * 
 XHMap (string*nat) (XMaybe (XInteger * OrderInfo) * (XList OrderInfo) * XInteger128 ) * 
 XHMap (string*nat) ( XMaybe (XInteger * OrderInfo) ) * 
 XHMap (string*nat) ( XList OrderInfo ) * 
 XHMap (string*nat) OrderRet * 
 XHMap (string*nat) XInteger * 
 XHMap (string*nat) dealer * 
 XHMap (string*nat) process_ret * 
 XHMap (string*nat) XInteger8 * 
 XHMap (string*nat) TonsConfig * 
 XHMap (string*nat) ( (XList OrderInfo) * XInteger128 ) * 
 XHMap (string*nat) addr_std_fixed * 
 XHMap (string*nat) Grams * 
 XHMap (string*nat) SellArgs * 
 XHMap (string*nat) XAddress * 
 XHMap (string*nat) DetailsInfo * 
 XHMap (string*nat) ( XHMap XInteger OrderInfo ) * 
 XHMap (string*nat) ( XMaybe XAddress ) * 
 XHMap (string*nat) TONTokenWallet * 
 XHMap (string*nat) ( XAddress * Grams ) * 
 XHMap (string*nat) XSlice * 
 XHMap (string*nat) ( XMaybe OrderRet ) * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat * 
 XHMap string nat )%type .
(* 1 *) Inductive LedgerFieldsI := | Ledger_ι_Price | Ledger_ι_VMState | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .
(* 2 *) Definition Ledger := 
 ( Price * 
 VMStateLRecord * 
 LocalState * 
 LocalState )%type .

 Definition LedgerFields := LedgerFieldsI. 


(* 3 *) Definition TickTock_field_type f : Type :=  
match f with 
 | TickTock_ι_tick => XBool | TickTock_ι_tock => XBool end .
(* 4 *) Definition TickTock_get (f: TickTockFields )(r: TickTock ) :  TickTock_field_type f := 
 let '( r1 , r2 ) := r in 
 match f with 
 | TickTock_ι_tick => r1 
 | TickTock_ι_tock => r2 
 end .
(* 5 *) Coercion TickTock_get : TickTockFields >-> Funclass .
(* 6 *) Definition TickTock_set (f: TickTockFields ) 
(v: TickTock_field_type f) (r: TickTock ): TickTock := 
 let '( r1 , r2 ) := r in 
 match f, v with 
 | TickTock_ι_tick , v' => ( v' , r2 ) 
 | TickTock_ι_tock , v' => ( r1 , v' ) 
 end .
(* 7 *) Global Instance TickTock_PruvendoRecord : PruvendoRecord TickTock TickTockFields :=
{
  field_type := TickTock_field_type; 
  getPruvendoRecord := @TickTock_get ;
  setPruvendoRecord := @TickTock_set ;
} .
(* 3 *) Definition StateInit_field_type f : Type :=  
match f with 
 | StateInit_ι_split_depth => XMaybe XInteger | StateInit_ι_special => XMaybe TickTock | StateInit_ι_code => XMaybe XCell | StateInit_ι_data => XMaybe XCell | StateInit_ι_library => XMaybe XCell end .
(* 4 *) Definition StateInit_get (f: StateInitFields )(r: StateInit ) :  StateInit_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 ) := r in 
 match f with 
 | StateInit_ι_split_depth => r1 
 | StateInit_ι_special => r2 
 | StateInit_ι_code => r3 
 | StateInit_ι_data => r4 
 | StateInit_ι_library => r5 
 end .
(* 5 *) Coercion StateInit_get : StateInitFields >-> Funclass .
(* 6 *) Definition StateInit_set (f: StateInitFields ) 
(v: StateInit_field_type f) (r: StateInit ): StateInit := 
 let '( r1 , r2 , r3 , r4 , r5 ) := r in 
 match f, v with 
 | StateInit_ι_split_depth , v' => ( v' , r2 , r3 , r4 , r5 ) 
 | StateInit_ι_special , v' => ( r1 , v' , r3 , r4 , r5 ) 
 | StateInit_ι_code , v' => ( r1 , r2 , v' , r4 , r5 ) 
 | StateInit_ι_data , v' => ( r1 , r2 , r3 , v' , r5 ) 
 | StateInit_ι_library , v' => ( r1 , r2 , r3 , r4 , v' ) 
 end .
(* 7 *) Global Instance StateInit_PruvendoRecord : PruvendoRecord StateInit StateInitFields :=
{
  field_type := StateInit_field_type; 
  getPruvendoRecord := @StateInit_get ;
  setPruvendoRecord := @StateInit_set ;
} .
(* 3 *) Definition addr_std_fixed_field_type f : Type :=  
match f with 
 | addr_std_fixed_ι_workchain_id => XInteger8 | addr_std_fixed_ι_address => XInteger256 end .
(* 4 *) Definition addr_std_fixed_get (f: addr_std_fixedFields )(r: addr_std_fixed ) :  addr_std_fixed_field_type f := 
 let '( r1 , r2 ) := r in 
 match f with 
 | addr_std_fixed_ι_workchain_id => r1 
 | addr_std_fixed_ι_address => r2 
 end .
(* 5 *) Coercion addr_std_fixed_get : addr_std_fixedFields >-> Funclass .
(* 6 *) Definition addr_std_fixed_set (f: addr_std_fixedFields ) 
(v: addr_std_fixed_field_type f) (r: addr_std_fixed ): addr_std_fixed := 
 let '( r1 , r2 ) := r in 
 match f, v with 
 | addr_std_fixed_ι_workchain_id , v' => ( v' , r2 ) 
 | addr_std_fixed_ι_address , v' => ( r1 , v' ) 
 end .
(* 7 *) Global Instance addr_std_fixed_PruvendoRecord : PruvendoRecord addr_std_fixed addr_std_fixedFields :=
{
  field_type := addr_std_fixed_field_type; 
  getPruvendoRecord := @addr_std_fixed_get ;
  setPruvendoRecord := @addr_std_fixed_set ;
} .
(* 3 *) Definition TonsConfig_field_type f : Type :=  
match f with 
 | TonsConfig_ι_transfer_tip3 => XInteger128 | TonsConfig_ι_return_ownership => XInteger128 | TonsConfig_ι_trading_pair_deploy => XInteger128 | TonsConfig_ι_order_answer => XInteger128 | TonsConfig_ι_process_queue => XInteger128 | TonsConfig_ι_send_notify => XInteger128 end .
(* 4 *) Definition TonsConfig_get (f: TonsConfigFields )(r: TonsConfig ) :  TonsConfig_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 ) := r in 
 match f with 
 | TonsConfig_ι_transfer_tip3 => r1 
 | TonsConfig_ι_return_ownership => r2 
 | TonsConfig_ι_trading_pair_deploy => r3 
 | TonsConfig_ι_order_answer => r4 
 | TonsConfig_ι_process_queue => r5 
 | TonsConfig_ι_send_notify => r6 
 end .
(* 5 *) Coercion TonsConfig_get : TonsConfigFields >-> Funclass .
(* 6 *) Definition TonsConfig_set (f: TonsConfigFields ) 
(v: TonsConfig_field_type f) (r: TonsConfig ): TonsConfig := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 ) := r in 
 match f, v with 
 | TonsConfig_ι_transfer_tip3 , v' => ( v' , r2 , r3 , r4 , r5 , r6 ) 
 | TonsConfig_ι_return_ownership , v' => ( r1 , v' , r3 , r4 , r5 , r6 ) 
 | TonsConfig_ι_trading_pair_deploy , v' => ( r1 , r2 , v' , r4 , r5 , r6 ) 
 | TonsConfig_ι_order_answer , v' => ( r1 , r2 , r3 , v' , r5 , r6 ) 
 | TonsConfig_ι_process_queue , v' => ( r1 , r2 , r3 , r4 , v' , r6 ) 
 | TonsConfig_ι_send_notify , v' => ( r1 , r2 , r3 , r4 , r5 , v' ) 
 end .
(* 7 *) Global Instance TonsConfig_PruvendoRecord : PruvendoRecord TonsConfig TonsConfigFields :=
{
  field_type := TonsConfig_field_type; 
  getPruvendoRecord := @TonsConfig_get ;
  setPruvendoRecord := @TonsConfig_set ;
} .
(* 3 *) Definition OrderRet_field_type f : Type :=  
match f with 
 | OrderRet_ι_err_code => XInteger32 | OrderRet_ι_processed => XInteger128 | OrderRet_ι_enqueued => XInteger128 end .
(* 4 *) Definition OrderRet_get (f: OrderRetFields )(r: OrderRet ) :  OrderRet_field_type f := 
 let '( r1 , r2 , r3 ) := r in 
 match f with 
 | OrderRet_ι_err_code => r1 
 | OrderRet_ι_processed => r2 
 | OrderRet_ι_enqueued => r3 
 end .
(* 5 *) Coercion OrderRet_get : OrderRetFields >-> Funclass .
(* 6 *) Definition OrderRet_set (f: OrderRetFields ) 
(v: OrderRet_field_type f) (r: OrderRet ): OrderRet := 
 let '( r1 , r2 , r3 ) := r in 
 match f, v with 
 | OrderRet_ι_err_code , v' => ( v' , r2 , r3 ) 
 | OrderRet_ι_processed , v' => ( r1 , v' , r3 ) 
 | OrderRet_ι_enqueued , v' => ( r1 , r2 , v' ) 
 end .
(* 7 *) Global Instance OrderRet_PruvendoRecord : PruvendoRecord OrderRet OrderRetFields :=
{
  field_type := OrderRet_field_type; 
  getPruvendoRecord := @OrderRet_get ;
  setPruvendoRecord := @OrderRet_set ;
} .
(* 3 *) Definition SellArgs_field_type f : Type :=  
match f with 
 | SellArgs_ι_amount => XInteger128 | SellArgs_ι_receive_wallet => XAddress end .
(* 4 *) Definition SellArgs_get (f: SellArgsFields )(r: SellArgs ) :  SellArgs_field_type f := 
 let '( r1 , r2 ) := r in 
 match f with 
 | SellArgs_ι_amount => r1 
 | SellArgs_ι_receive_wallet => r2 
 end .
(* 5 *) Coercion SellArgs_get : SellArgsFields >-> Funclass .
(* 6 *) Definition SellArgs_set (f: SellArgsFields ) 
(v: SellArgs_field_type f) (r: SellArgs ): SellArgs := 
 let '( r1 , r2 ) := r in 
 match f, v with 
 | SellArgs_ι_amount , v' => ( v' , r2 ) 
 | SellArgs_ι_receive_wallet , v' => ( r1 , v' ) 
 end .
(* 7 *) Global Instance SellArgs_PruvendoRecord : PruvendoRecord SellArgs SellArgsFields :=
{
  field_type := SellArgs_field_type; 
  getPruvendoRecord := @SellArgs_get ;
  setPruvendoRecord := @SellArgs_set ;
} .
(* 3 *) Definition OrderInfo_field_type f : Type :=  
match f with 
 | OrderInfo_ι_original_amount => XInteger128 | OrderInfo_ι_amount => XInteger128 | OrderInfo_ι_account => XInteger128 | OrderInfo_ι_tip3_wallet => addr_std_fixed | OrderInfo_ι_client_addr => addr_std_fixed | OrderInfo_ι_order_finish_time => XInteger32 end .
(* 4 *) Definition OrderInfo_get (f: OrderInfoFields )(r: OrderInfo ) :  OrderInfo_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 ) := r in 
 match f with 
 | OrderInfo_ι_original_amount => r1 
 | OrderInfo_ι_amount => r2 
 | OrderInfo_ι_account => r3 
 | OrderInfo_ι_tip3_wallet => r4 
 | OrderInfo_ι_client_addr => r5 
 | OrderInfo_ι_order_finish_time => r6 
 end .
(* 5 *) Coercion OrderInfo_get : OrderInfoFields >-> Funclass .
(* 6 *) Definition OrderInfo_set (f: OrderInfoFields ) 
(v: OrderInfo_field_type f) (r: OrderInfo ): OrderInfo := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 ) := r in 
 match f, v with 
 | OrderInfo_ι_original_amount , v' => ( v' , r2 , r3 , r4 , r5 , r6 ) 
 | OrderInfo_ι_amount , v' => ( r1 , v' , r3 , r4 , r5 , r6 ) 
 | OrderInfo_ι_account , v' => ( r1 , r2 , v' , r4 , r5 , r6 ) 
 | OrderInfo_ι_tip3_wallet , v' => ( r1 , r2 , r3 , v' , r5 , r6 ) 
 | OrderInfo_ι_client_addr , v' => ( r1 , r2 , r3 , r4 , v' , r6 ) 
 | OrderInfo_ι_order_finish_time , v' => ( r1 , r2 , r3 , r4 , r5 , v' ) 
 end .
(* 7 *) Global Instance OrderInfo_PruvendoRecord : PruvendoRecord OrderInfo OrderInfoFields :=
{
  field_type := OrderInfo_field_type; 
  getPruvendoRecord := @OrderInfo_get ;
  setPruvendoRecord := @OrderInfo_set ;
} .
(* 3 *) Definition DetailsInfo_field_type f : Type :=  
match f with 
 | DetailsInfo_ι_price => XInteger128 | DetailsInfo_ι_min_amount => XInteger128 | DetailsInfo_ι_sell_amount => XInteger128 | DetailsInfo_ι_buy_amount => XInteger128 end .
(* 4 *) Definition DetailsInfo_get (f: DetailsInfoFields )(r: DetailsInfo ) :  DetailsInfo_field_type f := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f with 
 | DetailsInfo_ι_price => r1 
 | DetailsInfo_ι_min_amount => r2 
 | DetailsInfo_ι_sell_amount => r3 
 | DetailsInfo_ι_buy_amount => r4 
 end .
(* 5 *) Coercion DetailsInfo_get : DetailsInfoFields >-> Funclass .
(* 6 *) Definition DetailsInfo_set (f: DetailsInfoFields ) 
(v: DetailsInfo_field_type f) (r: DetailsInfo ): DetailsInfo := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f, v with 
 | DetailsInfo_ι_price , v' => ( v' , r2 , r3 , r4 ) 
 | DetailsInfo_ι_min_amount , v' => ( r1 , v' , r3 , r4 ) 
 | DetailsInfo_ι_sell_amount , v' => ( r1 , r2 , v' , r4 ) 
 | DetailsInfo_ι_buy_amount , v' => ( r1 , r2 , r3 , v' ) 
 end .
(* 7 *) Global Instance DetailsInfo_PruvendoRecord : PruvendoRecord DetailsInfo DetailsInfoFields :=
{
  field_type := DetailsInfo_field_type; 
  getPruvendoRecord := @DetailsInfo_get ;
  setPruvendoRecord := @DetailsInfo_set ;
} .
(* 3 *) Definition Tip3Config_field_type f : Type :=  
match f with 
 | Tip3Config_ι_name => XString | Tip3Config_ι_symbol => XString | Tip3Config_ι_decimals => XInteger8 | Tip3Config_ι_root_public_key => XInteger256 | Tip3Config_ι_root_address => XAddress end .
(* 4 *) Definition Tip3Config_get (f: Tip3ConfigFields )(r: Tip3Config ) :  Tip3Config_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 ) := r in 
 match f with 
 | Tip3Config_ι_name => r1 
 | Tip3Config_ι_symbol => r2 
 | Tip3Config_ι_decimals => r3 
 | Tip3Config_ι_root_public_key => r4 
 | Tip3Config_ι_root_address => r5 
 end .
(* 5 *) Coercion Tip3Config_get : Tip3ConfigFields >-> Funclass .
(* 6 *) Definition Tip3Config_set (f: Tip3ConfigFields ) 
(v: Tip3Config_field_type f) (r: Tip3Config ): Tip3Config := 
 let '( r1 , r2 , r3 , r4 , r5 ) := r in 
 match f, v with 
 | Tip3Config_ι_name , v' => ( v' , r2 , r3 , r4 , r5 ) 
 | Tip3Config_ι_symbol , v' => ( r1 , v' , r3 , r4 , r5 ) 
 | Tip3Config_ι_decimals , v' => ( r1 , r2 , v' , r4 , r5 ) 
 | Tip3Config_ι_root_public_key , v' => ( r1 , r2 , r3 , v' , r5 ) 
 | Tip3Config_ι_root_address , v' => ( r1 , r2 , r3 , r4 , v' ) 
 end .
(* 7 *) Global Instance Tip3Config_PruvendoRecord : PruvendoRecord Tip3Config Tip3ConfigFields :=
{
  field_type := Tip3Config_field_type; 
  getPruvendoRecord := @Tip3Config_get ;
  setPruvendoRecord := @Tip3Config_set ;
} .
(* 3 *) Definition Price_field_type f : Type :=  
match f with 
 | Price_ι_price_ => XInteger128 | Price_ι_sells_amount_ => XInteger128 | Price_ι_buys_amount_ => XInteger128 | Price_ι_flex_ => addr_std_fixed | Price_ι_min_amount_ => XInteger128 | Price_ι_deals_limit_ => XInteger8 | Price_ι_notify_addr_ => XAddress | Price_ι_workchain_id_ => XInteger8 | Price_ι_tons_cfg_ => TonsConfig | Price_ι_tip3_code_ => XCell | Price_ι_tip3cfg_ => Tip3Config | Price_ι_sells_ => XList OrderInfo | Price_ι_buys_ => XList OrderInfo end .
(* 4 *) Definition Price_get (f: PriceFields )(r: Price ) :  Price_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) := r in 
 match f with 
 | Price_ι_price_ => r1 
 | Price_ι_sells_amount_ => r2 
 | Price_ι_buys_amount_ => r3 
 | Price_ι_flex_ => r4 
 | Price_ι_min_amount_ => r5 
 | Price_ι_deals_limit_ => r6 
 | Price_ι_notify_addr_ => r7 
 | Price_ι_workchain_id_ => r8 
 | Price_ι_tons_cfg_ => r9 
 | Price_ι_tip3_code_ => r10 
 | Price_ι_tip3cfg_ => r11 
 | Price_ι_sells_ => r12 
 | Price_ι_buys_ => r13 
 end .
(* 5 *) Coercion Price_get : PriceFields >-> Funclass .
(* 6 *) Definition Price_set (f: PriceFields ) 
(v: Price_field_type f) (r: Price ): Price := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) := r in 
 match f, v with 
 | Price_ι_price_ , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | Price_ι_sells_amount_ , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | Price_ι_buys_amount_ , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | Price_ι_flex_ , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | Price_ι_min_amount_ , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | Price_ι_deals_limit_ , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | Price_ι_notify_addr_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | Price_ι_workchain_id_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 , r11 , r12 , r13 ) 
 | Price_ι_tons_cfg_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 , r11 , r12 , r13 ) 
 | Price_ι_tip3_code_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' , r11 , r12 , r13 ) 
 | Price_ι_tip3cfg_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , v' , r12 , r13 ) 
 | Price_ι_sells_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , v' , r13 ) 
 | Price_ι_buys_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , v' ) 
 end .
(* 7 *) Global Instance Price_PruvendoRecord : PruvendoRecord Price PriceFields :=
{
  field_type := Price_field_type; 
  getPruvendoRecord := @Price_get ;
  setPruvendoRecord := @Price_set ;
} .
(* 3 *) Definition dealer_field_type f : Type :=  
match f with 
 | dealer_ι_tip3root_ => XAddress | dealer_ι_notify_addr_ => XAddress | dealer_ι_price_ => XInteger128 | dealer_ι_deals_limit_ => XInteger | dealer_ι_tons_cfg_ => TonsConfig | dealer_ι_sells_amount_ => XInteger128 | dealer_ι_sells_ => XList OrderInfo | dealer_ι_buys_amount_ => XInteger128 | dealer_ι_buys_ => XList OrderInfo | dealer_ι_ret_ => XMaybe OrderRet end .
(* 4 *) Definition dealer_get (f: dealerFields )(r: dealer ) :  dealer_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) := r in 
 match f with 
 | dealer_ι_tip3root_ => r1 
 | dealer_ι_notify_addr_ => r2 
 | dealer_ι_price_ => r3 
 | dealer_ι_deals_limit_ => r4 
 | dealer_ι_tons_cfg_ => r5 
 | dealer_ι_sells_amount_ => r6 
 | dealer_ι_sells_ => r7 
 | dealer_ι_buys_amount_ => r8 
 | dealer_ι_buys_ => r9 
 | dealer_ι_ret_ => r10 
 end .
(* 5 *) Coercion dealer_get : dealerFields >-> Funclass .
(* 6 *) Definition dealer_set (f: dealerFields ) 
(v: dealer_field_type f) (r: dealer ): dealer := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) := r in 
 match f, v with 
 | dealer_ι_tip3root_ , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | dealer_ι_notify_addr_ , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | dealer_ι_price_ , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | dealer_ι_deals_limit_ , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | dealer_ι_tons_cfg_ , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 ) 
 | dealer_ι_sells_amount_ , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 ) 
 | dealer_ι_sells_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 ) 
 | dealer_ι_buys_amount_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 ) 
 | dealer_ι_buys_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 ) 
 | dealer_ι_ret_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' ) 
 end .
(* 7 *) Global Instance dealer_PruvendoRecord : PruvendoRecord dealer dealerFields :=
{
  field_type := dealer_field_type; 
  getPruvendoRecord := @dealer_get ;
  setPruvendoRecord := @dealer_set ;
} .
(* 3 *) Definition process_ret_field_type f : Type :=  
match f with 
 | process_ret_ι_sells_amount => XInteger128 | process_ret_ι_sells_ => XList OrderInfo | process_ret_ι_buys_amount => XInteger128 | process_ret_ι_buys_ => XList OrderInfo | process_ret_ι_ret_ => XMaybe OrderRet end .
(* 4 *) Definition process_ret_get (f: process_retFields )(r: process_ret ) :  process_ret_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 ) := r in 
 match f with 
 | process_ret_ι_sells_amount => r1 
 | process_ret_ι_sells_ => r2 
 | process_ret_ι_buys_amount => r3 
 | process_ret_ι_buys_ => r4 
 | process_ret_ι_ret_ => r5 
 end .
(* 5 *) Coercion process_ret_get : process_retFields >-> Funclass .
(* 6 *) Definition process_ret_set (f: process_retFields ) 
(v: process_ret_field_type f) (r: process_ret ): process_ret := 
 let '( r1 , r2 , r3 , r4 , r5 ) := r in 
 match f, v with 
 | process_ret_ι_sells_amount , v' => ( v' , r2 , r3 , r4 , r5 ) 
 | process_ret_ι_sells_ , v' => ( r1 , v' , r3 , r4 , r5 ) 
 | process_ret_ι_buys_amount , v' => ( r1 , r2 , v' , r4 , r5 ) 
 | process_ret_ι_buys_ , v' => ( r1 , r2 , r3 , v' , r5 ) 
 | process_ret_ι_ret_ , v' => ( r1 , r2 , r3 , r4 , v' ) 
 end .
(* 7 *) Global Instance process_ret_PruvendoRecord : PruvendoRecord process_ret process_retFields :=
{
  field_type := process_ret_field_type; 
  getPruvendoRecord := @process_ret_get ;
  setPruvendoRecord := @process_ret_set ;
} .
(* 3 *) Definition lend_ownership_info_field_type f : Type :=  
match f with 
 | lend_ownership_info_ι_owner => XAddress | lend_ownership_info_ι_lend_balance => TokensType | lend_ownership_info_ι_lend_finish_time => XInteger32 end .
(* 4 *) Definition lend_ownership_info_get (f: lend_ownership_infoFields )(r: lend_ownership_info ) :  lend_ownership_info_field_type f := 
 let '( r1 , r2 , r3 ) := r in 
 match f with 
 | lend_ownership_info_ι_owner => r1 
 | lend_ownership_info_ι_lend_balance => r2 
 | lend_ownership_info_ι_lend_finish_time => r3 
 end .
(* 5 *) Coercion lend_ownership_info_get : lend_ownership_infoFields >-> Funclass .
(* 6 *) Definition lend_ownership_info_set (f: lend_ownership_infoFields ) 
(v: lend_ownership_info_field_type f) (r: lend_ownership_info ): lend_ownership_info := 
 let '( r1 , r2 , r3 ) := r in 
 match f, v with 
 | lend_ownership_info_ι_owner , v' => ( v' , r2 , r3 ) 
 | lend_ownership_info_ι_lend_balance , v' => ( r1 , v' , r3 ) 
 | lend_ownership_info_ι_lend_finish_time , v' => ( r1 , r2 , v' ) 
 end .
(* 7 *) Global Instance lend_ownership_info_PruvendoRecord : PruvendoRecord lend_ownership_info lend_ownership_infoFields :=
{
  field_type := lend_ownership_info_field_type; 
  getPruvendoRecord := @lend_ownership_info_get ;
  setPruvendoRecord := @lend_ownership_info_set ;
} .
(* 3 *) Definition allowance_info_field_type f : Type :=  
match f with 
 | allowance_info_ι_spender => XAddress | allowance_info_ι_remainingTokens => TokensType end .
(* 4 *) Definition allowance_info_get (f: allowance_infoFields )(r: allowance_info ) :  allowance_info_field_type f := 
 let '( r1 , r2 ) := r in 
 match f with 
 | allowance_info_ι_spender => r1 
 | allowance_info_ι_remainingTokens => r2 
 end .
(* 5 *) Coercion allowance_info_get : allowance_infoFields >-> Funclass .
(* 6 *) Definition allowance_info_set (f: allowance_infoFields ) 
(v: allowance_info_field_type f) (r: allowance_info ): allowance_info := 
 let '( r1 , r2 ) := r in 
 match f, v with 
 | allowance_info_ι_spender , v' => ( v' , r2 ) 
 | allowance_info_ι_remainingTokens , v' => ( r1 , v' ) 
 end .
(* 7 *) Global Instance allowance_info_PruvendoRecord : PruvendoRecord allowance_info allowance_infoFields :=
{
  field_type := allowance_info_field_type; 
  getPruvendoRecord := @allowance_info_get ;
  setPruvendoRecord := @allowance_info_set ;
} .
(* 3 *) Definition TONTokenWallet_field_type f : Type :=  
match f with 
 | TONTokenWallet_ι_name_ => XList XInteger8 | TONTokenWallet_ι_symbol_ => XList XInteger8 | TONTokenWallet_ι_decimals_ => XInteger8 | TONTokenWallet_ι_balance_ => TokensType | TONTokenWallet_ι_root_public_key_ => XInteger256 | TONTokenWallet_ι_wallet_public_key_ => XInteger256 | TONTokenWallet_ι_root_address_ => XAddress | TONTokenWallet_ι_owner_address_ => XMaybe XAddress | TONTokenWallet_ι_lend_ownership_ => XMaybe lend_ownership_info | TONTokenWallet_ι_code_ => XCell | TONTokenWallet_ι_allowance_ => XMaybe allowance_info | TONTokenWallet_ι_workchain_id_ => XInteger8 end .
(* 4 *) Definition TONTokenWallet_get (f: TONTokenWalletFields )(r: TONTokenWallet ) :  TONTokenWallet_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) := r in 
 match f with 
 | TONTokenWallet_ι_name_ => r1 
 | TONTokenWallet_ι_symbol_ => r2 
 | TONTokenWallet_ι_decimals_ => r3 
 | TONTokenWallet_ι_balance_ => r4 
 | TONTokenWallet_ι_root_public_key_ => r5 
 | TONTokenWallet_ι_wallet_public_key_ => r6 
 | TONTokenWallet_ι_root_address_ => r7 
 | TONTokenWallet_ι_owner_address_ => r8 
 | TONTokenWallet_ι_lend_ownership_ => r9 
 | TONTokenWallet_ι_code_ => r10 
 | TONTokenWallet_ι_allowance_ => r11 
 | TONTokenWallet_ι_workchain_id_ => r12 
 end .
(* 5 *) Coercion TONTokenWallet_get : TONTokenWalletFields >-> Funclass .
(* 6 *) Definition TONTokenWallet_set (f: TONTokenWalletFields ) 
(v: TONTokenWallet_field_type f) (r: TONTokenWallet ): TONTokenWallet := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) := r in 
 match f, v with 
 | TONTokenWallet_ι_name_ , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | TONTokenWallet_ι_symbol_ , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | TONTokenWallet_ι_decimals_ , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | TONTokenWallet_ι_balance_ , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | TONTokenWallet_ι_root_public_key_ , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | TONTokenWallet_ι_wallet_public_key_ , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | TONTokenWallet_ι_root_address_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 , r11 , r12 ) 
 | TONTokenWallet_ι_owner_address_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 , r11 , r12 ) 
 | TONTokenWallet_ι_lend_ownership_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 , r11 , r12 ) 
 | TONTokenWallet_ι_code_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' , r11 , r12 ) 
 | TONTokenWallet_ι_allowance_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , v' , r12 ) 
 | TONTokenWallet_ι_workchain_id_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , v' ) 
 end .
(* 7 *) Global Instance TONTokenWallet_PruvendoRecord : PruvendoRecord TONTokenWallet TONTokenWalletFields :=
{
  field_type := TONTokenWallet_field_type; 
  getPruvendoRecord := @TONTokenWallet_get ;
  setPruvendoRecord := @TONTokenWallet_set ;
} .
(* 3 *) Definition OrderInfoXchg_field_type f : Type :=  
match f with 
 | OrderInfoXchg_ι_original_amount => XInteger128 | OrderInfoXchg_ι_amount => XInteger128 | OrderInfoXchg_ι_account => XInteger128 | OrderInfoXchg_ι_tip3_wallet_provide => addr_std_fixed | OrderInfoXchg_ι_tip3_wallet_receive => addr_std_fixed | OrderInfoXchg_ι_client_addr => addr_std_fixed | OrderInfoXchg_ι_order_finish_time => XInteger32 end .
(* 4 *) Definition OrderInfoXchg_get (f: OrderInfoXchgFields )(r: OrderInfoXchg ) :  OrderInfoXchg_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 ) := r in 
 match f with 
 | OrderInfoXchg_ι_original_amount => r1 
 | OrderInfoXchg_ι_amount => r2 
 | OrderInfoXchg_ι_account => r3 
 | OrderInfoXchg_ι_tip3_wallet_provide => r4 
 | OrderInfoXchg_ι_tip3_wallet_receive => r5 
 | OrderInfoXchg_ι_client_addr => r6 
 | OrderInfoXchg_ι_order_finish_time => r7 
 end .
(* 5 *) Coercion OrderInfoXchg_get : OrderInfoXchgFields >-> Funclass .
(* 6 *) Definition OrderInfoXchg_set (f: OrderInfoXchgFields ) 
(v: OrderInfoXchg_field_type f) (r: OrderInfoXchg ): OrderInfoXchg := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 ) := r in 
 match f, v with 
 | OrderInfoXchg_ι_original_amount , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 ) 
 | OrderInfoXchg_ι_amount , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 ) 
 | OrderInfoXchg_ι_account , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 ) 
 | OrderInfoXchg_ι_tip3_wallet_provide , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 ) 
 | OrderInfoXchg_ι_tip3_wallet_receive , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 ) 
 | OrderInfoXchg_ι_client_addr , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 ) 
 | OrderInfoXchg_ι_order_finish_time , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' ) 
 end .
(* 7 *) Global Instance OrderInfoXchg_PruvendoRecord : PruvendoRecord OrderInfoXchg OrderInfoXchgFields :=
{
  field_type := OrderInfoXchg_field_type; 
  getPruvendoRecord := @OrderInfoXchg_get ;
  setPruvendoRecord := @OrderInfoXchg_set ;
} .
(* 3 *) Definition LocalState_field_type f : Type :=
match f with 
 | LocalState_ι_cell => XHMap (string*nat) XCell | LocalState_ι_StateInit => XHMap (string*nat) StateInit | LocalState_ι_tplStateInituint256 => XHMap (string*nat) ( StateInit * XInteger256 ) | LocalState_ι_bool => XHMap (string*nat) XBool | LocalState_ι_uint32 => XHMap (string*nat) XInteger32 | LocalState_ι_Price => XHMap (string*nat) Price | LocalState_ι_optuint128 => XHMap (string*nat) ( XMaybe XInteger128 ) | LocalState_ι_uint128 => XHMap (string*nat) XInteger128 | LocalState_ι_tplboolbool => XHMap (string*nat) ( XBool * XBool * XInteger128 ) | LocalState_ι_OrderInfo => XHMap (string*nat) OrderInfo | LocalState_ι_int => XHMap (string*nat) XInteger | LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfo => XHMap (string*nat) (XMaybe (XInteger * OrderInfo) * (XList OrderInfo) * XInteger128 ) | LocalState_ι_optpair_unsigned_OrderInfo__ => XHMap (string*nat) ( XMaybe (XInteger * OrderInfo) ) | LocalState_ι_queueOrderInfo => XHMap (string*nat) ( XList OrderInfo ) | LocalState_ι_OrderRet => XHMap (string*nat) OrderRet | LocalState_ι_unsigned => XHMap (string*nat) XInteger | LocalState_ι_dealer => XHMap (string*nat) dealer | LocalState_ι_process_ret => XHMap (string*nat) process_ret | LocalState_ι_uint8 => XHMap (string*nat) XInteger8 | LocalState_ι_TonsConfig => XHMap (string*nat) TonsConfig | LocalState_ι_tplqueue_OrderInfouint128 => XHMap (string*nat) ( (XList OrderInfo) * XInteger128 ) | LocalState_ι_addr_std_fixed => XHMap (string*nat) addr_std_fixed | LocalState_ι_Grams => XHMap (string*nat) Grams | LocalState_ι_SellArgs => XHMap (string*nat) SellArgs | LocalState_ι_address => XHMap (string*nat) XAddress | LocalState_ι_DetailsInfo => XHMap (string*nat) DetailsInfo | LocalState_ι_dict_arrayOrderInfo => XHMap (string*nat) ( XHMap XInteger OrderInfo ) | LocalState_ι_optaddress => XHMap (string*nat) ( XMaybe XAddress ) | LocalState_ι_TONTokenWallet => XHMap (string*nat) TONTokenWallet | LocalState_ι_tpladdressGrams => XHMap (string*nat) ( XAddress * Grams ) | LocalState_ι_XSlice => XHMap (string*nat) XSlice | LocalState_ι_optOrderRet => XHMap (string*nat) ( XMaybe OrderRet ) | LocalState_ι_cellIndex => XHMap string nat | LocalState_ι_StateInitIndex => XHMap string nat | LocalState_ι_tplStateInituint256Index => XHMap string nat | LocalState_ι_boolIndex => XHMap string nat | LocalState_ι_uint32Index => XHMap string nat | LocalState_ι_PriceIndex => XHMap string nat | LocalState_ι_optuint128Index => XHMap string nat | LocalState_ι_uint128Index => XHMap string nat | LocalState_ι_tplboolboolIndex => XHMap string nat | LocalState_ι_OrderInfoIndex => XHMap string nat | LocalState_ι_intIndex => XHMap string nat | LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex => XHMap string nat | LocalState_ι_optpair_unsigned_OrderInfo__Index => XHMap string nat | LocalState_ι_queueOrderInfoIndex => XHMap string nat | LocalState_ι_OrderRetIndex => XHMap string nat | LocalState_ι_unsignedIndex => XHMap string nat | LocalState_ι_dealerIndex => XHMap string nat | LocalState_ι_process_retIndex => XHMap string nat | LocalState_ι_uint8Index => XHMap string nat | LocalState_ι_TonsConfigIndex => XHMap string nat | LocalState_ι_tplqueue_OrderInfouint128Index => XHMap string nat | LocalState_ι_addr_std_fixedIndex => XHMap string nat | LocalState_ι_GramsIndex => XHMap string nat | LocalState_ι_SellArgsIndex => XHMap string nat | LocalState_ι_addressIndex => XHMap string nat | LocalState_ι_DetailsInfoIndex => XHMap string nat | LocalState_ι_dict_arrayOrderInfoIndex => XHMap string nat | LocalState_ι_optaddressIndex => XHMap string nat | LocalState_ι_TONTokenWalletIndex => XHMap string nat | LocalState_ι_tpladdressGramsIndex => XHMap string nat | LocalState_ι_XSliceIndex => XHMap string nat | LocalState_ι_optOrderRetIndex => XHMap string nat end .
(* 4 *) Definition LocalState_get (f: LocalStateFields )(r: LocalState ) :  LocalState_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) := r in 
 match f with 
 | LocalState_ι_cell => r1 
 | LocalState_ι_StateInit => r2 
 | LocalState_ι_tplStateInituint256 => r3 
 | LocalState_ι_bool => r4 
 | LocalState_ι_uint32 => r5 
 | LocalState_ι_Price => r6 
 | LocalState_ι_optuint128 => r7 
 | LocalState_ι_uint128 => r8 
 | LocalState_ι_tplboolbool => r9 
 | LocalState_ι_OrderInfo => r10 
 | LocalState_ι_int => r11 
 | LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfo => r12 
 | LocalState_ι_optpair_unsigned_OrderInfo__ => r13 
 | LocalState_ι_queueOrderInfo => r14 
 | LocalState_ι_OrderRet => r15 
 | LocalState_ι_unsigned => r16 
 | LocalState_ι_dealer => r17 
 | LocalState_ι_process_ret => r18 
 | LocalState_ι_uint8 => r19 
 | LocalState_ι_TonsConfig => r20 
 | LocalState_ι_tplqueue_OrderInfouint128 => r21 
 | LocalState_ι_addr_std_fixed => r22 
 | LocalState_ι_Grams => r23 
 | LocalState_ι_SellArgs => r24 
 | LocalState_ι_address => r25 
 | LocalState_ι_DetailsInfo => r26 
 | LocalState_ι_dict_arrayOrderInfo => r27 
 | LocalState_ι_optaddress => r28 
 | LocalState_ι_TONTokenWallet => r29 
 | LocalState_ι_tpladdressGrams => r30 
 | LocalState_ι_XSlice => r31 
 | LocalState_ι_optOrderRet => r32 
 | LocalState_ι_cellIndex => r33 
 | LocalState_ι_StateInitIndex => r34 
 | LocalState_ι_tplStateInituint256Index => r35 
 | LocalState_ι_boolIndex => r36 
 | LocalState_ι_uint32Index => r37 
 | LocalState_ι_PriceIndex => r38 
 | LocalState_ι_optuint128Index => r39 
 | LocalState_ι_uint128Index => r40 
 | LocalState_ι_tplboolboolIndex => r41 
 | LocalState_ι_OrderInfoIndex => r42 
 | LocalState_ι_intIndex => r43 
 | LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex => r44 
 | LocalState_ι_optpair_unsigned_OrderInfo__Index => r45 
 | LocalState_ι_queueOrderInfoIndex => r46 
 | LocalState_ι_OrderRetIndex => r47 
 | LocalState_ι_unsignedIndex => r48 
 | LocalState_ι_dealerIndex => r49 
 | LocalState_ι_process_retIndex => r50 
 | LocalState_ι_uint8Index => r51 
 | LocalState_ι_TonsConfigIndex => r52 
 | LocalState_ι_tplqueue_OrderInfouint128Index => r53 
 | LocalState_ι_addr_std_fixedIndex => r54 
 | LocalState_ι_GramsIndex => r55 
 | LocalState_ι_SellArgsIndex => r56 
 | LocalState_ι_addressIndex => r57 
 | LocalState_ι_DetailsInfoIndex => r58 
 | LocalState_ι_dict_arrayOrderInfoIndex => r59 
 | LocalState_ι_optaddressIndex => r60 
 | LocalState_ι_TONTokenWalletIndex => r61 
 | LocalState_ι_tpladdressGramsIndex => r62 
 | LocalState_ι_XSliceIndex => r63 
 | LocalState_ι_optOrderRetIndex => r64 
 end .
(* 5 *) Coercion LocalState_get : LocalStateFields >-> Funclass .
(* 6 *) Definition LocalState_set (f: LocalStateFields ) 
(v: LocalState_field_type f) (r: LocalState ): LocalState := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) := r in 
 match f, v with 
 | LocalState_ι_cell , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_StateInit , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_tplStateInituint256 , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_bool , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_uint32 , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_Price , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_optuint128 , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_uint128 , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_tplboolbool , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_OrderInfo , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_int , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , v' , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfo , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , v' , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_optpair_unsigned_OrderInfo__ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , v' , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_queueOrderInfo , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , v' , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_OrderRet , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , v' , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_unsigned , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , v' , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_dealer , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , v' , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_process_ret , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , v' , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_uint8 , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , v' , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_TonsConfig , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , v' , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_tplqueue_OrderInfouint128 , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , v' , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_addr_std_fixed , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , v' , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_Grams , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , v' , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_SellArgs , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , v' , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_address , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , v' , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_DetailsInfo , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , v' , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_dict_arrayOrderInfo , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , v' , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_optaddress , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , v' , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_TONTokenWallet , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , v' , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_tpladdressGrams , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , v' , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_XSlice , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , v' , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_optOrderRet , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , v' , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_cellIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , v' , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_StateInitIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , v' , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_tplStateInituint256Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , v' , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_boolIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , v' , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_uint32Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , v' , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_PriceIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , v' , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_optuint128Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , v' , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_uint128Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , v' , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_tplboolboolIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , v' , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_OrderInfoIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , v' , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_intIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , v' , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , v' , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_optpair_unsigned_OrderInfo__Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , v' , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_queueOrderInfoIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , v' , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_OrderRetIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , v' , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_unsignedIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , v' , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_dealerIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , v' , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_process_retIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , v' , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_uint8Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , v' , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_TonsConfigIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , v' , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_tplqueue_OrderInfouint128Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , v' , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_addr_std_fixedIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , v' , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_GramsIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , v' , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_SellArgsIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , v' , r57 , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_addressIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , v' , r58 , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_DetailsInfoIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , v' , r59 , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_dict_arrayOrderInfoIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , v' , r60 , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_optaddressIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , v' , r61 , r62 , r63 , r64 ) 
 | LocalState_ι_TONTokenWalletIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , v' , r62 , r63 , r64 ) 
 | LocalState_ι_tpladdressGramsIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , v' , r63 , r64 ) 
 | LocalState_ι_XSliceIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , v' , r64 ) 
 | LocalState_ι_optOrderRetIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 , r41 , r42 , r43 , r44 , r45 , r46 , r47 , r48 , r49 , r50 , r51 , r52 , r53 , r54 , r55 , r56 , r57 , r58 , r59 , r60 , r61 , r62 , r63 , v' ) 
 end .
(* 7 *) Global Instance LocalState_PruvendoRecord : PruvendoRecord LocalState LocalStateFields :=
{
  field_type := LocalState_field_type; 
  getPruvendoRecord := @LocalState_get ;
  setPruvendoRecord := @LocalState_set ;
} .
(* 3 *) Definition Ledger_field_type f : Type :=  
match f with 
 | Ledger_ι_Price => Price 
| Ledger_ι_VMState => VMStateLRecord 
| Ledger_ι_LocalState => LocalState 
| Ledger_ι_LocalStateCopy => LocalState 
end .

(* 4 *) Definition Ledger_get (f: LedgerFieldsI )(r: Ledger ) :  Ledger_field_type f := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f with 
 | Ledger_ι_Price => r1 
 | Ledger_ι_VMState => r2 
 | Ledger_ι_LocalState => r3 
 | Ledger_ι_LocalStateCopy => r4 
 end .
(* 5 *) Coercion Ledger_get : LedgerFieldsI >-> Funclass .
(* 6 *) Definition Ledger_set (f: LedgerFields ) 
(v: Ledger_field_type f) (r: Ledger ): Ledger := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f, v with 
 | Ledger_ι_Price , v' => ( v' , r2 , r3 , r4 ) 
 | Ledger_ι_VMState , v' => ( r1 , v' , r3 , r4 ) 
 | Ledger_ι_LocalState , v' => ( r1 , r2 , v' , r4 ) 
 | Ledger_ι_LocalStateCopy , v' => ( r1 , r2 , r3 , v' ) 
 end .
(* 7 *) Global Instance Ledger_PruvendoRecord : PruvendoRecord Ledger LedgerFields :=
{
  field_type := Ledger_field_type; 
  getPruvendoRecord := @Ledger_get ;
  setPruvendoRecord := @Ledger_set ;
} .
Definition T1 := Price .
Definition T2 := VMStateLRecord .
Definition T3 := LocalState .
Definition T4 := LocalState .

 
 Definition projEmbed_T1 : Ledger -> T1 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_Price. 
 Definition injEmbed_T1 : T1 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_Price. 
 
 Lemma projinj_T1 : forall ( t : T1 ) ( s : Ledger ), projEmbed_T1 ( injEmbed_T1 t s ) = t . 
 Proof. 
 intros. destruct s. destruct p. destruct p. compute. auto. 
 Qed. 
 
 Lemma injproj_T1 : forall ( s : Ledger ) , injEmbed_T1 ( projEmbed_T1 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T1 : forall ( t1 t2 : T1 ) ( s : Ledger ) , 
 injEmbed_T1 t1 ( injEmbed_T1 t2 s) = 
 injEmbed_T1 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT1 : EmbeddedType Ledger T1 := 
 { 
 projEmbed := projEmbed_T1 ; 
 injEmbed := injEmbed_T1 ; 
 projinj := projinj_T1 ; 
 injproj := injproj_T1 ; 
 injinj := injinj_T1 ; 
 } . 
 


 
 Definition projEmbed_T2 : Ledger -> T2 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_VMState. 
 Definition injEmbed_T2 : T2 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_VMState. 
 
 Lemma projinj_T2 : forall ( t : T2 ) ( s : Ledger ), projEmbed_T2 ( injEmbed_T2 t s ) = t . 
 Proof. 
 intros. destruct s. destruct p. destruct p. compute. auto. 
 Qed. 
 
 Lemma injproj_T2 : forall ( s : Ledger ) , injEmbed_T2 ( projEmbed_T2 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T2 : forall ( t1 t2 : T2 ) ( s : Ledger ) , 
 injEmbed_T2 t1 ( injEmbed_T2 t2 s) = 
 injEmbed_T2 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT2 : EmbeddedType Ledger T2 := 
 { 
 projEmbed := projEmbed_T2 ; 
 injEmbed := injEmbed_T2 ; 
 projinj := projinj_T2 ; 
 injproj := injproj_T2 ; 
 injinj := injinj_T2 ; 
 } . 
 


 
 Definition projEmbed_T3 : Ledger -> T3 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalState. 
 Definition injEmbed_T3 : T3 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalState. 
 
 Lemma projinj_T3 : forall ( t : T3 ) ( s : Ledger ), projEmbed_T3 ( injEmbed_T3 t s ) = t . 
 Proof. 
 intros. destruct s. destruct p. destruct p. compute. auto. 
 Qed. 
 
 Lemma injproj_T3 : forall ( s : Ledger ) , injEmbed_T3 ( projEmbed_T3 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T3 : forall ( t1 t2 : T3 ) ( s : Ledger ) , 
 injEmbed_T3 t1 ( injEmbed_T3 t2 s) = 
 injEmbed_T3 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT3 : EmbeddedType Ledger T3 := 
 { 
 projEmbed := projEmbed_T3 ; 
 injEmbed := injEmbed_T3 ; 
 projinj := projinj_T3 ; 
 injproj := injproj_T3 ; 
 injinj := injinj_T3 ; 
 } . 
 


 
 Definition projEmbed_T4 : Ledger -> T4 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalStateCopy. 
 Definition injEmbed_T4 : T4 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalStateCopy. 
 
 Lemma projinj_T4 : forall ( t : T4 ) ( s : Ledger ), projEmbed_T4 ( injEmbed_T4 t s ) = t . 
 Proof. 
 intros. destruct s. destruct p. destruct p. compute. auto. 
 Qed. 
 
 Lemma injproj_T4 : forall ( s : Ledger ) , injEmbed_T4 ( projEmbed_T4 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T4 : forall ( t1 t2 : T4 ) ( s : Ledger ) , 
 injEmbed_T4 t1 ( injEmbed_T4 t2 s) = 
 injEmbed_T4 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT4 : EmbeddedType Ledger T4 := 
 { 
 projEmbed := projEmbed_T4 ; 
 injEmbed := injEmbed_T4 ; 
 projinj := projinj_T4 ; 
 injproj := injproj_T4 ; 
 injinj := injinj_T4 ; 
 } . 
 



Lemma injcommute_T1_T2: 
               forall ( u : T2 ) ( t : T1 ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT2) u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT2) u s ) ).
Proof.
 intros. destruct s. destruct p. destruct p. compute.   auto.
Qed.

Instance InjectCommutableStates_T1_T2 : 
@InjectCommutableStates Ledger ( T1 ) T2 := 
{
(*   embeddedTypeT := embeddedT1; *)
  embeddedTypeU := embeddedT2 ;

  injcommute := injcommute_T1_T2 
}.

Definition embeddedProduct_T1_T2 := 
           @embeddedProduct Ledger ( T1 ) T2
           InjectCommutableStates_T1_T2.

Existing Instance embeddedProduct_T1_T2.


Lemma injcommute_T1xT2_T3 : 
               forall ( u : T3 ) ( t :  (T1 * T2)%xprod ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT3) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT3) u s ) ).
Proof.
 intros. destruct s. destruct p. destruct p. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2_T3 : 
@InjectCommutableStates Ledger (T1 * T2)%xprod T3 := 
{
  embeddedTypeU := embeddedT3 ;

  injcommute := injcommute_T1xT2_T3 
}.

Definition embeddedProduct_T1xT2_T3 := 
           @embeddedProduct Ledger (T1 * T2)%xprod T3
  
           InjectCommutableStates_T1xT2_T3.

Existing Instance embeddedProduct_T1xT2_T3 . 


Lemma injcommute_T1xT2xT3_T4 : 
               forall ( u : T4 ) ( t :  ((T1 * T2)%xprod* T3)%xprod ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT4) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT4) u s ) ).
Proof.
 intros. destruct s. destruct p. destruct p. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3_T4 : 
@InjectCommutableStates Ledger ((T1 * T2)%xprod* T3)%xprod T4 := 
{
  embeddedTypeU := embeddedT4 ;

  injcommute := injcommute_T1xT2xT3_T4 
}.

Definition embeddedProduct_T1xT2xT3_T4 := 
           @embeddedProduct Ledger ((T1 * T2)%xprod* T3)%xprod T4
  
           InjectCommutableStates_T1xT2xT3_T4.

Existing Instance embeddedProduct_T1xT2xT3_T4 . 


 
 Lemma fullState_T1xT2xT3_T4 : forall s s0, 
 injEmbed ( T := (((T1 * T2)%xprod * T3)%xprod * T4)%xprod ) 
 ( projEmbed s ) ( injEmbed ( T := T4 ) ( projEmbed s ) s0 ) = s. 
 Proof. 
 intros. destruct s. destruct p. destruct p. destruct s0. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Check FullState. 
 
 (* Instance FullState_T1xT2xT3_T4 : 
 FullState Ledger ((T1 * T2)%xprod * T3)%xprod T4 := 
 { 
 injComm := InjectCommutableStates_T1xT2xT3_T4 ; 
 fullState := fullState_T1xT2xT3_T4 
 } .  *)
 

Local Open Scope solidity_scope.
Notation "'↑ε4' m ":= (liftEmbeddedState ( H := embeddedT4 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε3' m ":= (liftEmbeddedState ( H := embeddedT3 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε2' m ":= (liftEmbeddedState ( H := embeddedT2 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε1' m ":= (liftEmbeddedState ( H := embeddedT1 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.

Notation "'↑4' m ":= (liftEmbeddedState ( H := embeddedT4 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑3' m ":= (liftEmbeddedState ( H := embeddedT3 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑2' m ":= (liftEmbeddedState ( H := embeddedT2 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑1' m ":= (liftEmbeddedState ( H := embeddedT1 ) ( m ) ) (at level 10, left associativity): solidity_scope.

Notation "'↑↑4' m ":= (liftEmbeddedState ( H := embeddedT4 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑3' m ":= (liftEmbeddedState ( H := embeddedT3 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑2' m ":= (liftEmbeddedState ( H := embeddedT2 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑1' m ":= (liftEmbeddedState ( H := embeddedT1 ) ) (at level 10, left associativity): solidity_scope.

Notation "'↑0' m " := ( liftEmbeddedState ( H :=  embeddedProduct_T1xT2xT3_T4 ) ( m )) (at level 10, left associativity): solidity_scope.
Notation "'↑↑0'" := ( liftEmbeddedState ( H :=  embeddedProduct_T1xT2xT3_T4 )) (at level 32, left associativity): solidity_scope.
(* Notation " ↓ m " := ( callEmbeddedStateAdj m default (H0 :=  FullState_T1xT2xT3_T4 ) ) (at level 31, left associativity): solidity_scope. *)
Global Instance iso_T1 : IsoTypes T1 (field_type (R:=Ledger) Ledger_ι_Price) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T2 : IsoTypes T2 (field_type (R:=Ledger) Ledger_ι_VMState) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T3 : IsoTypes T3 (field_type (R:=Ledger) Ledger_ι_LocalState) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T4 : IsoTypes T4 (field_type (R:=Ledger) Ledger_ι_LocalStateCopy) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.


 (* TODO: Тут надо вручную вставлять поля леджера зависящие от полей *) 

Class Countable (X: Type) :=
{
   rength : nat;
   rth : nat -> X -> {t: Type & t}
}.

Program Instance CountablePair0 : forall X Y, Countable (X*Y).
Next Obligation.
exact 2%nat.
Defined.
Next Obligation.
destruct H.
refine (existT id X x).
refine (existT id Y y).
Defined.
Fail Next Obligation.

Program Instance CountablePair_Next : forall X`{Countable X} Y, Countable (X*Y) .
Next Obligation.
exact (S rength).
Defined.
Next Obligation.
remember (Nat.ltb H0 rength).
destruct b.
refine (rth  H0 x).
refine (existT id Y y).
Defined.
Fail Next Obligation.

Existing Instance CountablePair_Next | 0.
Existing Instance CountablePair0 | 100.

Opaque Price.

Lemma Ledger1Type_eq: forall (l: Ledger), projT1 (rth 0 l) = Price.
Proof.
   intros.
   compute.
   destruct l.
   repeat destruct p.
   reflexivity.  
Defined.

Definition Ledger1Type (l: Ledger) := projT1 (rth 0 l).

Definition Ledger1TypePrice : forall (l:Ledger), Ledger1Type l -> Price.
intros.
unfold Ledger1Type in X.
rewrite Ledger1Type_eq in X.
exact X.
Defined.

Coercion Ledger1TypePrice       : Ledger1Type >-> Price.

Notation "r ₁" := ((projT2 (rth 0 r) : Ledger1Type r) : Price) (at level 10).

Transparent Price.

Definition LedgerPruvendoRecord := Ledger_PruvendoRecord.
Definition LedgerLocalState := LocalState.
Definition LedgerLocalFields := LocalStateFields.
Definition LedgerLocalPruvendoRecord := LocalState_PruvendoRecord.
Definition LocalEmbedded := embeddedT4.
Definition LocalCopyEmbedded := embeddedT3.
Definition LocalDefault : XDefault LocalState := prod_default.
Definition Ledger_LocalState := Ledger_ι_LocalState.
Definition Ledger_LocalStateCopy := Ledger_ι_LocalStateCopy.
Definition iso_local := iso_T4.


Lemma LedgerFieldsDec: forall (m1 m2: LedgerFields), {m1=m2}+{m1<>m2}.
Proof.
  intros.
  decide equality.
Defined.

Lemma LocalCopySameType: field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_LocalState = 
field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_LocalStateCopy.
Proof.
  reflexivity.
Defined.

Class LocalStateField (X:Type): Type := 
{
    local_index_embedded:> EmbeddedType LedgerLocalState (XHMap string nat) ;
    local_state_field: LedgerLocalFields;
    local_field_type_correct: field_type (PruvendoRecord:=LedgerLocalPruvendoRecord) local_state_field = XHMap (string*nat)%type X;
}.


(****************************************************************************)
Definition  LocalState_ι_cellIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_cellIndex l.

Definition  LocalState_ι_cellIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_cellIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_cellIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_cellIndex_Embedded_projEmbed (LocalState_ι_cellIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_cellIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_cellIndex_Embedded_injEmbed (LocalState_ι_cellIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_cellIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_cellIndex_Embedded_injEmbed t1 (LocalState_ι_cellIndex_Embedded_injEmbed t2 s) = LocalState_ι_cellIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_cellIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_cellIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_cellIndex_Embedded_injEmbed;
  projinj := LocalState_ι_cellIndex_Embedded_projinj;
  injproj := LocalState_ι_cellIndex_Embedded_injproj;
  injinj := LocalState_ι_cellIndex_Embedded_injinj
}.
Definition  LocalState_ι_StateInitIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_StateInitIndex l.

Definition  LocalState_ι_StateInitIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_StateInitIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_StateInitIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_StateInitIndex_Embedded_projEmbed (LocalState_ι_StateInitIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_StateInitIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_StateInitIndex_Embedded_injEmbed (LocalState_ι_StateInitIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_StateInitIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_StateInitIndex_Embedded_injEmbed t1 (LocalState_ι_StateInitIndex_Embedded_injEmbed t2 s) = LocalState_ι_StateInitIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_StateInitIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_StateInitIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_StateInitIndex_Embedded_injEmbed;
  projinj := LocalState_ι_StateInitIndex_Embedded_projinj;
  injproj := LocalState_ι_StateInitIndex_Embedded_injproj;
  injinj := LocalState_ι_StateInitIndex_Embedded_injinj
}.
Definition  LocalState_ι_tplStateInituint256Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_tplStateInituint256Index l.

Definition  LocalState_ι_tplStateInituint256Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_tplStateInituint256Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_tplStateInituint256Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_tplStateInituint256Index_Embedded_projEmbed (LocalState_ι_tplStateInituint256Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_tplStateInituint256Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_tplStateInituint256Index_Embedded_injEmbed (LocalState_ι_tplStateInituint256Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_tplStateInituint256Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_tplStateInituint256Index_Embedded_injEmbed t1 (LocalState_ι_tplStateInituint256Index_Embedded_injEmbed t2 s) = LocalState_ι_tplStateInituint256Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_tplStateInituint256Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_tplStateInituint256Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_tplStateInituint256Index_Embedded_injEmbed;
  projinj := LocalState_ι_tplStateInituint256Index_Embedded_projinj;
  injproj := LocalState_ι_tplStateInituint256Index_Embedded_injproj;
  injinj := LocalState_ι_tplStateInituint256Index_Embedded_injinj
}.
Definition  LocalState_ι_boolIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_boolIndex l.

Definition  LocalState_ι_boolIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_boolIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_boolIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_boolIndex_Embedded_projEmbed (LocalState_ι_boolIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_boolIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_boolIndex_Embedded_injEmbed (LocalState_ι_boolIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_boolIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_boolIndex_Embedded_injEmbed t1 (LocalState_ι_boolIndex_Embedded_injEmbed t2 s) = LocalState_ι_boolIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_boolIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_boolIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_boolIndex_Embedded_injEmbed;
  projinj := LocalState_ι_boolIndex_Embedded_projinj;
  injproj := LocalState_ι_boolIndex_Embedded_injproj;
  injinj := LocalState_ι_boolIndex_Embedded_injinj
}.
Definition  LocalState_ι_uint32Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_uint32Index l.

Definition  LocalState_ι_uint32Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_uint32Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_uint32Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_uint32Index_Embedded_projEmbed (LocalState_ι_uint32Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_uint32Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_uint32Index_Embedded_injEmbed (LocalState_ι_uint32Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_uint32Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_uint32Index_Embedded_injEmbed t1 (LocalState_ι_uint32Index_Embedded_injEmbed t2 s) = LocalState_ι_uint32Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_uint32Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_uint32Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_uint32Index_Embedded_injEmbed;
  projinj := LocalState_ι_uint32Index_Embedded_projinj;
  injproj := LocalState_ι_uint32Index_Embedded_injproj;
  injinj := LocalState_ι_uint32Index_Embedded_injinj
}.
Definition  LocalState_ι_PriceIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_PriceIndex l.

Definition  LocalState_ι_PriceIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_PriceIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_PriceIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_PriceIndex_Embedded_projEmbed (LocalState_ι_PriceIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_PriceIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_PriceIndex_Embedded_injEmbed (LocalState_ι_PriceIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_PriceIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_PriceIndex_Embedded_injEmbed t1 (LocalState_ι_PriceIndex_Embedded_injEmbed t2 s) = LocalState_ι_PriceIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_PriceIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_PriceIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_PriceIndex_Embedded_injEmbed;
  projinj := LocalState_ι_PriceIndex_Embedded_projinj;
  injproj := LocalState_ι_PriceIndex_Embedded_injproj;
  injinj := LocalState_ι_PriceIndex_Embedded_injinj
}.
Definition  LocalState_ι_optuint128Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_optuint128Index l.

Definition  LocalState_ι_optuint128Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_optuint128Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_optuint128Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_optuint128Index_Embedded_projEmbed (LocalState_ι_optuint128Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_optuint128Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_optuint128Index_Embedded_injEmbed (LocalState_ι_optuint128Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_optuint128Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_optuint128Index_Embedded_injEmbed t1 (LocalState_ι_optuint128Index_Embedded_injEmbed t2 s) = LocalState_ι_optuint128Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_optuint128Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_optuint128Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_optuint128Index_Embedded_injEmbed;
  projinj := LocalState_ι_optuint128Index_Embedded_projinj;
  injproj := LocalState_ι_optuint128Index_Embedded_injproj;
  injinj := LocalState_ι_optuint128Index_Embedded_injinj
}.
Definition  LocalState_ι_uint128Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_uint128Index l.

Definition  LocalState_ι_uint128Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_uint128Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_uint128Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_uint128Index_Embedded_projEmbed (LocalState_ι_uint128Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_uint128Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_uint128Index_Embedded_injEmbed (LocalState_ι_uint128Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_uint128Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_uint128Index_Embedded_injEmbed t1 (LocalState_ι_uint128Index_Embedded_injEmbed t2 s) = LocalState_ι_uint128Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_uint128Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_uint128Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_uint128Index_Embedded_injEmbed;
  projinj := LocalState_ι_uint128Index_Embedded_projinj;
  injproj := LocalState_ι_uint128Index_Embedded_injproj;
  injinj := LocalState_ι_uint128Index_Embedded_injinj
}.
Definition  LocalState_ι_tplboolboolIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_tplboolboolIndex l.

Definition  LocalState_ι_tplboolboolIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_tplboolboolIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_tplboolboolIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_tplboolboolIndex_Embedded_projEmbed (LocalState_ι_tplboolboolIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_tplboolboolIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_tplboolboolIndex_Embedded_injEmbed (LocalState_ι_tplboolboolIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_tplboolboolIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_tplboolboolIndex_Embedded_injEmbed t1 (LocalState_ι_tplboolboolIndex_Embedded_injEmbed t2 s) = LocalState_ι_tplboolboolIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_tplboolboolIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_tplboolboolIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_tplboolboolIndex_Embedded_injEmbed;
  projinj := LocalState_ι_tplboolboolIndex_Embedded_projinj;
  injproj := LocalState_ι_tplboolboolIndex_Embedded_injproj;
  injinj := LocalState_ι_tplboolboolIndex_Embedded_injinj
}.
Definition  LocalState_ι_OrderInfoIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_OrderInfoIndex l.

Definition  LocalState_ι_OrderInfoIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_OrderInfoIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_OrderInfoIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_OrderInfoIndex_Embedded_projEmbed (LocalState_ι_OrderInfoIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_OrderInfoIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_OrderInfoIndex_Embedded_injEmbed (LocalState_ι_OrderInfoIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_OrderInfoIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_OrderInfoIndex_Embedded_injEmbed t1 (LocalState_ι_OrderInfoIndex_Embedded_injEmbed t2 s) = LocalState_ι_OrderInfoIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_OrderInfoIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_OrderInfoIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_OrderInfoIndex_Embedded_injEmbed;
  projinj := LocalState_ι_OrderInfoIndex_Embedded_projinj;
  injproj := LocalState_ι_OrderInfoIndex_Embedded_injproj;
  injinj := LocalState_ι_OrderInfoIndex_Embedded_injinj
}.
Definition  LocalState_ι_intIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_intIndex l.

Definition  LocalState_ι_intIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_intIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_intIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_intIndex_Embedded_projEmbed (LocalState_ι_intIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_intIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_intIndex_Embedded_injEmbed (LocalState_ι_intIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_intIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_intIndex_Embedded_injEmbed t1 (LocalState_ι_intIndex_Embedded_injEmbed t2 s) = LocalState_ι_intIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_intIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_intIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_intIndex_Embedded_injEmbed;
  projinj := LocalState_ι_intIndex_Embedded_projinj;
  injproj := LocalState_ι_intIndex_Embedded_injproj;
  injinj := LocalState_ι_intIndex_Embedded_injinj
}.
Definition  LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex l.

Definition  LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_projEmbed (LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injEmbed (LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injEmbed t1 (LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injEmbed t2 s) = LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injEmbed;
  projinj := LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_projinj;
  injproj := LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injproj;
  injinj := LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded_injinj
}.
Definition  LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_optpair_unsigned_OrderInfo__Index l.

Definition  LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_optpair_unsigned_OrderInfo__Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_projEmbed (LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injEmbed (LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injEmbed t1 (LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injEmbed t2 s) = LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injEmbed;
  projinj := LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_projinj;
  injproj := LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injproj;
  injinj := LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded_injinj
}.
Definition  LocalState_ι_queueOrderInfoIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_queueOrderInfoIndex l.

Definition  LocalState_ι_queueOrderInfoIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_queueOrderInfoIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_queueOrderInfoIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_queueOrderInfoIndex_Embedded_projEmbed (LocalState_ι_queueOrderInfoIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_queueOrderInfoIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_queueOrderInfoIndex_Embedded_injEmbed (LocalState_ι_queueOrderInfoIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_queueOrderInfoIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_queueOrderInfoIndex_Embedded_injEmbed t1 (LocalState_ι_queueOrderInfoIndex_Embedded_injEmbed t2 s) = LocalState_ι_queueOrderInfoIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_queueOrderInfoIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_queueOrderInfoIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_queueOrderInfoIndex_Embedded_injEmbed;
  projinj := LocalState_ι_queueOrderInfoIndex_Embedded_projinj;
  injproj := LocalState_ι_queueOrderInfoIndex_Embedded_injproj;
  injinj := LocalState_ι_queueOrderInfoIndex_Embedded_injinj
}.
Definition  LocalState_ι_OrderRetIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_OrderRetIndex l.

Definition  LocalState_ι_OrderRetIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_OrderRetIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_OrderRetIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_OrderRetIndex_Embedded_projEmbed (LocalState_ι_OrderRetIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_OrderRetIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_OrderRetIndex_Embedded_injEmbed (LocalState_ι_OrderRetIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_OrderRetIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_OrderRetIndex_Embedded_injEmbed t1 (LocalState_ι_OrderRetIndex_Embedded_injEmbed t2 s) = LocalState_ι_OrderRetIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_OrderRetIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_OrderRetIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_OrderRetIndex_Embedded_injEmbed;
  projinj := LocalState_ι_OrderRetIndex_Embedded_projinj;
  injproj := LocalState_ι_OrderRetIndex_Embedded_injproj;
  injinj := LocalState_ι_OrderRetIndex_Embedded_injinj
}.
Definition  LocalState_ι_unsignedIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_unsignedIndex l.

Definition  LocalState_ι_unsignedIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_unsignedIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_unsignedIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_unsignedIndex_Embedded_projEmbed (LocalState_ι_unsignedIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_unsignedIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_unsignedIndex_Embedded_injEmbed (LocalState_ι_unsignedIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_unsignedIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_unsignedIndex_Embedded_injEmbed t1 (LocalState_ι_unsignedIndex_Embedded_injEmbed t2 s) = LocalState_ι_unsignedIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_unsignedIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_unsignedIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_unsignedIndex_Embedded_injEmbed;
  projinj := LocalState_ι_unsignedIndex_Embedded_projinj;
  injproj := LocalState_ι_unsignedIndex_Embedded_injproj;
  injinj := LocalState_ι_unsignedIndex_Embedded_injinj
}.
Definition  LocalState_ι_dealerIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_dealerIndex l.

Definition  LocalState_ι_dealerIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_dealerIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_dealerIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_dealerIndex_Embedded_projEmbed (LocalState_ι_dealerIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_dealerIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_dealerIndex_Embedded_injEmbed (LocalState_ι_dealerIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_dealerIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_dealerIndex_Embedded_injEmbed t1 (LocalState_ι_dealerIndex_Embedded_injEmbed t2 s) = LocalState_ι_dealerIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_dealerIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_dealerIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_dealerIndex_Embedded_injEmbed;
  projinj := LocalState_ι_dealerIndex_Embedded_projinj;
  injproj := LocalState_ι_dealerIndex_Embedded_injproj;
  injinj := LocalState_ι_dealerIndex_Embedded_injinj
}.
Definition  LocalState_ι_process_retIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_process_retIndex l.

Definition  LocalState_ι_process_retIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_process_retIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_process_retIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_process_retIndex_Embedded_projEmbed (LocalState_ι_process_retIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_process_retIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_process_retIndex_Embedded_injEmbed (LocalState_ι_process_retIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_process_retIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_process_retIndex_Embedded_injEmbed t1 (LocalState_ι_process_retIndex_Embedded_injEmbed t2 s) = LocalState_ι_process_retIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_process_retIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_process_retIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_process_retIndex_Embedded_injEmbed;
  projinj := LocalState_ι_process_retIndex_Embedded_projinj;
  injproj := LocalState_ι_process_retIndex_Embedded_injproj;
  injinj := LocalState_ι_process_retIndex_Embedded_injinj
}.
Definition  LocalState_ι_uint8Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_uint8Index l.

Definition  LocalState_ι_uint8Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_uint8Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_uint8Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_uint8Index_Embedded_projEmbed (LocalState_ι_uint8Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_uint8Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_uint8Index_Embedded_injEmbed (LocalState_ι_uint8Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_uint8Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_uint8Index_Embedded_injEmbed t1 (LocalState_ι_uint8Index_Embedded_injEmbed t2 s) = LocalState_ι_uint8Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_uint8Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_uint8Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_uint8Index_Embedded_injEmbed;
  projinj := LocalState_ι_uint8Index_Embedded_projinj;
  injproj := LocalState_ι_uint8Index_Embedded_injproj;
  injinj := LocalState_ι_uint8Index_Embedded_injinj
}.
Definition  LocalState_ι_TonsConfigIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_TonsConfigIndex l.

Definition  LocalState_ι_TonsConfigIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_TonsConfigIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_TonsConfigIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_TonsConfigIndex_Embedded_projEmbed (LocalState_ι_TonsConfigIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_TonsConfigIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_TonsConfigIndex_Embedded_injEmbed (LocalState_ι_TonsConfigIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_TonsConfigIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_TonsConfigIndex_Embedded_injEmbed t1 (LocalState_ι_TonsConfigIndex_Embedded_injEmbed t2 s) = LocalState_ι_TonsConfigIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_TonsConfigIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_TonsConfigIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_TonsConfigIndex_Embedded_injEmbed;
  projinj := LocalState_ι_TonsConfigIndex_Embedded_projinj;
  injproj := LocalState_ι_TonsConfigIndex_Embedded_injproj;
  injinj := LocalState_ι_TonsConfigIndex_Embedded_injinj
}.
Definition  LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_tplqueue_OrderInfouint128Index l.

Definition  LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_tplqueue_OrderInfouint128Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_projEmbed (LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injEmbed (LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injEmbed t1 (LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injEmbed t2 s) = LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_tplqueue_OrderInfouint128Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injEmbed;
  projinj := LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_projinj;
  injproj := LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injproj;
  injinj := LocalState_ι_tplqueue_OrderInfouint128Index_Embedded_injinj
}.
Definition  LocalState_ι_addr_std_fixedIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_addr_std_fixedIndex l.

Definition  LocalState_ι_addr_std_fixedIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_addr_std_fixedIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_addr_std_fixedIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_addr_std_fixedIndex_Embedded_projEmbed (LocalState_ι_addr_std_fixedIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_addr_std_fixedIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_addr_std_fixedIndex_Embedded_injEmbed (LocalState_ι_addr_std_fixedIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_addr_std_fixedIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_addr_std_fixedIndex_Embedded_injEmbed t1 (LocalState_ι_addr_std_fixedIndex_Embedded_injEmbed t2 s) = LocalState_ι_addr_std_fixedIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_addr_std_fixedIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_addr_std_fixedIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_addr_std_fixedIndex_Embedded_injEmbed;
  projinj := LocalState_ι_addr_std_fixedIndex_Embedded_projinj;
  injproj := LocalState_ι_addr_std_fixedIndex_Embedded_injproj;
  injinj := LocalState_ι_addr_std_fixedIndex_Embedded_injinj
}.
Definition  LocalState_ι_GramsIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_GramsIndex l.

Definition  LocalState_ι_GramsIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_GramsIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_GramsIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_GramsIndex_Embedded_projEmbed (LocalState_ι_GramsIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_GramsIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_GramsIndex_Embedded_injEmbed (LocalState_ι_GramsIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_GramsIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_GramsIndex_Embedded_injEmbed t1 (LocalState_ι_GramsIndex_Embedded_injEmbed t2 s) = LocalState_ι_GramsIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_GramsIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_GramsIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_GramsIndex_Embedded_injEmbed;
  projinj := LocalState_ι_GramsIndex_Embedded_projinj;
  injproj := LocalState_ι_GramsIndex_Embedded_injproj;
  injinj := LocalState_ι_GramsIndex_Embedded_injinj
}.
Definition  LocalState_ι_SellArgsIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_SellArgsIndex l.

Definition  LocalState_ι_SellArgsIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_SellArgsIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_SellArgsIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_SellArgsIndex_Embedded_projEmbed (LocalState_ι_SellArgsIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_SellArgsIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_SellArgsIndex_Embedded_injEmbed (LocalState_ι_SellArgsIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_SellArgsIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_SellArgsIndex_Embedded_injEmbed t1 (LocalState_ι_SellArgsIndex_Embedded_injEmbed t2 s) = LocalState_ι_SellArgsIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_SellArgsIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_SellArgsIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_SellArgsIndex_Embedded_injEmbed;
  projinj := LocalState_ι_SellArgsIndex_Embedded_projinj;
  injproj := LocalState_ι_SellArgsIndex_Embedded_injproj;
  injinj := LocalState_ι_SellArgsIndex_Embedded_injinj
}.
Definition  LocalState_ι_addressIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_addressIndex l.

Definition  LocalState_ι_addressIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_addressIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_addressIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_addressIndex_Embedded_projEmbed (LocalState_ι_addressIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_addressIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_addressIndex_Embedded_injEmbed (LocalState_ι_addressIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_addressIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_addressIndex_Embedded_injEmbed t1 (LocalState_ι_addressIndex_Embedded_injEmbed t2 s) = LocalState_ι_addressIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_addressIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_addressIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_addressIndex_Embedded_injEmbed;
  projinj := LocalState_ι_addressIndex_Embedded_projinj;
  injproj := LocalState_ι_addressIndex_Embedded_injproj;
  injinj := LocalState_ι_addressIndex_Embedded_injinj
}.
Definition  LocalState_ι_DetailsInfoIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_DetailsInfoIndex l.

Definition  LocalState_ι_DetailsInfoIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_DetailsInfoIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_DetailsInfoIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_DetailsInfoIndex_Embedded_projEmbed (LocalState_ι_DetailsInfoIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_DetailsInfoIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_DetailsInfoIndex_Embedded_injEmbed (LocalState_ι_DetailsInfoIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_DetailsInfoIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_DetailsInfoIndex_Embedded_injEmbed t1 (LocalState_ι_DetailsInfoIndex_Embedded_injEmbed t2 s) = LocalState_ι_DetailsInfoIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_DetailsInfoIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_DetailsInfoIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_DetailsInfoIndex_Embedded_injEmbed;
  projinj := LocalState_ι_DetailsInfoIndex_Embedded_projinj;
  injproj := LocalState_ι_DetailsInfoIndex_Embedded_injproj;
  injinj := LocalState_ι_DetailsInfoIndex_Embedded_injinj
}.
Definition  LocalState_ι_dict_arrayOrderInfoIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_dict_arrayOrderInfoIndex l.

Definition  LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_dict_arrayOrderInfoIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_dict_arrayOrderInfoIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_dict_arrayOrderInfoIndex_Embedded_projEmbed (LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injEmbed (LocalState_ι_dict_arrayOrderInfoIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injEmbed t1 (LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injEmbed t2 s) = LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_dict_arrayOrderInfoIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_dict_arrayOrderInfoIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injEmbed;
  projinj := LocalState_ι_dict_arrayOrderInfoIndex_Embedded_projinj;
  injproj := LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injproj;
  injinj := LocalState_ι_dict_arrayOrderInfoIndex_Embedded_injinj
}.
Definition  LocalState_ι_optaddressIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_optaddressIndex l.

Definition  LocalState_ι_optaddressIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_optaddressIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_optaddressIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_optaddressIndex_Embedded_projEmbed (LocalState_ι_optaddressIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_optaddressIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_optaddressIndex_Embedded_injEmbed (LocalState_ι_optaddressIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_optaddressIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_optaddressIndex_Embedded_injEmbed t1 (LocalState_ι_optaddressIndex_Embedded_injEmbed t2 s) = LocalState_ι_optaddressIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_optaddressIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_optaddressIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_optaddressIndex_Embedded_injEmbed;
  projinj := LocalState_ι_optaddressIndex_Embedded_projinj;
  injproj := LocalState_ι_optaddressIndex_Embedded_injproj;
  injinj := LocalState_ι_optaddressIndex_Embedded_injinj
}.
Definition  LocalState_ι_TONTokenWalletIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_TONTokenWalletIndex l.

Definition  LocalState_ι_TONTokenWalletIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_TONTokenWalletIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_TONTokenWalletIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_TONTokenWalletIndex_Embedded_projEmbed (LocalState_ι_TONTokenWalletIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_TONTokenWalletIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_TONTokenWalletIndex_Embedded_injEmbed (LocalState_ι_TONTokenWalletIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_TONTokenWalletIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_TONTokenWalletIndex_Embedded_injEmbed t1 (LocalState_ι_TONTokenWalletIndex_Embedded_injEmbed t2 s) = LocalState_ι_TONTokenWalletIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_TONTokenWalletIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_TONTokenWalletIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_TONTokenWalletIndex_Embedded_injEmbed;
  projinj := LocalState_ι_TONTokenWalletIndex_Embedded_projinj;
  injproj := LocalState_ι_TONTokenWalletIndex_Embedded_injproj;
  injinj := LocalState_ι_TONTokenWalletIndex_Embedded_injinj
}.
Definition  LocalState_ι_tpladdressGramsIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_tpladdressGramsIndex l.

Definition  LocalState_ι_tpladdressGramsIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_tpladdressGramsIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_tpladdressGramsIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_tpladdressGramsIndex_Embedded_projEmbed (LocalState_ι_tpladdressGramsIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_tpladdressGramsIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_tpladdressGramsIndex_Embedded_injEmbed (LocalState_ι_tpladdressGramsIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_tpladdressGramsIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_tpladdressGramsIndex_Embedded_injEmbed t1 (LocalState_ι_tpladdressGramsIndex_Embedded_injEmbed t2 s) = LocalState_ι_tpladdressGramsIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_tpladdressGramsIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_tpladdressGramsIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_tpladdressGramsIndex_Embedded_injEmbed;
  projinj := LocalState_ι_tpladdressGramsIndex_Embedded_projinj;
  injproj := LocalState_ι_tpladdressGramsIndex_Embedded_injproj;
  injinj := LocalState_ι_tpladdressGramsIndex_Embedded_injinj
}.
Definition  LocalState_ι_XSliceIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_XSliceIndex l.

Definition  LocalState_ι_XSliceIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_XSliceIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_XSliceIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_XSliceIndex_Embedded_projEmbed (LocalState_ι_XSliceIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_XSliceIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_XSliceIndex_Embedded_injEmbed (LocalState_ι_XSliceIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_XSliceIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_XSliceIndex_Embedded_injEmbed t1 (LocalState_ι_XSliceIndex_Embedded_injEmbed t2 s) = LocalState_ι_XSliceIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_XSliceIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_XSliceIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_XSliceIndex_Embedded_injEmbed;
  projinj := LocalState_ι_XSliceIndex_Embedded_projinj;
  injproj := LocalState_ι_XSliceIndex_Embedded_injproj;
  injinj := LocalState_ι_XSliceIndex_Embedded_injinj
}.
Definition  LocalState_ι_optOrderRetIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_optOrderRetIndex l.

Definition  LocalState_ι_optOrderRetIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_optOrderRetIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_optOrderRetIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_optOrderRetIndex_Embedded_projEmbed (LocalState_ι_optOrderRetIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_optOrderRetIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_optOrderRetIndex_Embedded_injEmbed (LocalState_ι_optOrderRetIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_optOrderRetIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_optOrderRetIndex_Embedded_injEmbed t1 (LocalState_ι_optOrderRetIndex_Embedded_injEmbed t2 s) = LocalState_ι_optOrderRetIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_optOrderRetIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_optOrderRetIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_optOrderRetIndex_Embedded_injEmbed;
  projinj := LocalState_ι_optOrderRetIndex_Embedded_projinj;
  injproj := LocalState_ι_optOrderRetIndex_Embedded_injproj;
  injinj := LocalState_ι_optOrderRetIndex_Embedded_injinj
}.
(****************************************************************************)

Global Instance LocalState_cellIndex: LocalStateField XCell :=
{
  local_index_embedded := LocalState_ι_cellIndex_Embedded;
  local_state_field := LocalState_ι_cell; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_StateInitIndex: LocalStateField StateInit :=
{
  local_index_embedded := LocalState_ι_StateInitIndex_Embedded;
  local_state_field := LocalState_ι_StateInit; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_tplStateInituint256Index: LocalStateField ( StateInit * XInteger256 ) :=
{
  local_index_embedded := LocalState_ι_tplStateInituint256Index_Embedded;
  local_state_field := LocalState_ι_tplStateInituint256; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_boolIndex: LocalStateField XBool :=
{
  local_index_embedded := LocalState_ι_boolIndex_Embedded;
  local_state_field := LocalState_ι_bool; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_uint32Index: LocalStateField XInteger32 :=
{
  local_index_embedded := LocalState_ι_uint32Index_Embedded;
  local_state_field := LocalState_ι_uint32; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_PriceIndex: LocalStateField Price :=
{
  local_index_embedded := LocalState_ι_PriceIndex_Embedded;
  local_state_field := LocalState_ι_Price; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_optuint128Index: LocalStateField ( XMaybe XInteger128 ) :=
{
  local_index_embedded := LocalState_ι_optuint128Index_Embedded;
  local_state_field := LocalState_ι_optuint128; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_uint128Index: LocalStateField XInteger128 :=
{
  local_index_embedded := LocalState_ι_uint128Index_Embedded;
  local_state_field := LocalState_ι_uint128; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_tplboolboolIndex: LocalStateField ( XBool * XBool * XInteger128 ) :=
{
  local_index_embedded := LocalState_ι_tplboolboolIndex_Embedded;
  local_state_field := LocalState_ι_tplboolbool; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_OrderInfoIndex: LocalStateField OrderInfo :=
{
  local_index_embedded := LocalState_ι_OrderInfoIndex_Embedded;
  local_state_field := LocalState_ι_OrderInfo; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_intIndex: LocalStateField XInteger :=
{
  local_index_embedded := LocalState_ι_intIndex_Embedded;
  local_state_field := LocalState_ι_int; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex: LocalStateField (XMaybe (XInteger * OrderInfo) * (XList OrderInfo) * XInteger128 ) :=
{
  local_index_embedded := LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfoIndex_Embedded;
  local_state_field := LocalState_ι_tploptional_pair_unsigned_OrderInfoqueue_OrderInfo; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_optpair_unsigned_OrderInfo__Index: LocalStateField ( XMaybe (XInteger * OrderInfo) ) :=
{
  local_index_embedded := LocalState_ι_optpair_unsigned_OrderInfo__Index_Embedded;
  local_state_field := LocalState_ι_optpair_unsigned_OrderInfo__; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_queueOrderInfoIndex: LocalStateField ( XList OrderInfo ) :=
{
  local_index_embedded := LocalState_ι_queueOrderInfoIndex_Embedded;
  local_state_field := LocalState_ι_queueOrderInfo; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_OrderRetIndex: LocalStateField OrderRet :=
{
  local_index_embedded := LocalState_ι_OrderRetIndex_Embedded;
  local_state_field := LocalState_ι_OrderRet; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_unsignedIndex: LocalStateField XInteger :=
{
  local_index_embedded := LocalState_ι_unsignedIndex_Embedded;
  local_state_field := LocalState_ι_unsigned; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_dealerIndex: LocalStateField dealer :=
{
  local_index_embedded := LocalState_ι_dealerIndex_Embedded;
  local_state_field := LocalState_ι_dealer; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_process_retIndex: LocalStateField process_ret :=
{
  local_index_embedded := LocalState_ι_process_retIndex_Embedded;
  local_state_field := LocalState_ι_process_ret; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_uint8Index: LocalStateField XInteger8 :=
{
  local_index_embedded := LocalState_ι_uint8Index_Embedded;
  local_state_field := LocalState_ι_uint8; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_TonsConfigIndex: LocalStateField TonsConfig :=
{
  local_index_embedded := LocalState_ι_TonsConfigIndex_Embedded;
  local_state_field := LocalState_ι_TonsConfig; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_tplqueue_OrderInfouint128Index: LocalStateField ( (XList OrderInfo) * XInteger128 ) :=
{
  local_index_embedded := LocalState_ι_tplqueue_OrderInfouint128Index_Embedded;
  local_state_field := LocalState_ι_tplqueue_OrderInfouint128; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_addr_std_fixedIndex: LocalStateField addr_std_fixed :=
{
  local_index_embedded := LocalState_ι_addr_std_fixedIndex_Embedded;
  local_state_field := LocalState_ι_addr_std_fixed; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_GramsIndex: LocalStateField Grams :=
{
  local_index_embedded := LocalState_ι_GramsIndex_Embedded;
  local_state_field := LocalState_ι_Grams; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_SellArgsIndex: LocalStateField SellArgs :=
{
  local_index_embedded := LocalState_ι_SellArgsIndex_Embedded;
  local_state_field := LocalState_ι_SellArgs; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_addressIndex: LocalStateField XAddress :=
{
  local_index_embedded := LocalState_ι_addressIndex_Embedded;
  local_state_field := LocalState_ι_address; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_DetailsInfoIndex: LocalStateField DetailsInfo :=
{
  local_index_embedded := LocalState_ι_DetailsInfoIndex_Embedded;
  local_state_field := LocalState_ι_DetailsInfo; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_dict_arrayOrderInfoIndex: LocalStateField ( XHMap XInteger OrderInfo ) :=
{
  local_index_embedded := LocalState_ι_dict_arrayOrderInfoIndex_Embedded;
  local_state_field := LocalState_ι_dict_arrayOrderInfo; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_optaddressIndex: LocalStateField ( XMaybe XAddress ) :=
{
  local_index_embedded := LocalState_ι_optaddressIndex_Embedded;
  local_state_field := LocalState_ι_optaddress; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_TONTokenWalletIndex: LocalStateField TONTokenWallet :=
{
  local_index_embedded := LocalState_ι_TONTokenWalletIndex_Embedded;
  local_state_field := LocalState_ι_TONTokenWallet; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_tpladdressGramsIndex: LocalStateField ( XAddress * Grams ) :=
{
  local_index_embedded := LocalState_ι_tpladdressGramsIndex_Embedded;
  local_state_field := LocalState_ι_tpladdressGrams; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_XSliceIndex: LocalStateField XSlice :=
{
  local_index_embedded := LocalState_ι_XSliceIndex_Embedded;
  local_state_field := LocalState_ι_XSlice; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_optOrderRetIndex: LocalStateField ( XMaybe OrderRet ) :=
{
  local_index_embedded := LocalState_ι_optOrderRetIndex_Embedded;
  local_state_field := LocalState_ι_optOrderRet; 
  local_field_type_correct := eq_refl
}.





Global Instance LocalStateField_XInteger: LocalStateField XInteger :=
{
  local_index_embedded := LocalState_ι_intIndex_Embedded;
  local_state_field := LocalState_ι_int; 
  local_field_type_correct := eq_refl
}.
 
Global Instance LocalStateField_XBool: LocalStateField XBool :=
{
  local_index_embedded := LocalState_ι_boolIndex_Embedded;
  local_state_field := LocalState_ι_bool; 
  local_field_type_correct := eq_refl
}.

Global Instance LocalStateField_XCell: LocalStateField XCell :=
{
  local_index_embedded := LocalState_ι_cellIndex_Embedded;
  local_state_field := LocalState_ι_cell; 
  local_field_type_correct := eq_refl
}.




 

Definition LedgerVMStateEmbedded := embeddedT2. 
Definition LedgerVMStateField := Ledger_ι_VMState .
Definition isoVMState := iso_T2.

Definition MessagesAndEvents := VMStateLRecord.
Definition LedgerMessagesEmbedded := embeddedT2.
Definition LedgerMessagesField := Ledger_ι_VMState.
Definition isoMessages := iso_T2.


End LedgerPriceClass .
