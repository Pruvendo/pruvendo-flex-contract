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
 Require Import UMLang.SML_NG26. 
 Require Import UrsusTVM.tvmFunc. 
 
 Local Open Scope record. 
 Local Open Scope program_scope. 
 
 Require Import UMLang.ProofEnvironment2. 
 
 
 Module LedgerClass (xt: XTypesSig) (sm: StateMonadSig) <: ClassSig xt. 
 
 
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
Definition varuint32 := XInteger32 .
 

(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 2 *) Definition TickTock := 
 ( XBool * 
 XBool )%type .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 2 *) Definition StateInit := 
 ( XMaybe XInteger * 
 XMaybe TickTock * 
 XMaybe TvmCell * 
 XMaybe TvmCell * 
 XMaybe TvmCell )%type .
(* 1 *) Inductive anycast_infoFields := | anycast_info_ι_rewrite_pfx .
(* 2 *) Definition anycast_info := 
 ( varuint32 )%type .
(* 1 *) Inductive addr_stdFields := | addr_std_ι_kind | addr_std_ι_Anycast | addr_std_ι_workchain_id | addr_std_ι_address .
(* 2 *) Definition addr_std := 
 ( XInteger * 
 XMaybe anycast_info * 
 XInteger8 * 
 XInteger256 )%type .
(* 1 *) Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address .
(* 2 *) Definition addr_std_fixed := 
 ( XInteger8 * 
 XInteger256 )%type .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
(* 2 *) Definition SellArgs := 
 ( XInteger128 * 
 addr_std_fixed )%type .
(* 1 *) Inductive FlexBurnWalletArgsFields := | FlexBurnWalletArgs_ι_tons_value | FlexBurnWalletArgs_ι_out_pubkey | FlexBurnWalletArgs_ι_out_internal_owner | FlexBurnWalletArgs_ι_my_tip3_addr .
(* 2 *) Definition FlexBurnWalletArgs := 
 ( XInteger128 * 
 XInteger256 * 
 XAddress * 
 XAddress )%type .
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 2 *) Definition TonsConfig := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 )%type .
(* 1 *) Inductive FLeXClientFields := | FLeXClient_ι_owner_ | FLeXClient_ι_trading_pair_code_ | FLeXClient_ι_xchg_pair_code_ | FLeXClient_ι_workchain_id_ | FLeXClient_ι_tons_cfg_ | FLeXClient_ι_flex_ | FLeXClient_ι_notify_addr_ | FLeXClient_ι_ext_wallet_code_ | FLeXClient_ι_flex_wallet_code_ | FLeXClient_ι_flex_wrapper_code_ .
(* 2 *) Definition FLeXClient := 
 ( XInteger256 * 
 TvmCell * 
 TvmCell * 
 XInteger8 * 
 TonsConfig * 
 addr_std_compact * 
 addr_std_compact * 
 XMaybe TvmCell * 
 XMaybe TvmCell * 
 XMaybe TvmCell )%type .
(* 1 *) Inductive FLeXSellArgsAddrsFields := | FLeXSellArgsAddrs_ι_my_tip3_addr .
(* 2 *) Definition FLeXSellArgsAddrs := 
 ( XAddress )%type .
(* 1 *) Inductive FLeXSellArgsFields := | FLeXSellArgs_ι_price | FLeXSellArgs_ι_amount | FLeXSellArgs_ι_lend_finish_time | FLeXSellArgs_ι_min_amount | FLeXSellArgs_ι_deals_limit | FLeXSellArgs_ι_tons_value | FLeXSellArgs_ι_price_code | FLeXSellArgs_ι_addrs | FLeXSellArgs_ι_tip3_code | FLeXSellArgs_ι_tip3cfg .
(* 2 *) Definition FLeXSellArgs := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger32 * 
 XInteger128 * 
 XInteger8 * 
 XInteger128 * 
 TvmCell * 
 XAddress * 
 TvmCell * 
 XAddress )%type .
(* 1 *) Inductive FLeXBuyArgsFields := | FLeXBuyArgs_ι_price | FLeXBuyArgs_ι_amount | FLeXBuyArgs_ι_order_finish_time | FLeXBuyArgs_ι_min_amount | FLeXBuyArgs_ι_deals_limit | FLeXBuyArgs_ι_deploy_value | FLeXBuyArgs_ι_price_code | FLeXBuyArgs_ι_my_tip3_addr | FLeXBuyArgs_ι_tip3_code | FLeXBuyArgs_ι_tip3cfg .
(* 2 *) Definition FLeXBuyArgs := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger32 * 
 XInteger128 * 
 XInteger8 * 
 XInteger128 * 
 TvmCell * 
 XAddress * 
 TvmCell * 
 XAddress )%type .
(* 1 *) Inductive FLeXXchgCfgsFields := | FLeXXchgCfgs_ι_major_tip3cfg | FLeXXchgCfgs_ι_minor_tip3cfg .
(* 2 *) Definition FLeXXchgCfgs := 
 ( XAddress * 
 XAddress )%type .
(* 1 *) Inductive FLeXXchgArgsFields := | FLeXXchgArgs_ι_sell | FLeXXchgArgs_ι_price_num | FLeXXchgArgs_ι_price_denum | FLeXXchgArgs_ι_amount | FLeXXchgArgs_ι_lend_amount | FLeXXchgArgs_ι_lend_finish_time | FLeXXchgArgs_ι_min_amount | FLeXXchgArgs_ι_deals_limit | FLeXXchgArgs_ι_tons_value | FLeXXchgArgs_ι_xchg_price_code | FLeXXchgArgs_ι_addrs | FLeXXchgArgs_ι_tip3_code | FLeXXchgArgs_ι_tip3cfgs .
(* 2 *) Definition FLeXXchgArgs := 
 ( XBool * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger32 * 
 XInteger128 * 
 XInteger8 * 
 XInteger128 * 
 TvmCell * 
 XAddress * 
 TvmCell * 
 XAddress )%type .
(* 1 *) Inductive FLeXCancelArgsFields := | FLeXCancelArgs_ι_price | FLeXCancelArgs_ι_min_amount | FLeXCancelArgs_ι_deals_limit | FLeXCancelArgs_ι_value | FLeXCancelArgs_ι_price_code | FLeXCancelArgs_ι_tip3_code | FLeXCancelArgs_ι_tip3cfg .
(* 2 *) Definition FLeXCancelArgs := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger8 * 
 XInteger128 * 
 TvmCell * 
 TvmCell * 
 XAddress )%type .
(* 1 *) Inductive FLeXXchgCancelArgsFields := | FLeXXchgCancelArgs_ι_sell | FLeXXchgCancelArgs_ι_price_num | FLeXXchgCancelArgs_ι_price_denum | FLeXXchgCancelArgs_ι_min_amount | FLeXXchgCancelArgs_ι_deals_limit | FLeXXchgCancelArgs_ι_value | FLeXXchgCancelArgs_ι_xchg_price_code | FLeXXchgCancelArgs_ι_tip3_code | FLeXXchgCancelArgs_ι_tip3cfgs .
(* 2 *) Definition FLeXXchgCancelArgs := 
 ( XBool * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger8 * 
 XInteger128 * 
 TvmCell * 
 TvmCell * 
 XAddress )%type .
(* 1 *) Inductive XchgPairFields := | XchgPair_ι_flex_addr_ | XchgPair_ι_tip3_major_root_ | XchgPair_ι_tip3_minor_root_ | XchgPair_ι_deploy_value_ .
(* 2 *) Definition XchgPair := 
 ( XAddress * 
 XAddress * 
 XAddress * 
 XInteger128 )%type .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 2 *) Definition OrderInfo := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 addr_std_fixed * 
 addr_std_fixed * 
 XInteger32 )%type .
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
 IFLeXNotifyPtr * 
 XInteger8 * 
 TonsConfig * 
 TvmCell * 
 Tip3Config * 
 XList OrderInfo * 
 XList OrderInfo )%type .
(* 1 *) Inductive RationalPriceFields := | RationalPrice_ι_num | RationalPrice_ι_denum .
(* 2 *) Definition RationalPrice := 
 ( XInteger128 * 
 XInteger128 )%type .
(* 1 *) Inductive PriceXchgFields := | PriceXchg_ι_price_ | PriceXchg_ι_sells_amount_ | PriceXchg_ι_buys_amount_ | PriceXchg_ι_flex_ | PriceXchg_ι_min_amount_ | PriceXchg_ι_deals_limit_ | PriceXchg_ι_notify_addr_ | PriceXchg_ι_workchain_id_ | PriceXchg_ι_tons_cfg_ | PriceXchg_ι_tip3_code_ | PriceXchg_ι_major_tip3cfg_ | PriceXchg_ι_minor_tip3cfg_ .
(* 2 *) Definition PriceXchg := 
 ( RationalPrice * 
 XInteger128 * 
 XInteger128 * 
 addr_std_fixed * 
 XInteger128 * 
 XInteger8 * 
 IFLeXNotifyPtr * 
 XInteger8 * 
 TonsConfig * 
 TvmCell * 
 Tip3Config * 
 Tip3Config )%type .
(* 1 *) Inductive TradingPairFields := | TradingPair_ι_flex_addr_ | TradingPair_ι_tip3_root_ | TradingPair_ι_deploy_value_ .
(* 2 *) Definition TradingPair := 
 ( XAddress * 
 XAddress * 
 XInteger128 )%type .
(* 1 *) Inductive PayloadArgsFields := | PayloadArgs_ι_sell | PayloadArgs_ι_amount | PayloadArgs_ι_receive_tip3_wallet | PayloadArgs_ι_client_addr .
(* 2 *) Definition PayloadArgs := 
 ( XBool * 
 XInteger128 * 
 XAddress * 
 XAddress )%type .
(* 1 *) Inductive LocalStateFields := | LocalState_ι_uint256 | LocalState_ι_cell | LocalState_ι_TonsConfig | LocalState_ι_address | LocalState_ι_uint128 | LocalState_ι_TradingPair | LocalState_ι_tplStateInituint256 | LocalState_ι_StateInit | LocalState_ι_XchgPair | LocalState_ι_tplStateInitaddress | LocalState_ι_SellArgs | LocalState_ι_ITONTokenWalletPtr | LocalState_ι_IPricePtr | LocalState_ι_int | LocalState_ι_Price | LocalState_ι_uint8 | LocalState_ι_uint32 | LocalState_ι_Tip3Config | LocalState_ι_PriceXchg | LocalState_ι_PayloadArgs | LocalState_ι_uint256Index | LocalState_ι_cellIndex | LocalState_ι_TonsConfigIndex | LocalState_ι_addressIndex | LocalState_ι_uint128Index | LocalState_ι_TradingPairIndex | LocalState_ι_tplStateInituint256Index | LocalState_ι_StateInitIndex | LocalState_ι_XchgPairIndex | LocalState_ι_tplStateInitaddressIndex | LocalState_ι_SellArgsIndex | LocalState_ι_ITONTokenWalletPtrIndex | LocalState_ι_IPricePtrIndex | LocalState_ι_intIndex | LocalState_ι_PriceIndex | LocalState_ι_uint8Index | LocalState_ι_uint32Index | LocalState_ι_Tip3ConfigIndex | LocalState_ι_PriceXchgIndex | LocalState_ι_PayloadArgsIndex .
(* 2 *) Definition LocalState := 
 ( XHMap (string*nat) XInteger256 * 
 XHMap (string*nat) TvmCell * 
 XHMap (string*nat) TonsConfig * 
 XHMap (string*nat) XAddress * 
 XHMap (string*nat) XInteger128 * 
 XHMap (string*nat) TradingPair * 
 XHMap (string*nat) ( StateInit * XInteger256 ) * 
 XHMap (string*nat) StateInit * 
 XHMap (string*nat) XchgPair * 
 XHMap (string*nat) ( StateInit * XAddress * XInteger256 ) * 
 XHMap (string*nat) SellArgs * 
 XHMap (string*nat) ITONTokenWalletPtr * 
 XHMap (string*nat) IPricePtr * 
 XHMap (string*nat) XInteger * 
 XHMap (string*nat) Price * 
 XHMap (string*nat) XInteger8 * 
 XHMap (string*nat) XInteger32 * 
 XHMap (string*nat) Tip3Config * 
 XHMap (string*nat) PriceXchg * 
 XHMap (string*nat) PayloadArgs * 
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
(* 1 *) Inductive LedgerFieldsI := | Ledger_ι_FLeXClient | Ledger_ι_VMState | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .
(* 2 *) Definition Ledger := 
 ( FLeXClient * 
 VMState * 
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
 | StateInit_ι_split_depth => XMaybe XInteger | StateInit_ι_special => XMaybe TickTock | StateInit_ι_code => XMaybe TvmCell | StateInit_ι_data => XMaybe TvmCell | StateInit_ι_library => XMaybe TvmCell end .
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
(* 3 *) Definition anycast_info_field_type f : Type :=  
match f with 
 | anycast_info_ι_rewrite_pfx => varuint32 end .
(* 4 *) Definition anycast_info_get (f: anycast_infoFields )(r: anycast_info ) :  anycast_info_field_type f := 
 let '( r1 ) := r in 
 match f with 
 | anycast_info_ι_rewrite_pfx => r1 
 end .
(* 5 *) Coercion anycast_info_get : anycast_infoFields >-> Funclass .
(* 6 *) Definition anycast_info_set (f: anycast_infoFields ) 
(v: anycast_info_field_type f) (r: anycast_info ): anycast_info := 
 let '( r1 ) := r in 
 match f, v with 
 | anycast_info_ι_rewrite_pfx , v' => ( v' ) 
 end .
(* 7 *) Global Instance anycast_info_PruvendoRecord : PruvendoRecord anycast_info anycast_infoFields :=
{
  field_type := anycast_info_field_type; 
  getPruvendoRecord := @anycast_info_get ;
  setPruvendoRecord := @anycast_info_set ;
} .
(* 3 *) Definition addr_std_field_type f : Type :=  
match f with 
 | addr_std_ι_kind => XInteger | addr_std_ι_Anycast => XMaybe anycast_info | addr_std_ι_workchain_id => XInteger8 | addr_std_ι_address => XInteger256 end .
(* 4 *) Definition addr_std_get (f: addr_stdFields )(r: addr_std ) :  addr_std_field_type f := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f with 
 | addr_std_ι_kind => r1 
 | addr_std_ι_Anycast => r2 
 | addr_std_ι_workchain_id => r3 
 | addr_std_ι_address => r4 
 end .
(* 5 *) Coercion addr_std_get : addr_stdFields >-> Funclass .
(* 6 *) Definition addr_std_set (f: addr_stdFields ) 
(v: addr_std_field_type f) (r: addr_std ): addr_std := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f, v with 
 | addr_std_ι_kind , v' => ( v' , r2 , r3 , r4 ) 
 | addr_std_ι_Anycast , v' => ( r1 , v' , r3 , r4 ) 
 | addr_std_ι_workchain_id , v' => ( r1 , r2 , v' , r4 ) 
 | addr_std_ι_address , v' => ( r1 , r2 , r3 , v' ) 
 end .
(* 7 *) Global Instance addr_std_PruvendoRecord : PruvendoRecord addr_std addr_stdFields :=
{
  field_type := addr_std_field_type; 
  getPruvendoRecord := @addr_std_get ;
  setPruvendoRecord := @addr_std_set ;
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
(* 3 *) Definition SellArgs_field_type f : Type :=  
match f with 
 | SellArgs_ι_amount => XInteger128 | SellArgs_ι_receive_wallet => addr_std_fixed end .
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
(* 3 *) Definition FlexBurnWalletArgs_field_type f : Type :=  
match f with 
 | FlexBurnWalletArgs_ι_tons_value => XInteger128 | FlexBurnWalletArgs_ι_out_pubkey => XInteger256 | FlexBurnWalletArgs_ι_out_internal_owner => XAddress | FlexBurnWalletArgs_ι_my_tip3_addr => XAddress end .
(* 4 *) Definition FlexBurnWalletArgs_get (f: FlexBurnWalletArgsFields )(r: FlexBurnWalletArgs ) :  FlexBurnWalletArgs_field_type f := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f with 
 | FlexBurnWalletArgs_ι_tons_value => r1 
 | FlexBurnWalletArgs_ι_out_pubkey => r2 
 | FlexBurnWalletArgs_ι_out_internal_owner => r3 
 | FlexBurnWalletArgs_ι_my_tip3_addr => r4 
 end .
(* 5 *) Coercion FlexBurnWalletArgs_get : FlexBurnWalletArgsFields >-> Funclass .
(* 6 *) Definition FlexBurnWalletArgs_set (f: FlexBurnWalletArgsFields ) 
(v: FlexBurnWalletArgs_field_type f) (r: FlexBurnWalletArgs ): FlexBurnWalletArgs := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f, v with 
 | FlexBurnWalletArgs_ι_tons_value , v' => ( v' , r2 , r3 , r4 ) 
 | FlexBurnWalletArgs_ι_out_pubkey , v' => ( r1 , v' , r3 , r4 ) 
 | FlexBurnWalletArgs_ι_out_internal_owner , v' => ( r1 , r2 , v' , r4 ) 
 | FlexBurnWalletArgs_ι_my_tip3_addr , v' => ( r1 , r2 , r3 , v' ) 
 end .
(* 7 *) Global Instance FlexBurnWalletArgs_PruvendoRecord : PruvendoRecord FlexBurnWalletArgs FlexBurnWalletArgsFields :=
{
  field_type := FlexBurnWalletArgs_field_type; 
  getPruvendoRecord := @FlexBurnWalletArgs_get ;
  setPruvendoRecord := @FlexBurnWalletArgs_set ;
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
(* 3 *) Definition FLeXClient_field_type f : Type :=  
match f with 
 | FLeXClient_ι_owner_ => XInteger256 | FLeXClient_ι_trading_pair_code_ => TvmCell | FLeXClient_ι_xchg_pair_code_ => TvmCell | FLeXClient_ι_workchain_id_ => XInteger8 | FLeXClient_ι_tons_cfg_ => TonsConfig | FLeXClient_ι_flex_ => addr_std_compact | FLeXClient_ι_notify_addr_ => addr_std_compact | FLeXClient_ι_ext_wallet_code_ => XMaybe TvmCell | FLeXClient_ι_flex_wallet_code_ => XMaybe TvmCell | FLeXClient_ι_flex_wrapper_code_ => XMaybe TvmCell end .
(* 4 *) Definition FLeXClient_get (f: FLeXClientFields )(r: FLeXClient ) :  FLeXClient_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) := r in 
 match f with 
 | FLeXClient_ι_owner_ => r1 
 | FLeXClient_ι_trading_pair_code_ => r2 
 | FLeXClient_ι_xchg_pair_code_ => r3 
 | FLeXClient_ι_workchain_id_ => r4 
 | FLeXClient_ι_tons_cfg_ => r5 
 | FLeXClient_ι_flex_ => r6 
 | FLeXClient_ι_notify_addr_ => r7 
 | FLeXClient_ι_ext_wallet_code_ => r8 
 | FLeXClient_ι_flex_wallet_code_ => r9 
 | FLeXClient_ι_flex_wrapper_code_ => r10 
 end .
(* 5 *) Coercion FLeXClient_get : FLeXClientFields >-> Funclass .
(* 6 *) Definition FLeXClient_set (f: FLeXClientFields ) 
(v: FLeXClient_field_type f) (r: FLeXClient ): FLeXClient := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) := r in 
 match f, v with 
 | FLeXClient_ι_owner_ , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXClient_ι_trading_pair_code_ , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXClient_ι_xchg_pair_code_ , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXClient_ι_workchain_id_ , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXClient_ι_tons_cfg_ , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXClient_ι_flex_ , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 ) 
 | FLeXClient_ι_notify_addr_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 ) 
 | FLeXClient_ι_ext_wallet_code_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 ) 
 | FLeXClient_ι_flex_wallet_code_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 ) 
 | FLeXClient_ι_flex_wrapper_code_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' ) 
 end .
(* 7 *) Global Instance FLeXClient_PruvendoRecord : PruvendoRecord FLeXClient FLeXClientFields :=
{
  field_type := FLeXClient_field_type; 
  getPruvendoRecord := @FLeXClient_get ;
  setPruvendoRecord := @FLeXClient_set ;
} .
(* 3 *) Definition FLeXSellArgsAddrs_field_type f : Type :=  
match f with 
 | FLeXSellArgsAddrs_ι_my_tip3_addr => XAddress end .
(* 4 *) Definition FLeXSellArgsAddrs_get (f: FLeXSellArgsAddrsFields )(r: FLeXSellArgsAddrs ) :  FLeXSellArgsAddrs_field_type f := 
 let '( r1 ) := r in 
 match f with 
 | FLeXSellArgsAddrs_ι_my_tip3_addr => r1 
 end .
(* 5 *) Coercion FLeXSellArgsAddrs_get : FLeXSellArgsAddrsFields >-> Funclass .
(* 6 *) Definition FLeXSellArgsAddrs_set (f: FLeXSellArgsAddrsFields ) 
(v: FLeXSellArgsAddrs_field_type f) (r: FLeXSellArgsAddrs ): FLeXSellArgsAddrs := 
 let '( r1 ) := r in 
 match f, v with 
 | FLeXSellArgsAddrs_ι_my_tip3_addr , v' => ( v' ) 
 end .
(* 7 *) Global Instance FLeXSellArgsAddrs_PruvendoRecord : PruvendoRecord FLeXSellArgsAddrs FLeXSellArgsAddrsFields :=
{
  field_type := FLeXSellArgsAddrs_field_type; 
  getPruvendoRecord := @FLeXSellArgsAddrs_get ;
  setPruvendoRecord := @FLeXSellArgsAddrs_set ;
} .
(* 3 *) Definition FLeXSellArgs_field_type f : Type :=  
match f with 
 | FLeXSellArgs_ι_price => XInteger128 | FLeXSellArgs_ι_amount => XInteger128 | FLeXSellArgs_ι_lend_finish_time => XInteger32 | FLeXSellArgs_ι_min_amount => XInteger128 | FLeXSellArgs_ι_deals_limit => XInteger8 | FLeXSellArgs_ι_tons_value => XInteger128 | FLeXSellArgs_ι_price_code => TvmCell | FLeXSellArgs_ι_addrs => XAddress | FLeXSellArgs_ι_tip3_code => TvmCell | FLeXSellArgs_ι_tip3cfg => XAddress end .
(* 4 *) Definition FLeXSellArgs_get (f: FLeXSellArgsFields )(r: FLeXSellArgs ) :  FLeXSellArgs_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) := r in 
 match f with 
 | FLeXSellArgs_ι_price => r1 
 | FLeXSellArgs_ι_amount => r2 
 | FLeXSellArgs_ι_lend_finish_time => r3 
 | FLeXSellArgs_ι_min_amount => r4 
 | FLeXSellArgs_ι_deals_limit => r5 
 | FLeXSellArgs_ι_tons_value => r6 
 | FLeXSellArgs_ι_price_code => r7 
 | FLeXSellArgs_ι_addrs => r8 
 | FLeXSellArgs_ι_tip3_code => r9 
 | FLeXSellArgs_ι_tip3cfg => r10 
 end .
(* 5 *) Coercion FLeXSellArgs_get : FLeXSellArgsFields >-> Funclass .
(* 6 *) Definition FLeXSellArgs_set (f: FLeXSellArgsFields ) 
(v: FLeXSellArgs_field_type f) (r: FLeXSellArgs ): FLeXSellArgs := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) := r in 
 match f, v with 
 | FLeXSellArgs_ι_price , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXSellArgs_ι_amount , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXSellArgs_ι_lend_finish_time , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXSellArgs_ι_min_amount , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXSellArgs_ι_deals_limit , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXSellArgs_ι_tons_value , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 ) 
 | FLeXSellArgs_ι_price_code , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 ) 
 | FLeXSellArgs_ι_addrs , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 ) 
 | FLeXSellArgs_ι_tip3_code , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 ) 
 | FLeXSellArgs_ι_tip3cfg , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' ) 
 end .
(* 7 *) Global Instance FLeXSellArgs_PruvendoRecord : PruvendoRecord FLeXSellArgs FLeXSellArgsFields :=
{
  field_type := FLeXSellArgs_field_type; 
  getPruvendoRecord := @FLeXSellArgs_get ;
  setPruvendoRecord := @FLeXSellArgs_set ;
} .
(* 3 *) Definition FLeXBuyArgs_field_type f : Type :=  
match f with 
 | FLeXBuyArgs_ι_price => XInteger128 | FLeXBuyArgs_ι_amount => XInteger128 | FLeXBuyArgs_ι_order_finish_time => XInteger32 | FLeXBuyArgs_ι_min_amount => XInteger128 | FLeXBuyArgs_ι_deals_limit => XInteger8 | FLeXBuyArgs_ι_deploy_value => XInteger128 | FLeXBuyArgs_ι_price_code => TvmCell | FLeXBuyArgs_ι_my_tip3_addr => XAddress | FLeXBuyArgs_ι_tip3_code => TvmCell | FLeXBuyArgs_ι_tip3cfg => XAddress end .
(* 4 *) Definition FLeXBuyArgs_get (f: FLeXBuyArgsFields )(r: FLeXBuyArgs ) :  FLeXBuyArgs_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) := r in 
 match f with 
 | FLeXBuyArgs_ι_price => r1 
 | FLeXBuyArgs_ι_amount => r2 
 | FLeXBuyArgs_ι_order_finish_time => r3 
 | FLeXBuyArgs_ι_min_amount => r4 
 | FLeXBuyArgs_ι_deals_limit => r5 
 | FLeXBuyArgs_ι_deploy_value => r6 
 | FLeXBuyArgs_ι_price_code => r7 
 | FLeXBuyArgs_ι_my_tip3_addr => r8 
 | FLeXBuyArgs_ι_tip3_code => r9 
 | FLeXBuyArgs_ι_tip3cfg => r10 
 end .
(* 5 *) Coercion FLeXBuyArgs_get : FLeXBuyArgsFields >-> Funclass .
(* 6 *) Definition FLeXBuyArgs_set (f: FLeXBuyArgsFields ) 
(v: FLeXBuyArgs_field_type f) (r: FLeXBuyArgs ): FLeXBuyArgs := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) := r in 
 match f, v with 
 | FLeXBuyArgs_ι_price , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXBuyArgs_ι_amount , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXBuyArgs_ι_order_finish_time , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXBuyArgs_ι_min_amount , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXBuyArgs_ι_deals_limit , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 ) 
 | FLeXBuyArgs_ι_deploy_value , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 ) 
 | FLeXBuyArgs_ι_price_code , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 ) 
 | FLeXBuyArgs_ι_my_tip3_addr , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 ) 
 | FLeXBuyArgs_ι_tip3_code , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 ) 
 | FLeXBuyArgs_ι_tip3cfg , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' ) 
 end .
(* 7 *) Global Instance FLeXBuyArgs_PruvendoRecord : PruvendoRecord FLeXBuyArgs FLeXBuyArgsFields :=
{
  field_type := FLeXBuyArgs_field_type; 
  getPruvendoRecord := @FLeXBuyArgs_get ;
  setPruvendoRecord := @FLeXBuyArgs_set ;
} .
(* 3 *) Definition FLeXXchgCfgs_field_type f : Type :=  
match f with 
 | FLeXXchgCfgs_ι_major_tip3cfg => XAddress | FLeXXchgCfgs_ι_minor_tip3cfg => XAddress end .
(* 4 *) Definition FLeXXchgCfgs_get (f: FLeXXchgCfgsFields )(r: FLeXXchgCfgs ) :  FLeXXchgCfgs_field_type f := 
 let '( r1 , r2 ) := r in 
 match f with 
 | FLeXXchgCfgs_ι_major_tip3cfg => r1 
 | FLeXXchgCfgs_ι_minor_tip3cfg => r2 
 end .
(* 5 *) Coercion FLeXXchgCfgs_get : FLeXXchgCfgsFields >-> Funclass .
(* 6 *) Definition FLeXXchgCfgs_set (f: FLeXXchgCfgsFields ) 
(v: FLeXXchgCfgs_field_type f) (r: FLeXXchgCfgs ): FLeXXchgCfgs := 
 let '( r1 , r2 ) := r in 
 match f, v with 
 | FLeXXchgCfgs_ι_major_tip3cfg , v' => ( v' , r2 ) 
 | FLeXXchgCfgs_ι_minor_tip3cfg , v' => ( r1 , v' ) 
 end .
(* 7 *) Global Instance FLeXXchgCfgs_PruvendoRecord : PruvendoRecord FLeXXchgCfgs FLeXXchgCfgsFields :=
{
  field_type := FLeXXchgCfgs_field_type; 
  getPruvendoRecord := @FLeXXchgCfgs_get ;
  setPruvendoRecord := @FLeXXchgCfgs_set ;
} .
(* 3 *) Definition FLeXXchgArgs_field_type f : Type :=  
match f with 
 | FLeXXchgArgs_ι_sell => XBool | FLeXXchgArgs_ι_price_num => XInteger128 | FLeXXchgArgs_ι_price_denum => XInteger128 | FLeXXchgArgs_ι_amount => XInteger128 | FLeXXchgArgs_ι_lend_amount => XInteger128 | FLeXXchgArgs_ι_lend_finish_time => XInteger32 | FLeXXchgArgs_ι_min_amount => XInteger128 | FLeXXchgArgs_ι_deals_limit => XInteger8 | FLeXXchgArgs_ι_tons_value => XInteger128 | FLeXXchgArgs_ι_xchg_price_code => TvmCell | FLeXXchgArgs_ι_addrs => XAddress | FLeXXchgArgs_ι_tip3_code => TvmCell | FLeXXchgArgs_ι_tip3cfgs => XAddress end .
(* 4 *) Definition FLeXXchgArgs_get (f: FLeXXchgArgsFields )(r: FLeXXchgArgs ) :  FLeXXchgArgs_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) := r in 
 match f with 
 | FLeXXchgArgs_ι_sell => r1 
 | FLeXXchgArgs_ι_price_num => r2 
 | FLeXXchgArgs_ι_price_denum => r3 
 | FLeXXchgArgs_ι_amount => r4 
 | FLeXXchgArgs_ι_lend_amount => r5 
 | FLeXXchgArgs_ι_lend_finish_time => r6 
 | FLeXXchgArgs_ι_min_amount => r7 
 | FLeXXchgArgs_ι_deals_limit => r8 
 | FLeXXchgArgs_ι_tons_value => r9 
 | FLeXXchgArgs_ι_xchg_price_code => r10 
 | FLeXXchgArgs_ι_addrs => r11 
 | FLeXXchgArgs_ι_tip3_code => r12 
 | FLeXXchgArgs_ι_tip3cfgs => r13 
 end .
(* 5 *) Coercion FLeXXchgArgs_get : FLeXXchgArgsFields >-> Funclass .
(* 6 *) Definition FLeXXchgArgs_set (f: FLeXXchgArgsFields ) 
(v: FLeXXchgArgs_field_type f) (r: FLeXXchgArgs ): FLeXXchgArgs := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) := r in 
 match f, v with 
 | FLeXXchgArgs_ι_sell , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_price_num , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_price_denum , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_amount , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_lend_amount , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_lend_finish_time , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_min_amount , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_deals_limit , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_tons_value , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_xchg_price_code , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' , r11 , r12 , r13 ) 
 | FLeXXchgArgs_ι_addrs , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , v' , r12 , r13 ) 
 | FLeXXchgArgs_ι_tip3_code , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , v' , r13 ) 
 | FLeXXchgArgs_ι_tip3cfgs , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , v' ) 
 end .
(* 7 *) Global Instance FLeXXchgArgs_PruvendoRecord : PruvendoRecord FLeXXchgArgs FLeXXchgArgsFields :=
{
  field_type := FLeXXchgArgs_field_type; 
  getPruvendoRecord := @FLeXXchgArgs_get ;
  setPruvendoRecord := @FLeXXchgArgs_set ;
} .
(* 3 *) Definition FLeXCancelArgs_field_type f : Type :=  
match f with 
 | FLeXCancelArgs_ι_price => XInteger128 | FLeXCancelArgs_ι_min_amount => XInteger128 | FLeXCancelArgs_ι_deals_limit => XInteger8 | FLeXCancelArgs_ι_value => XInteger128 | FLeXCancelArgs_ι_price_code => TvmCell | FLeXCancelArgs_ι_tip3_code => TvmCell | FLeXCancelArgs_ι_tip3cfg => XAddress end .
(* 4 *) Definition FLeXCancelArgs_get (f: FLeXCancelArgsFields )(r: FLeXCancelArgs ) :  FLeXCancelArgs_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 ) := r in 
 match f with 
 | FLeXCancelArgs_ι_price => r1 
 | FLeXCancelArgs_ι_min_amount => r2 
 | FLeXCancelArgs_ι_deals_limit => r3 
 | FLeXCancelArgs_ι_value => r4 
 | FLeXCancelArgs_ι_price_code => r5 
 | FLeXCancelArgs_ι_tip3_code => r6 
 | FLeXCancelArgs_ι_tip3cfg => r7 
 end .
(* 5 *) Coercion FLeXCancelArgs_get : FLeXCancelArgsFields >-> Funclass .
(* 6 *) Definition FLeXCancelArgs_set (f: FLeXCancelArgsFields ) 
(v: FLeXCancelArgs_field_type f) (r: FLeXCancelArgs ): FLeXCancelArgs := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 ) := r in 
 match f, v with 
 | FLeXCancelArgs_ι_price , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 ) 
 | FLeXCancelArgs_ι_min_amount , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 ) 
 | FLeXCancelArgs_ι_deals_limit , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 ) 
 | FLeXCancelArgs_ι_value , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 ) 
 | FLeXCancelArgs_ι_price_code , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 ) 
 | FLeXCancelArgs_ι_tip3_code , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 ) 
 | FLeXCancelArgs_ι_tip3cfg , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' ) 
 end .
(* 7 *) Global Instance FLeXCancelArgs_PruvendoRecord : PruvendoRecord FLeXCancelArgs FLeXCancelArgsFields :=
{
  field_type := FLeXCancelArgs_field_type; 
  getPruvendoRecord := @FLeXCancelArgs_get ;
  setPruvendoRecord := @FLeXCancelArgs_set ;
} .
(* 3 *) Definition FLeXXchgCancelArgs_field_type f : Type :=  
match f with 
 | FLeXXchgCancelArgs_ι_sell => XBool | FLeXXchgCancelArgs_ι_price_num => XInteger128 | FLeXXchgCancelArgs_ι_price_denum => XInteger128 | FLeXXchgCancelArgs_ι_min_amount => XInteger128 | FLeXXchgCancelArgs_ι_deals_limit => XInteger8 | FLeXXchgCancelArgs_ι_value => XInteger128 | FLeXXchgCancelArgs_ι_xchg_price_code => TvmCell | FLeXXchgCancelArgs_ι_tip3_code => TvmCell | FLeXXchgCancelArgs_ι_tip3cfgs => XAddress end .
(* 4 *) Definition FLeXXchgCancelArgs_get (f: FLeXXchgCancelArgsFields )(r: FLeXXchgCancelArgs ) :  FLeXXchgCancelArgs_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 ) := r in 
 match f with 
 | FLeXXchgCancelArgs_ι_sell => r1 
 | FLeXXchgCancelArgs_ι_price_num => r2 
 | FLeXXchgCancelArgs_ι_price_denum => r3 
 | FLeXXchgCancelArgs_ι_min_amount => r4 
 | FLeXXchgCancelArgs_ι_deals_limit => r5 
 | FLeXXchgCancelArgs_ι_value => r6 
 | FLeXXchgCancelArgs_ι_xchg_price_code => r7 
 | FLeXXchgCancelArgs_ι_tip3_code => r8 
 | FLeXXchgCancelArgs_ι_tip3cfgs => r9 
 end .
(* 5 *) Coercion FLeXXchgCancelArgs_get : FLeXXchgCancelArgsFields >-> Funclass .
(* 6 *) Definition FLeXXchgCancelArgs_set (f: FLeXXchgCancelArgsFields ) 
(v: FLeXXchgCancelArgs_field_type f) (r: FLeXXchgCancelArgs ): FLeXXchgCancelArgs := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 ) := r in 
 match f, v with 
 | FLeXXchgCancelArgs_ι_sell , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 ) 
 | FLeXXchgCancelArgs_ι_price_num , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 ) 
 | FLeXXchgCancelArgs_ι_price_denum , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 ) 
 | FLeXXchgCancelArgs_ι_min_amount , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 ) 
 | FLeXXchgCancelArgs_ι_deals_limit , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 ) 
 | FLeXXchgCancelArgs_ι_value , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 ) 
 | FLeXXchgCancelArgs_ι_xchg_price_code , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 ) 
 | FLeXXchgCancelArgs_ι_tip3_code , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 ) 
 | FLeXXchgCancelArgs_ι_tip3cfgs , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' ) 
 end .
(* 7 *) Global Instance FLeXXchgCancelArgs_PruvendoRecord : PruvendoRecord FLeXXchgCancelArgs FLeXXchgCancelArgsFields :=
{
  field_type := FLeXXchgCancelArgs_field_type; 
  getPruvendoRecord := @FLeXXchgCancelArgs_get ;
  setPruvendoRecord := @FLeXXchgCancelArgs_set ;
} .
(* 3 *) Definition XchgPair_field_type f : Type :=  
match f with 
 | XchgPair_ι_flex_addr_ => XAddress | XchgPair_ι_tip3_major_root_ => XAddress | XchgPair_ι_tip3_minor_root_ => XAddress | XchgPair_ι_deploy_value_ => XInteger128 end .
(* 4 *) Definition XchgPair_get (f: XchgPairFields )(r: XchgPair ) :  XchgPair_field_type f := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f with 
 | XchgPair_ι_flex_addr_ => r1 
 | XchgPair_ι_tip3_major_root_ => r2 
 | XchgPair_ι_tip3_minor_root_ => r3 
 | XchgPair_ι_deploy_value_ => r4 
 end .
(* 5 *) Coercion XchgPair_get : XchgPairFields >-> Funclass .
(* 6 *) Definition XchgPair_set (f: XchgPairFields ) 
(v: XchgPair_field_type f) (r: XchgPair ): XchgPair := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f, v with 
 | XchgPair_ι_flex_addr_ , v' => ( v' , r2 , r3 , r4 ) 
 | XchgPair_ι_tip3_major_root_ , v' => ( r1 , v' , r3 , r4 ) 
 | XchgPair_ι_tip3_minor_root_ , v' => ( r1 , r2 , v' , r4 ) 
 | XchgPair_ι_deploy_value_ , v' => ( r1 , r2 , r3 , v' ) 
 end .
(* 7 *) Global Instance XchgPair_PruvendoRecord : PruvendoRecord XchgPair XchgPairFields :=
{
  field_type := XchgPair_field_type; 
  getPruvendoRecord := @XchgPair_get ;
  setPruvendoRecord := @XchgPair_set ;
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
 | Price_ι_price_ => XInteger128 | Price_ι_sells_amount_ => XInteger128 | Price_ι_buys_amount_ => XInteger128 | Price_ι_flex_ => addr_std_fixed | Price_ι_min_amount_ => XInteger128 | Price_ι_deals_limit_ => XInteger8 | Price_ι_notify_addr_ => IFLeXNotifyPtr | Price_ι_workchain_id_ => XInteger8 | Price_ι_tons_cfg_ => TonsConfig | Price_ι_tip3_code_ => TvmCell | Price_ι_tip3cfg_ => Tip3Config | Price_ι_sells_ => XList OrderInfo | Price_ι_buys_ => XList OrderInfo end .
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
(* 3 *) Definition RationalPrice_field_type f : Type :=  
match f with 
 | RationalPrice_ι_num => XInteger128 | RationalPrice_ι_denum => XInteger128 end .
(* 4 *) Definition RationalPrice_get (f: RationalPriceFields )(r: RationalPrice ) :  RationalPrice_field_type f := 
 let '( r1 , r2 ) := r in 
 match f with 
 | RationalPrice_ι_num => r1 
 | RationalPrice_ι_denum => r2 
 end .
(* 5 *) Coercion RationalPrice_get : RationalPriceFields >-> Funclass .
(* 6 *) Definition RationalPrice_set (f: RationalPriceFields ) 
(v: RationalPrice_field_type f) (r: RationalPrice ): RationalPrice := 
 let '( r1 , r2 ) := r in 
 match f, v with 
 | RationalPrice_ι_num , v' => ( v' , r2 ) 
 | RationalPrice_ι_denum , v' => ( r1 , v' ) 
 end .
(* 7 *) Global Instance RationalPrice_PruvendoRecord : PruvendoRecord RationalPrice RationalPriceFields :=
{
  field_type := RationalPrice_field_type; 
  getPruvendoRecord := @RationalPrice_get ;
  setPruvendoRecord := @RationalPrice_set ;
} .
(* 3 *) Definition PriceXchg_field_type f : Type :=  
match f with 
 | PriceXchg_ι_price_ => RationalPrice | PriceXchg_ι_sells_amount_ => XInteger128 | PriceXchg_ι_buys_amount_ => XInteger128 | PriceXchg_ι_flex_ => addr_std_fixed | PriceXchg_ι_min_amount_ => XInteger128 | PriceXchg_ι_deals_limit_ => XInteger8 | PriceXchg_ι_notify_addr_ => IFLeXNotifyPtr | PriceXchg_ι_workchain_id_ => XInteger8 | PriceXchg_ι_tons_cfg_ => TonsConfig | PriceXchg_ι_tip3_code_ => TvmCell | PriceXchg_ι_major_tip3cfg_ => Tip3Config | PriceXchg_ι_minor_tip3cfg_ => Tip3Config end .
(* 4 *) Definition PriceXchg_get (f: PriceXchgFields )(r: PriceXchg ) :  PriceXchg_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) := r in 
 match f with 
 | PriceXchg_ι_price_ => r1 
 | PriceXchg_ι_sells_amount_ => r2 
 | PriceXchg_ι_buys_amount_ => r3 
 | PriceXchg_ι_flex_ => r4 
 | PriceXchg_ι_min_amount_ => r5 
 | PriceXchg_ι_deals_limit_ => r6 
 | PriceXchg_ι_notify_addr_ => r7 
 | PriceXchg_ι_workchain_id_ => r8 
 | PriceXchg_ι_tons_cfg_ => r9 
 | PriceXchg_ι_tip3_code_ => r10 
 | PriceXchg_ι_major_tip3cfg_ => r11 
 | PriceXchg_ι_minor_tip3cfg_ => r12 
 end .
(* 5 *) Coercion PriceXchg_get : PriceXchgFields >-> Funclass .
(* 6 *) Definition PriceXchg_set (f: PriceXchgFields ) 
(v: PriceXchg_field_type f) (r: PriceXchg ): PriceXchg := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) := r in 
 match f, v with 
 | PriceXchg_ι_price_ , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | PriceXchg_ι_sells_amount_ , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | PriceXchg_ι_buys_amount_ , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | PriceXchg_ι_flex_ , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | PriceXchg_ι_min_amount_ , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | PriceXchg_ι_deals_limit_ , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 , r11 , r12 ) 
 | PriceXchg_ι_notify_addr_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 , r11 , r12 ) 
 | PriceXchg_ι_workchain_id_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 , r11 , r12 ) 
 | PriceXchg_ι_tons_cfg_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 , r11 , r12 ) 
 | PriceXchg_ι_tip3_code_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' , r11 , r12 ) 
 | PriceXchg_ι_major_tip3cfg_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , v' , r12 ) 
 | PriceXchg_ι_minor_tip3cfg_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , v' ) 
 end .
(* 7 *) Global Instance PriceXchg_PruvendoRecord : PruvendoRecord PriceXchg PriceXchgFields :=
{
  field_type := PriceXchg_field_type; 
  getPruvendoRecord := @PriceXchg_get ;
  setPruvendoRecord := @PriceXchg_set ;
} .
(* 3 *) Definition TradingPair_field_type f : Type :=  
match f with 
 | TradingPair_ι_flex_addr_ => XAddress | TradingPair_ι_tip3_root_ => XAddress | TradingPair_ι_deploy_value_ => XInteger128 end .
(* 4 *) Definition TradingPair_get (f: TradingPairFields )(r: TradingPair ) :  TradingPair_field_type f := 
 let '( r1 , r2 , r3 ) := r in 
 match f with 
 | TradingPair_ι_flex_addr_ => r1 
 | TradingPair_ι_tip3_root_ => r2 
 | TradingPair_ι_deploy_value_ => r3 
 end .
(* 5 *) Coercion TradingPair_get : TradingPairFields >-> Funclass .
(* 6 *) Definition TradingPair_set (f: TradingPairFields ) 
(v: TradingPair_field_type f) (r: TradingPair ): TradingPair := 
 let '( r1 , r2 , r3 ) := r in 
 match f, v with 
 | TradingPair_ι_flex_addr_ , v' => ( v' , r2 , r3 ) 
 | TradingPair_ι_tip3_root_ , v' => ( r1 , v' , r3 ) 
 | TradingPair_ι_deploy_value_ , v' => ( r1 , r2 , v' ) 
 end .
(* 7 *) Global Instance TradingPair_PruvendoRecord : PruvendoRecord TradingPair TradingPairFields :=
{
  field_type := TradingPair_field_type; 
  getPruvendoRecord := @TradingPair_get ;
  setPruvendoRecord := @TradingPair_set ;
} .
(* 3 *) Definition PayloadArgs_field_type f : Type :=  
match f with 
 | PayloadArgs_ι_sell => XBool | PayloadArgs_ι_amount => XInteger128 | PayloadArgs_ι_receive_tip3_wallet => XAddress | PayloadArgs_ι_client_addr => XAddress end .
(* 4 *) Definition PayloadArgs_get (f: PayloadArgsFields )(r: PayloadArgs ) :  PayloadArgs_field_type f := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f with 
 | PayloadArgs_ι_sell => r1 
 | PayloadArgs_ι_amount => r2 
 | PayloadArgs_ι_receive_tip3_wallet => r3 
 | PayloadArgs_ι_client_addr => r4 
 end .
(* 5 *) Coercion PayloadArgs_get : PayloadArgsFields >-> Funclass .
(* 6 *) Definition PayloadArgs_set (f: PayloadArgsFields ) 
(v: PayloadArgs_field_type f) (r: PayloadArgs ): PayloadArgs := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f, v with 
 | PayloadArgs_ι_sell , v' => ( v' , r2 , r3 , r4 ) 
 | PayloadArgs_ι_amount , v' => ( r1 , v' , r3 , r4 ) 
 | PayloadArgs_ι_receive_tip3_wallet , v' => ( r1 , r2 , v' , r4 ) 
 | PayloadArgs_ι_client_addr , v' => ( r1 , r2 , r3 , v' ) 
 end .
(* 7 *) Global Instance PayloadArgs_PruvendoRecord : PruvendoRecord PayloadArgs PayloadArgsFields :=
{
  field_type := PayloadArgs_field_type; 
  getPruvendoRecord := @PayloadArgs_get ;
  setPruvendoRecord := @PayloadArgs_set ;
} .
(* 3 *) Definition LocalState_field_type f : Type :=  
match f with 
 | LocalState_ι_uint256 => XHMap (string*nat) XInteger256 | LocalState_ι_cell => XHMap (string*nat) TvmCell | LocalState_ι_TonsConfig => XHMap (string*nat) TonsConfig | LocalState_ι_address => XHMap (string*nat) XAddress | LocalState_ι_uint128 => XHMap (string*nat) XInteger128 | LocalState_ι_TradingPair => XHMap (string*nat) TradingPair | LocalState_ι_tplStateInituint256 => XHMap (string*nat) ( StateInit * XInteger256 ) | LocalState_ι_StateInit => XHMap (string*nat) StateInit | LocalState_ι_XchgPair => XHMap (string*nat) XchgPair | LocalState_ι_tplStateInitaddress => XHMap (string*nat) ( StateInit * XAddress * XInteger256 ) | LocalState_ι_SellArgs => XHMap (string*nat) SellArgs | LocalState_ι_ITONTokenWalletPtr => XHMap (string*nat) ITONTokenWalletPtr | LocalState_ι_IPricePtr => XHMap (string*nat) IPricePtr | LocalState_ι_int => XHMap (string*nat) XInteger | LocalState_ι_Price => XHMap (string*nat) Price | LocalState_ι_uint8 => XHMap (string*nat) XInteger8 | LocalState_ι_uint32 => XHMap (string*nat) XInteger32 | LocalState_ι_Tip3Config => XHMap (string*nat) Tip3Config | LocalState_ι_PriceXchg => XHMap (string*nat) PriceXchg | LocalState_ι_PayloadArgs => XHMap (string*nat) PayloadArgs | LocalState_ι_uint256Index => XHMap string nat | LocalState_ι_cellIndex => XHMap string nat | LocalState_ι_TonsConfigIndex => XHMap string nat | LocalState_ι_addressIndex => XHMap string nat | LocalState_ι_uint128Index => XHMap string nat | LocalState_ι_TradingPairIndex => XHMap string nat | LocalState_ι_tplStateInituint256Index => XHMap string nat | LocalState_ι_StateInitIndex => XHMap string nat | LocalState_ι_XchgPairIndex => XHMap string nat | LocalState_ι_tplStateInitaddressIndex => XHMap string nat | LocalState_ι_SellArgsIndex => XHMap string nat | LocalState_ι_ITONTokenWalletPtrIndex => XHMap string nat | LocalState_ι_IPricePtrIndex => XHMap string nat | LocalState_ι_intIndex => XHMap string nat | LocalState_ι_PriceIndex => XHMap string nat | LocalState_ι_uint8Index => XHMap string nat | LocalState_ι_uint32Index => XHMap string nat | LocalState_ι_Tip3ConfigIndex => XHMap string nat | LocalState_ι_PriceXchgIndex => XHMap string nat | LocalState_ι_PayloadArgsIndex => XHMap string nat end .
(* 4 *) Definition LocalState_get (f: LocalStateFields )(r: LocalState ) :  LocalState_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) := r in 
 match f with 
 | LocalState_ι_uint256 => r1 
 | LocalState_ι_cell => r2 
 | LocalState_ι_TonsConfig => r3 
 | LocalState_ι_address => r4 
 | LocalState_ι_uint128 => r5 
 | LocalState_ι_TradingPair => r6 
 | LocalState_ι_tplStateInituint256 => r7 
 | LocalState_ι_StateInit => r8 
 | LocalState_ι_XchgPair => r9 
 | LocalState_ι_tplStateInitaddress => r10 
 | LocalState_ι_SellArgs => r11 
 | LocalState_ι_ITONTokenWalletPtr => r12 
 | LocalState_ι_IPricePtr => r13 
 | LocalState_ι_int => r14 
 | LocalState_ι_Price => r15 
 | LocalState_ι_uint8 => r16 
 | LocalState_ι_uint32 => r17 
 | LocalState_ι_Tip3Config => r18 
 | LocalState_ι_PriceXchg => r19 
 | LocalState_ι_PayloadArgs => r20 
 | LocalState_ι_uint256Index => r21 
 | LocalState_ι_cellIndex => r22 
 | LocalState_ι_TonsConfigIndex => r23 
 | LocalState_ι_addressIndex => r24 
 | LocalState_ι_uint128Index => r25 
 | LocalState_ι_TradingPairIndex => r26 
 | LocalState_ι_tplStateInituint256Index => r27 
 | LocalState_ι_StateInitIndex => r28 
 | LocalState_ι_XchgPairIndex => r29 
 | LocalState_ι_tplStateInitaddressIndex => r30 
 | LocalState_ι_SellArgsIndex => r31 
 | LocalState_ι_ITONTokenWalletPtrIndex => r32 
 | LocalState_ι_IPricePtrIndex => r33 
 | LocalState_ι_intIndex => r34 
 | LocalState_ι_PriceIndex => r35 
 | LocalState_ι_uint8Index => r36 
 | LocalState_ι_uint32Index => r37 
 | LocalState_ι_Tip3ConfigIndex => r38 
 | LocalState_ι_PriceXchgIndex => r39 
 | LocalState_ι_PayloadArgsIndex => r40 
 end .
(* 5 *) Coercion LocalState_get : LocalStateFields >-> Funclass .
(* 6 *) Definition LocalState_set (f: LocalStateFields ) 
(v: LocalState_field_type f) (r: LocalState ): LocalState := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) := r in 
 match f, v with 
 | LocalState_ι_uint256 , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_cell , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_TonsConfig , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_address , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_uint128 , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_TradingPair , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_tplStateInituint256 , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_StateInit , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_XchgPair , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_tplStateInitaddress , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_SellArgs , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , v' , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_ITONTokenWalletPtr , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , v' , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_IPricePtr , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , v' , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_int , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , v' , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_Price , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , v' , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_uint8 , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , v' , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_uint32 , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , v' , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_Tip3Config , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , v' , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_PriceXchg , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , v' , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_PayloadArgs , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , v' , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_uint256Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , v' , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_cellIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , v' , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_TonsConfigIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , v' , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_addressIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , v' , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_uint128Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , v' , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_TradingPairIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , v' , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_tplStateInituint256Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , v' , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_StateInitIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , v' , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_XchgPairIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , v' , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_tplStateInitaddressIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , v' , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_SellArgsIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , v' , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_ITONTokenWalletPtrIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , v' , r33 , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_IPricePtrIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , v' , r34 , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_intIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , v' , r35 , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_PriceIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , v' , r36 , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_uint8Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , v' , r37 , r38 , r39 , r40 ) 
 | LocalState_ι_uint32Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , v' , r38 , r39 , r40 ) 
 | LocalState_ι_Tip3ConfigIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , v' , r39 , r40 ) 
 | LocalState_ι_PriceXchgIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , v' , r40 ) 
 | LocalState_ι_PayloadArgsIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 , r23 , r24 , r25 , r26 , r27 , r28 , r29 , r30 , r31 , r32 , r33 , r34 , r35 , r36 , r37 , r38 , r39 , v' ) 
 end .
(* 7 *) Global Instance LocalState_PruvendoRecord : PruvendoRecord LocalState LocalStateFields :=
{
  field_type := LocalState_field_type; 
  getPruvendoRecord := @LocalState_get ;
  setPruvendoRecord := @LocalState_set ;
} .
(* 3 *) Definition Ledger_field_type f : Type :=  
match f with 
 | Ledger_ι_FLeXClient => FLeXClient | Ledger_ι_VMState => VMState | Ledger_ι_LocalState => LocalState | Ledger_ι_LocalStateCopy => LocalState end .
(* 4 *) Definition Ledger_get (f: LedgerFields )(r: Ledger ) :  Ledger_field_type f := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f with 
 | Ledger_ι_FLeXClient => r1 
 | Ledger_ι_VMState => r2 
 | Ledger_ι_LocalState => r3 
 | Ledger_ι_LocalStateCopy => r4 
 end .
(* 5 *) Coercion Ledger_get : LedgerFields >-> Funclass .
(* 6 *) Definition Ledger_set (f: LedgerFields ) 
(v: Ledger_field_type f) (r: Ledger ): Ledger := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f, v with 
 | Ledger_ι_FLeXClient , v' => ( v' , r2 , r3 , r4 ) 
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
Definition T1 := FLeXClient .
Definition T2 := VMState .
Definition T3 := LocalState .
Definition T4 := LocalState .

 
 Definition projEmbed_T1 : Ledger -> T1 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_FLeXClient. 
 Definition injEmbed_T1 : T1 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_FLeXClient. 
 
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
 (* 
 Instance FullState_T1xT2xT3_T4 : 
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
Global Instance iso_T1 : IsoTypes T1 (field_type (R:=Ledger) Ledger_ι_FLeXClient) :=
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

Opaque FLeXClient.

Lemma Ledger1Type_eq: forall (l: Ledger), projT1 (rth 0 l) = FLeXClient.
Proof.
   intros.
   compute.
   destruct l.
   repeat destruct p.
   reflexivity.  
Defined.

Definition Ledger1Type (l: Ledger) := projT1 (rth 0 l).

Definition Ledger1TypeFLeXClient : forall (l:Ledger), Ledger1Type l -> FLeXClient.
intros.
unfold Ledger1Type in X.
rewrite Ledger1Type_eq in X.
exact X.
Defined.

Coercion Ledger1TypeFLeXClient       : Ledger1Type >-> FLeXClient.

Notation "r ₁" := ((projT2 (rth 0 r) : Ledger1Type r) : FLeXClient) (at level 10).

Transparent FLeXClient.

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
Definition  LocalState_ι_uint256Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_uint256Index l.

Definition  LocalState_ι_uint256Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_uint256Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_uint256Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_uint256Index_Embedded_projEmbed (LocalState_ι_uint256Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_uint256Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_uint256Index_Embedded_injEmbed (LocalState_ι_uint256Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_uint256Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_uint256Index_Embedded_injEmbed t1 (LocalState_ι_uint256Index_Embedded_injEmbed t2 s) = LocalState_ι_uint256Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_uint256Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_uint256Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_uint256Index_Embedded_injEmbed;
  projinj := LocalState_ι_uint256Index_Embedded_projinj;
  injproj := LocalState_ι_uint256Index_Embedded_injproj;
  injinj := LocalState_ι_uint256Index_Embedded_injinj
}.
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
Definition  LocalState_ι_TradingPairIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_TradingPairIndex l.

Definition  LocalState_ι_TradingPairIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_TradingPairIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_TradingPairIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_TradingPairIndex_Embedded_projEmbed (LocalState_ι_TradingPairIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_TradingPairIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_TradingPairIndex_Embedded_injEmbed (LocalState_ι_TradingPairIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_TradingPairIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_TradingPairIndex_Embedded_injEmbed t1 (LocalState_ι_TradingPairIndex_Embedded_injEmbed t2 s) = LocalState_ι_TradingPairIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_TradingPairIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_TradingPairIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_TradingPairIndex_Embedded_injEmbed;
  projinj := LocalState_ι_TradingPairIndex_Embedded_projinj;
  injproj := LocalState_ι_TradingPairIndex_Embedded_injproj;
  injinj := LocalState_ι_TradingPairIndex_Embedded_injinj
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
Definition  LocalState_ι_XchgPairIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_XchgPairIndex l.

Definition  LocalState_ι_XchgPairIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_XchgPairIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_XchgPairIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_XchgPairIndex_Embedded_projEmbed (LocalState_ι_XchgPairIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_XchgPairIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_XchgPairIndex_Embedded_injEmbed (LocalState_ι_XchgPairIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_XchgPairIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_XchgPairIndex_Embedded_injEmbed t1 (LocalState_ι_XchgPairIndex_Embedded_injEmbed t2 s) = LocalState_ι_XchgPairIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_XchgPairIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_XchgPairIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_XchgPairIndex_Embedded_injEmbed;
  projinj := LocalState_ι_XchgPairIndex_Embedded_projinj;
  injproj := LocalState_ι_XchgPairIndex_Embedded_injproj;
  injinj := LocalState_ι_XchgPairIndex_Embedded_injinj
}.
Definition  LocalState_ι_tplStateInitaddressIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_tplStateInitaddressIndex l.

Definition  LocalState_ι_tplStateInitaddressIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_tplStateInitaddressIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_tplStateInitaddressIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_tplStateInitaddressIndex_Embedded_projEmbed (LocalState_ι_tplStateInitaddressIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_tplStateInitaddressIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_tplStateInitaddressIndex_Embedded_injEmbed (LocalState_ι_tplStateInitaddressIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_tplStateInitaddressIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_tplStateInitaddressIndex_Embedded_injEmbed t1 (LocalState_ι_tplStateInitaddressIndex_Embedded_injEmbed t2 s) = LocalState_ι_tplStateInitaddressIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_tplStateInitaddressIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_tplStateInitaddressIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_tplStateInitaddressIndex_Embedded_injEmbed;
  projinj := LocalState_ι_tplStateInitaddressIndex_Embedded_projinj;
  injproj := LocalState_ι_tplStateInitaddressIndex_Embedded_injproj;
  injinj := LocalState_ι_tplStateInitaddressIndex_Embedded_injinj
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
Definition  LocalState_ι_ITONTokenWalletPtrIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_ITONTokenWalletPtrIndex l.

Definition  LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_ITONTokenWalletPtrIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_ITONTokenWalletPtrIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_ITONTokenWalletPtrIndex_Embedded_projEmbed (LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injEmbed (LocalState_ι_ITONTokenWalletPtrIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injEmbed t1 (LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injEmbed t2 s) = LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_ITONTokenWalletPtrIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_ITONTokenWalletPtrIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injEmbed;
  projinj := LocalState_ι_ITONTokenWalletPtrIndex_Embedded_projinj;
  injproj := LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injproj;
  injinj := LocalState_ι_ITONTokenWalletPtrIndex_Embedded_injinj
}.
Definition  LocalState_ι_IPricePtrIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_IPricePtrIndex l.

Definition  LocalState_ι_IPricePtrIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_IPricePtrIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_IPricePtrIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_IPricePtrIndex_Embedded_projEmbed (LocalState_ι_IPricePtrIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_IPricePtrIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_IPricePtrIndex_Embedded_injEmbed (LocalState_ι_IPricePtrIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_IPricePtrIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_IPricePtrIndex_Embedded_injEmbed t1 (LocalState_ι_IPricePtrIndex_Embedded_injEmbed t2 s) = LocalState_ι_IPricePtrIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_IPricePtrIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_IPricePtrIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_IPricePtrIndex_Embedded_injEmbed;
  projinj := LocalState_ι_IPricePtrIndex_Embedded_projinj;
  injproj := LocalState_ι_IPricePtrIndex_Embedded_injproj;
  injinj := LocalState_ι_IPricePtrIndex_Embedded_injinj
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
Definition  LocalState_ι_Tip3ConfigIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_Tip3ConfigIndex l.

Definition  LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_Tip3ConfigIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_Tip3ConfigIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_Tip3ConfigIndex_Embedded_projEmbed (LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_Tip3ConfigIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed (LocalState_ι_Tip3ConfigIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_Tip3ConfigIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed t1 (LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed t2 s) = LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_Tip3ConfigIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_Tip3ConfigIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed;
  projinj := LocalState_ι_Tip3ConfigIndex_Embedded_projinj;
  injproj := LocalState_ι_Tip3ConfigIndex_Embedded_injproj;
  injinj := LocalState_ι_Tip3ConfigIndex_Embedded_injinj
}.
Definition  LocalState_ι_PriceXchgIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_PriceXchgIndex l.

Definition  LocalState_ι_PriceXchgIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_PriceXchgIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_PriceXchgIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_PriceXchgIndex_Embedded_projEmbed (LocalState_ι_PriceXchgIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_PriceXchgIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_PriceXchgIndex_Embedded_injEmbed (LocalState_ι_PriceXchgIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_PriceXchgIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_PriceXchgIndex_Embedded_injEmbed t1 (LocalState_ι_PriceXchgIndex_Embedded_injEmbed t2 s) = LocalState_ι_PriceXchgIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_PriceXchgIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_PriceXchgIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_PriceXchgIndex_Embedded_injEmbed;
  projinj := LocalState_ι_PriceXchgIndex_Embedded_projinj;
  injproj := LocalState_ι_PriceXchgIndex_Embedded_injproj;
  injinj := LocalState_ι_PriceXchgIndex_Embedded_injinj
}.
Definition  LocalState_ι_PayloadArgsIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_PayloadArgsIndex l.

Definition  LocalState_ι_PayloadArgsIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_PayloadArgsIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_PayloadArgsIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_PayloadArgsIndex_Embedded_projEmbed (LocalState_ι_PayloadArgsIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_PayloadArgsIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_PayloadArgsIndex_Embedded_injEmbed (LocalState_ι_PayloadArgsIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_PayloadArgsIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_PayloadArgsIndex_Embedded_injEmbed t1 (LocalState_ι_PayloadArgsIndex_Embedded_injEmbed t2 s) = LocalState_ι_PayloadArgsIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_PayloadArgsIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_PayloadArgsIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_PayloadArgsIndex_Embedded_injEmbed;
  projinj := LocalState_ι_PayloadArgsIndex_Embedded_projinj;
  injproj := LocalState_ι_PayloadArgsIndex_Embedded_injproj;
  injinj := LocalState_ι_PayloadArgsIndex_Embedded_injinj
}.
(****************************************************************************)

Global Instance LocalState_uint256Index: LocalStateField XInteger256 :=
{
  local_index_embedded := LocalState_ι_uint256Index_Embedded;
  local_state_field := LocalState_ι_uint256; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_cellIndex: LocalStateField TvmCell :=
{
  local_index_embedded := LocalState_ι_cellIndex_Embedded;
  local_state_field := LocalState_ι_cell; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_TonsConfigIndex: LocalStateField TonsConfig :=
{
  local_index_embedded := LocalState_ι_TonsConfigIndex_Embedded;
  local_state_field := LocalState_ι_TonsConfig; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_addressIndex: LocalStateField XAddress :=
{
  local_index_embedded := LocalState_ι_addressIndex_Embedded;
  local_state_field := LocalState_ι_address; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_uint128Index: LocalStateField XInteger128 :=
{
  local_index_embedded := LocalState_ι_uint128Index_Embedded;
  local_state_field := LocalState_ι_uint128; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_TradingPairIndex: LocalStateField TradingPair :=
{
  local_index_embedded := LocalState_ι_TradingPairIndex_Embedded;
  local_state_field := LocalState_ι_TradingPair; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_tplStateInituint256Index: LocalStateField ( StateInit * XInteger256 ) :=
{
  local_index_embedded := LocalState_ι_tplStateInituint256Index_Embedded;
  local_state_field := LocalState_ι_tplStateInituint256; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_StateInitIndex: LocalStateField StateInit :=
{
  local_index_embedded := LocalState_ι_StateInitIndex_Embedded;
  local_state_field := LocalState_ι_StateInit; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_XchgPairIndex: LocalStateField XchgPair :=
{
  local_index_embedded := LocalState_ι_XchgPairIndex_Embedded;
  local_state_field := LocalState_ι_XchgPair; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_tplStateInitaddressIndex: LocalStateField ( StateInit * XAddress * XInteger256 ) :=
{
  local_index_embedded := LocalState_ι_tplStateInitaddressIndex_Embedded;
  local_state_field := LocalState_ι_tplStateInitaddress; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_SellArgsIndex: LocalStateField SellArgs :=
{
  local_index_embedded := LocalState_ι_SellArgsIndex_Embedded;
  local_state_field := LocalState_ι_SellArgs; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ITONTokenWalletPtrIndex: LocalStateField ITONTokenWalletPtr :=
{
  local_index_embedded := LocalState_ι_ITONTokenWalletPtrIndex_Embedded;
  local_state_field := LocalState_ι_ITONTokenWalletPtr; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_IPricePtrIndex: LocalStateField IPricePtr :=
{
  local_index_embedded := LocalState_ι_IPricePtrIndex_Embedded;
  local_state_field := LocalState_ι_IPricePtr; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_intIndex: LocalStateField XInteger :=
{
  local_index_embedded := LocalState_ι_intIndex_Embedded;
  local_state_field := LocalState_ι_int; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_PriceIndex: LocalStateField Price :=
{
  local_index_embedded := LocalState_ι_PriceIndex_Embedded;
  local_state_field := LocalState_ι_Price; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_uint8Index: LocalStateField XInteger8 :=
{
  local_index_embedded := LocalState_ι_uint8Index_Embedded;
  local_state_field := LocalState_ι_uint8; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_uint32Index: LocalStateField XInteger32 :=
{
  local_index_embedded := LocalState_ι_uint32Index_Embedded;
  local_state_field := LocalState_ι_uint32; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_Tip3ConfigIndex: LocalStateField Tip3Config :=
{
  local_index_embedded := LocalState_ι_Tip3ConfigIndex_Embedded;
  local_state_field := LocalState_ι_Tip3Config; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_PriceXchgIndex: LocalStateField PriceXchg :=
{
  local_index_embedded := LocalState_ι_PriceXchgIndex_Embedded;
  local_state_field := LocalState_ι_PriceXchg; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_PayloadArgsIndex: LocalStateField PayloadArgs :=
{
  local_index_embedded := LocalState_ι_PayloadArgsIndex_Embedded;
  local_state_field := LocalState_ι_PayloadArgs; 
  local_field_type_correct := eq_refl
}.

 

Definition LedgerVMStateEmbedded := embeddedT2. 
Definition LedgerVMStateField := Ledger_ι_VMState .
Definition isoVMState := iso_T2.

End LedgerClass .
