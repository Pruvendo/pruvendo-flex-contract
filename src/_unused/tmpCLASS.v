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


Module Export SolidityNotationsClass := SolidityNotations xt  sm.
Module Export VMStateModule := VMStateModule xt  sm.

Import xt. 
Existing Instance monadStateT. 
Existing Instance monadStateStateT.


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
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 2 *) Definition TonsConfig := 
 ( XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 * 
 XInteger128 )%type .
(* 1 *) Inductive FLeXFields := | FLeX_ι_deployer_pubkey_ | FLeX_ι_tons_cfg_ | FLeX_ι_pair_code_ | FLeX_ι_xchg_pair_code_ | FLeX_ι_price_code_ | FLeX_ι_xchg_price_code_ | FLeX_ι_min_amount_ | FLeX_ι_deals_limit_ | FLeX_ι_notify_addr_ .
(* 2 *) Definition FLeX := 
 ( XInteger256 * 
 TonsConfig * 
 XMaybe TvmCell * 
 XMaybe TvmCell * 
 XMaybe TvmCell * 
 XMaybe TvmCell * 
 XInteger128 * 
 XInteger8 * 
 XAddress )%type .
(* 1 *) Inductive TradingPairFields := | TradingPair_ι_flex_addr_ | TradingPair_ι_tip3_root_ | TradingPair_ι_deploy_value_ .
(* 2 *) Definition TradingPair := 
 ( XAddress * 
 XAddress * 
 XInteger128 )%type .
(* 1 *) Inductive XchgPairFields := | XchgPair_ι_flex_addr_ | XchgPair_ι_tip3_major_root_ | XchgPair_ι_tip3_minor_root_ | XchgPair_ι_deploy_value_ .
(* 2 *) Definition XchgPair := 
 ( XAddress * 
 XAddress * 
 XAddress * 
 XInteger128 )%type .
(* 1 *) Inductive LocalStateFields := | LocalState_ι_int | LocalState_ι_optcell | LocalState_ι_tpladdressaddress | LocalState_ι_uint256 | LocalState_ι_uint128 | LocalState_ι_uint8 | LocalState_ι_address | LocalState_ι_cell | LocalState_ι_XchgPair | LocalState_ι_bool | LocalState_ι_TradingPair | LocalState_ι_intIndex | LocalState_ι_optcellIndex | LocalState_ι_tpladdressaddressIndex | LocalState_ι_uint256Index | LocalState_ι_uint128Index | LocalState_ι_uint8Index | LocalState_ι_addressIndex | LocalState_ι_cellIndex | LocalState_ι_XchgPairIndex | LocalState_ι_boolIndex | LocalState_ι_TradingPairIndex .
(* 2 *) Definition LocalState := 
 ( XHMap (string*nat) XInteger * 
 XHMap (string*nat) ( XMaybe TvmCell ) * 
 XHMap (string*nat) ( XAddress * XAddress ) * 
 XHMap (string*nat) XInteger256 * 
 XHMap (string*nat) XInteger128 * 
 XHMap (string*nat) XInteger8 * 
 XHMap (string*nat) XAddress * 
 XHMap (string*nat) TvmCell * 
 XHMap (string*nat) XchgPair * 
 XHMap (string*nat) XBool * 
 XHMap (string*nat) TradingPair * 
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
(* 1 *) Inductive LedgerFieldsI := | Ledger_ι_FLeX | Ledger_ι_VMState | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .
(* 2 *) Definition Ledger := 
 ( FLeX * 
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
(* 3 *) Definition FLeX_field_type f : Type :=  
match f with 
 | FLeX_ι_deployer_pubkey_ => XInteger256 | FLeX_ι_tons_cfg_ => TonsConfig | FLeX_ι_pair_code_ => XMaybe TvmCell | FLeX_ι_xchg_pair_code_ => XMaybe TvmCell | FLeX_ι_price_code_ => XMaybe TvmCell | FLeX_ι_xchg_price_code_ => XMaybe TvmCell | FLeX_ι_min_amount_ => XInteger128 | FLeX_ι_deals_limit_ => XInteger8 | FLeX_ι_notify_addr_ => XAddress end .
(* 4 *) Definition FLeX_get (f: FLeXFields )(r: FLeX ) :  FLeX_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 ) := r in 
 match f with 
 | FLeX_ι_deployer_pubkey_ => r1 
 | FLeX_ι_tons_cfg_ => r2 
 | FLeX_ι_pair_code_ => r3 
 | FLeX_ι_xchg_pair_code_ => r4 
 | FLeX_ι_price_code_ => r5 
 | FLeX_ι_xchg_price_code_ => r6 
 | FLeX_ι_min_amount_ => r7 
 | FLeX_ι_deals_limit_ => r8 
 | FLeX_ι_notify_addr_ => r9 
 end .
(* 5 *) Coercion FLeX_get : FLeXFields >-> Funclass .
(* 6 *) Definition FLeX_set (f: FLeXFields ) 
(v: FLeX_field_type f) (r: FLeX ): FLeX := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 ) := r in 
 match f, v with 
 | FLeX_ι_deployer_pubkey_ , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 ) 
 | FLeX_ι_tons_cfg_ , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 ) 
 | FLeX_ι_pair_code_ , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 ) 
 | FLeX_ι_xchg_pair_code_ , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 ) 
 | FLeX_ι_price_code_ , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 ) 
 | FLeX_ι_xchg_price_code_ , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 ) 
 | FLeX_ι_min_amount_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 ) 
 | FLeX_ι_deals_limit_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 ) 
 | FLeX_ι_notify_addr_ , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' ) 
 end .
(* 7 *) Global Instance FLeX_PruvendoRecord : PruvendoRecord FLeX FLeXFields :=
{
  field_type := FLeX_field_type; 
  getPruvendoRecord := @FLeX_get ;
  setPruvendoRecord := @FLeX_set ;
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
(* 3 *) Definition LocalState_field_type f : Type :=  
match f with 
 | LocalState_ι_int => XHMap (string*nat) XInteger | LocalState_ι_optcell => XHMap (string*nat) ( XMaybe TvmCell ) | LocalState_ι_tpladdressaddress => XHMap (string*nat) ( XAddress * XAddress ) | LocalState_ι_uint256 => XHMap (string*nat) XInteger256 | LocalState_ι_uint128 => XHMap (string*nat) XInteger128 | LocalState_ι_uint8 => XHMap (string*nat) XInteger8 | LocalState_ι_address => XHMap (string*nat) XAddress | LocalState_ι_cell => XHMap (string*nat) TvmCell | LocalState_ι_XchgPair => XHMap (string*nat) XchgPair | LocalState_ι_bool => XHMap (string*nat) XBool | LocalState_ι_TradingPair => XHMap (string*nat) TradingPair | LocalState_ι_intIndex => XHMap string nat | LocalState_ι_optcellIndex => XHMap string nat | LocalState_ι_tpladdressaddressIndex => XHMap string nat | LocalState_ι_uint256Index => XHMap string nat | LocalState_ι_uint128Index => XHMap string nat | LocalState_ι_uint8Index => XHMap string nat | LocalState_ι_addressIndex => XHMap string nat | LocalState_ι_cellIndex => XHMap string nat | LocalState_ι_XchgPairIndex => XHMap string nat | LocalState_ι_boolIndex => XHMap string nat | LocalState_ι_TradingPairIndex => XHMap string nat end .
(* 4 *) Definition LocalState_get (f: LocalStateFields )(r: LocalState ) :  LocalState_field_type f := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) := r in 
 match f with 
 | LocalState_ι_int => r1 
 | LocalState_ι_optcell => r2 
 | LocalState_ι_tpladdressaddress => r3 
 | LocalState_ι_uint256 => r4 
 | LocalState_ι_uint128 => r5 
 | LocalState_ι_uint8 => r6 
 | LocalState_ι_address => r7 
 | LocalState_ι_cell => r8 
 | LocalState_ι_XchgPair => r9 
 | LocalState_ι_bool => r10 
 | LocalState_ι_TradingPair => r11 
 | LocalState_ι_intIndex => r12 
 | LocalState_ι_optcellIndex => r13 
 | LocalState_ι_tpladdressaddressIndex => r14 
 | LocalState_ι_uint256Index => r15 
 | LocalState_ι_uint128Index => r16 
 | LocalState_ι_uint8Index => r17 
 | LocalState_ι_addressIndex => r18 
 | LocalState_ι_cellIndex => r19 
 | LocalState_ι_XchgPairIndex => r20 
 | LocalState_ι_boolIndex => r21 
 | LocalState_ι_TradingPairIndex => r22 
 end .
(* 5 *) Coercion LocalState_get : LocalStateFields >-> Funclass .
(* 6 *) Definition LocalState_set (f: LocalStateFields ) 
(v: LocalState_field_type f) (r: LocalState ): LocalState := 
 let '( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) := r in 
 match f, v with 
 | LocalState_ι_int , v' => ( v' , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_optcell , v' => ( r1 , v' , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_tpladdressaddress , v' => ( r1 , r2 , v' , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_uint256 , v' => ( r1 , r2 , r3 , v' , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_uint128 , v' => ( r1 , r2 , r3 , r4 , v' , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_uint8 , v' => ( r1 , r2 , r3 , r4 , r5 , v' , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_address , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , v' , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_cell , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , v' , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_XchgPair , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , v' , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_bool , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , v' , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_TradingPair , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , v' , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_intIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , v' , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_optcellIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , v' , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_tpladdressaddressIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , v' , r15 , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_uint256Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , v' , r16 , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_uint128Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , v' , r17 , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_uint8Index , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , v' , r18 , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_addressIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , v' , r19 , r20 , r21 , r22 ) 
 | LocalState_ι_cellIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , v' , r20 , r21 , r22 ) 
 | LocalState_ι_XchgPairIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , v' , r21 , r22 ) 
 | LocalState_ι_boolIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , v' , r22 ) 
 | LocalState_ι_TradingPairIndex , v' => ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 , r17 , r18 , r19 , r20 , r21 , v' ) 
 end .
(* 7 *) Global Instance LocalState_PruvendoRecord : PruvendoRecord LocalState LocalStateFields :=
{
  field_type := LocalState_field_type; 
  getPruvendoRecord := @LocalState_get ;
  setPruvendoRecord := @LocalState_set ;
} .
(* 3 *) Definition Ledger_field_type f : Type :=  
match f with 
 | Ledger_ι_FLeX => FLeX | Ledger_ι_VMState => VMState | Ledger_ι_LocalState => LocalState | Ledger_ι_LocalStateCopy => LocalState end .
(* 4 *) Definition Ledger_get (f: LedgerFields )(r: Ledger ) :  Ledger_field_type f := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f with 
 | Ledger_ι_FLeX => r1 
 | Ledger_ι_VMState => r2 
 | Ledger_ι_LocalState => r3 
 | Ledger_ι_LocalStateCopy => r4 
 end .
(* 5 *) Coercion Ledger_get : LedgerFields >-> Funclass .
(* 6 *) Definition Ledger_set (f: LedgerFields ) 
(v: Ledger_field_type f) (r: Ledger ): Ledger := 
 let '( r1 , r2 , r3 , r4 ) := r in 
 match f, v with 
 | Ledger_ι_FLeX , v' => ( v' , r2 , r3 , r4 ) 
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
Definition T1 := FLeX .
Definition T2 := VMState .
Definition T3 := LocalState .
Definition T4 := LocalState .

 
 Definition projEmbed_T1 : Ledger -> T1 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_FLeX. 
 Definition injEmbed_T1 : T1 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_FLeX. 
 
Axiom (* Lemma *) projinj_T1 : forall ( t : T1 ) ( s : Ledger ), projEmbed_T1 ( injEmbed_T1 t s ) = t . 
(*  Proof. 
 intros. auto. 
 Qed.  *)
 
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
 
Axiom (* Lemma *) projinj_T2 : forall ( t : T2 ) ( s : Ledger ), projEmbed_T2 ( injEmbed_T2 t s ) = t . 
(*  Proof. 
 intros. auto. 
 Qed. 
 *) 
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
 
Axiom (* Lemma *) projinj_T3 : forall ( t : T3 ) ( s : Ledger ), projEmbed_T3 ( injEmbed_T3 t s ) = t . 
(*  Proof. 
 intros. auto. 
 Qed. 
 *) 

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
 intros. auto. 
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
 



Axiom (* Lemma *) injcommute_T1_T2: 
               forall ( u : T2 ) ( t : T1 ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT2) u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT2) u s ) ).
(* Proof.
 intros.  auto.
Qed. *)

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


Axiom (* Lemma *) injcommute_T1xT2_T3 : 
               forall ( u : T3 ) ( t :  (T1 * T2)%xprod ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT3) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT3) u s ) ).
(* Proof.
 intros. auto.
Qed.
 *)
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


Axiom (* Lemma *) injcommute_T1xT2xT3_T4 : 
               forall ( u : T4 ) ( t :  ((T1 * T2)%xprod* T3)%xprod ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT4) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT4) u s ) ).
(* Proof.
 intros. auto.
Qed. *)

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

Axiom (* Lemma *) fullState_T1xT2xT3_T4 : forall s s0, 
 injEmbed ( T := (((T1 * T2)%xprod * T3)%xprod * T4)%xprod ) 
 ( projEmbed s ) ( injEmbed ( T := T4 ) ( projEmbed s ) s0 ) = s. 
(*  Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed.  *)
 
 Check FullState. 

 Instance FullState_T1xT2xT3_T4 : 
 FullState Ledger ((T1 * T2)%xprod * T3)%xprod T4 := 
 { 
 injComm := InjectCommutableStates_T1xT2xT3_T4 ; 
 fullState := fullState_T1xT2xT3_T4 
 } . 
 

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
Notation " ↓ m " := ( callEmbeddedStateAdj m default (H0 :=  FullState_T1xT2xT3_T4 ) ) (at level 31, left associativity): solidity_scope.
Global Instance iso_T1 : IsoTypes T1 (field_type (R:=Ledger) Ledger_ι_FLeX) :=
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


 Тут надо вручную вставлять поля леджера зависящие от полей 
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

Opaque FLeX.

Lemma Ledger1Type_eq: forall (l: Ledger), projT1 (rth 0 l) = FLeX.
Proof.
   intros.
   compute.
   destruct l.
   repeat destruct p.
   reflexivity.  
Defined.

Definition Ledger1Type (l: Ledger) := projT1 (rth 0 l).

Definition Ledger1TypeFLeX : forall (l:Ledger), Ledger1Type l -> FLeX.
intros.
unfold Ledger1Type in X.
rewrite Ledger1Type_eq in X.
exact X.
Defined.

Coercion Ledger1TypeFLeX       : Ledger1Type >-> FLeX.

Notation "r ₁" := ((projT2 (rth 0 r) : Ledger1Type r) : FLeX) (at level 10).

Transparent FLeXP.

Definition LedgerPruvendoRecord := Ledger_PruvendoRecord.
Definition LedgerLocalState := LocalState.
Definition LedgerLocalFields := LocalStateFields.
Definition LedgerLocalPruvendoRecord := LocalState_PruvendoRecord.
Definition LocalEmbedded := embeddedT4.
Definition LocalCopyEmbedded := embeddedT3.
Definition LocalDefault := LocalState_default.
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


(****************************************************************************)
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
Definition  LocalState_ι_optcellIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_optcellIndex l.

Definition  LocalState_ι_optcellIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_optcellIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_optcellIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_optcellIndex_Embedded_projEmbed (LocalState_ι_optcellIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_optcellIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_optcellIndex_Embedded_injEmbed (LocalState_ι_optcellIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_optcellIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_optcellIndex_Embedded_injEmbed t1 (LocalState_ι_optcellIndex_Embedded_injEmbed t2 s) = LocalState_ι_optcellIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_optcellIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_optcellIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_optcellIndex_Embedded_injEmbed;
  projinj := LocalState_ι_optcellIndex_Embedded_projinj;
  injproj := LocalState_ι_optcellIndex_Embedded_injproj;
  injinj := LocalState_ι_optcellIndex_Embedded_injinj
}.
Definition  LocalState_ι_tpladdressaddressIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_tpladdressaddressIndex l.

Definition  LocalState_ι_tpladdressaddressIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_tpladdressaddressIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_tpladdressaddressIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_tpladdressaddressIndex_Embedded_projEmbed (LocalState_ι_tpladdressaddressIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_tpladdressaddressIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_tpladdressaddressIndex_Embedded_injEmbed (LocalState_ι_tpladdressaddressIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_tpladdressaddressIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_tpladdressaddressIndex_Embedded_injEmbed t1 (LocalState_ι_tpladdressaddressIndex_Embedded_injEmbed t2 s) = LocalState_ι_tpladdressaddressIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_tpladdressaddressIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_tpladdressaddressIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_tpladdressaddressIndex_Embedded_injEmbed;
  projinj := LocalState_ι_tpladdressaddressIndex_Embedded_projinj;
  injproj := LocalState_ι_tpladdressaddressIndex_Embedded_injproj;
  injinj := LocalState_ι_tpladdressaddressIndex_Embedded_injinj
}.
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
(****************************************************************************)

Global Instance LocalState_ι_intIndex: LocalStateField XInteger :=
{
  local_index_embedded := LocalState_ι_int_Embedded;
  local_state_field := LocalState_ι_int; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_optcellIndex: LocalStateField ( XMaybe TvmCell ) :=
{
  local_index_embedded := LocalState_ι_optcell_Embedded;
  local_state_field := LocalState_ι_optcell; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_tpladdressaddressIndex: LocalStateField ( XAddress * XAddress ) :=
{
  local_index_embedded := LocalState_ι_tpladdressaddress_Embedded;
  local_state_field := LocalState_ι_tpladdressaddress; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_uint256Index: LocalStateField XInteger256 :=
{
  local_index_embedded := LocalState_ι_uint256_Embedded;
  local_state_field := LocalState_ι_uint256; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_uint128Index: LocalStateField XInteger128 :=
{
  local_index_embedded := LocalState_ι_uint128_Embedded;
  local_state_field := LocalState_ι_uint128; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_uint8Index: LocalStateField XInteger8 :=
{
  local_index_embedded := LocalState_ι_uint8_Embedded;
  local_state_field := LocalState_ι_uint8; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_addressIndex: LocalStateField XAddress :=
{
  local_index_embedded := LocalState_ι_address_Embedded;
  local_state_field := LocalState_ι_address; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_cellIndex: LocalStateField TvmCell :=
{
  local_index_embedded := LocalState_ι_cell_Embedded;
  local_state_field := LocalState_ι_cell; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_XchgPairIndex: LocalStateField _ι_XchgPair :=
{
  local_index_embedded := LocalState_ι_XchgPair_Embedded;
  local_state_field := LocalState_ι_XchgPair; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_boolIndex: LocalStateField XBool :=
{
  local_index_embedded := LocalState_ι_bool_Embedded;
  local_state_field := LocalState_ι_bool; 
  local_field_type_correct := eq_refl
}.

 
 
Global Instance LocalState_ι_TradingPairIndex: LocalStateField _ι_TradingPair :=
{
  local_index_embedded := LocalState_ι_TradingPair_Embedded;
  local_state_field := LocalState_ι_TradingPair; 
  local_field_type_correct := eq_refl
}.

 

End LedgerClass ."
     : string
