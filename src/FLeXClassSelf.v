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
 XInteger8  * 
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

(* 1 *) Inductive LocalStateFields := | LocalState_ι_uint256 | LocalState_ι_uint128 | LocalState_ι_uint8 | LocalState_ι_address | LocalState_ι_DTradingPair | LocalState_ι_cell | LocalState_ι_DXchgPair | LocalState_ι_bool | LocalState_ι_uint256Index | LocalState_ι_uint128Index | LocalState_ι_uint8Index | LocalState_ι_addressIndex | LocalState_ι_DTradingPairIndex | LocalState_ι_cellIndex | LocalState_ι_DXchgPairIndex | LocalState_ι_boolIndex .
(* 2 *) Definition LocalState := 
 ( XHMap (string*nat) XInteger256 * 
 XHMap (string*nat) XInteger128 * 
 XHMap (string*nat) XInteger8  * 
 XHMap (string*nat) XAddress * 
 XHMap (string*nat) TradingPair * 
 XHMap (string*nat) TvmCell * 
 XHMap (string*nat) XchgPair * 
 XHMap (string*nat) XBool * 
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
Notation " 'fst14' x " := ( fst ( fst13 x ) ) (at level 60, right associativity).
Notation " 'fst15' x " := ( fst ( fst14 x ) ) (at level 60, right associativity).
Notation " 'fst16' x " := ( fst ( fst15 x ) ) (at level 60, right associativity).
Notation " 'fst17' x " := ( fst ( fst16 x ) ) (at level 60, right associativity).
Notation " 'fst18' x " := ( fst ( fst17 x ) ) (at level 60, right associativity).
Notation " 'fst19' x " := ( fst ( fst18 x ) ) (at level 60, right associativity).
Notation " 'fst20' x " := ( fst ( fst19 x ) ) (at level 60, right associativity).

(* 3 *) Definition TonsConfig_field_type f : Type :=  
match f with 
 | TonsConfig_ι_transfer_tip3 => XInteger128 
 | TonsConfig_ι_return_ownership => XInteger128 
 | TonsConfig_ι_trading_pair_deploy => XInteger128 
 | TonsConfig_ι_order_answer => XInteger128 
 | TonsConfig_ι_process_queue => XInteger128 
 | TonsConfig_ι_send_notify => XInteger128 
end .

(* 4 *) Definition TonsConfig_get (f: TonsConfigFields )(r: TonsConfig ) :  TonsConfig_field_type f := 
 match f with 
 | TonsConfig_ι_transfer_tip3 => fst5 r 
 | TonsConfig_ι_return_ownership => snd ( fst4 r ) 
 | TonsConfig_ι_trading_pair_deploy => snd ( fst3 r ) 
 | TonsConfig_ι_order_answer => snd ( fst2 r ) 
 | TonsConfig_ι_process_queue => snd ( fst1 r ) 
 | TonsConfig_ι_send_notify => snd r 
 end . 
(* 5 *) Coercion TonsConfig_get : TonsConfigFields >-> Funclass .
(* 6 *) Definition TonsConfig_set (f: TonsConfigFields ) 
(v: TonsConfig_field_type f) (r: TonsConfig ): TonsConfig  :=
  match f, v with | TonsConfig_ι_transfer_tip3 , v' => ( v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_return_ownership , v' => ( fst5 r , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_trading_pair_deploy , v' => ( fst5 r , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_order_answer , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_process_queue , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | TonsConfig_ι_send_notify , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
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
 match f with 
 | FLeX_ι_deployer_pubkey_ => fst8 r 
 | FLeX_ι_tons_cfg_ => snd ( fst7 r ) 
 | FLeX_ι_pair_code_ => snd ( fst6 r ) 
 | FLeX_ι_xchg_pair_code_ => snd ( fst5 r ) 
 | FLeX_ι_price_code_ => snd ( fst4 r ) 
 | FLeX_ι_xchg_price_code_ => snd ( fst3 r ) 
 | FLeX_ι_min_amount_ => snd ( fst2 r ) 
 | FLeX_ι_deals_limit_ => snd ( fst1 r ) 
 | FLeX_ι_notify_addr_ => snd r 
 end .
(* 5 *) Coercion FLeX_get : FLeXFields >-> Funclass .
(* 6 *) Definition FLeX_set (f: FLeXFields ) 
(v: FLeX_field_type f) (r: FLeX ): FLeX  :=
  match f, v with | FLeX_ι_deployer_pubkey_ , v' => ( v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_tons_cfg_ , v' => ( fst8 r , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_pair_code_ , v' => ( fst8 r , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_xchg_pair_code_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_price_code_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_xchg_price_code_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_min_amount_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_deals_limit_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeX_ι_notify_addr_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
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
 match f with 
 | TradingPair_ι_flex_addr_ => fst2 r 
 | TradingPair_ι_tip3_root_ => snd ( fst1 r ) 
 | TradingPair_ι_deploy_value_ => snd r 
 end .
(* 5 *) Coercion TradingPair_get : TradingPairFields >-> Funclass .
(* 6 *) Definition TradingPair_set (f: TradingPairFields ) 
(v: TradingPair_field_type f) (r: TradingPair ): TradingPair  :=
  match f, v with | TradingPair_ι_flex_addr_ , v' => ( v' , snd ( fst1 r ) , snd r ) 
 | TradingPair_ι_tip3_root_ , v' => ( fst2 r , v' , snd r ) 
 | TradingPair_ι_deploy_value_ , v' => ( fst2 r , snd ( fst1 r ) , v' ) 
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
 match f with 
 | XchgPair_ι_flex_addr_ => fst3 r 
 | XchgPair_ι_tip3_major_root_ => snd ( fst2 r ) 
 | XchgPair_ι_tip3_minor_root_ => snd ( fst1 r ) 
 | XchgPair_ι_deploy_value_ => snd r 
 end .
(* 5 *) Coercion XchgPair_get : XchgPairFields >-> Funclass .
(* 6 *) Definition XchgPair_set (f: XchgPairFields ) 
(v: XchgPair_field_type f) (r: XchgPair ): XchgPair  :=
  match f, v with | XchgPair_ι_flex_addr_ , v' => ( v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | XchgPair_ι_tip3_major_root_ , v' => ( fst3 r , v' , snd ( fst1 r ) , snd r ) 
 | XchgPair_ι_tip3_minor_root_ , v' => ( fst3 r , snd ( fst2 r ) , v' , snd r ) 
 | XchgPair_ι_deploy_value_ , v' => ( fst3 r , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance XchgPair_PruvendoRecord : PruvendoRecord XchgPair XchgPairFields :=
{
  field_type := XchgPair_field_type; 
  getPruvendoRecord := @XchgPair_get ;
  setPruvendoRecord := @XchgPair_set ;
} .
(* (* 3 *) Definition VMState_field_type f : Type :=  
match f with 
 | VMState_ι_msg_pubkey => XInteger256 | VMState_ι_now => XInteger64 | VMState_ι_accepted => XBool | VMState_ι_msg_value => XInteger256 end .
(* 4 *) Definition VMState_get (f: VMStateFields )(r: VMState ) :  VMState_field_type f := 
 match f with 
 | VMState_ι_msg_pubkey => fst3 r 
 | VMState_ι_now => snd ( fst2 r ) 
 | VMState_ι_accepted => snd ( fst1 r ) 
 | VMState_ι_msg_value => snd r 
 end .
(* 5 *) Coercion VMState_get : VMStateFields >-> Funclass .
(* 6 *) Definition VMState_set (f: VMStateFields ) 
(v: VMState_field_type f) (r: VMState ): VMState  :=
  match f, v with | VMState_ι_msg_pubkey , v' => ( v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | VMState_ι_now , v' => ( fst3 r , v' , snd ( fst1 r ) , snd r ) 
 | VMState_ι_accepted , v' => ( fst3 r , snd ( fst2 r ) , v' , snd r ) 
 | VMState_ι_msg_value , v' => ( fst3 r , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance VMState_PruvendoRecord : PruvendoRecord VMState VMStateFields :=
{
  field_type := VMState_field_type; 
  getPruvendoRecord := @VMState_get ;
  setPruvendoRecord := @VMState_set ;
} .
 *)

(* 3 *) Definition LocalState_field_type f : Type :=  
match f with 
 | LocalState_ι_uint256 => XHMap (string*nat) XInteger256 | LocalState_ι_uint128 => XHMap (string*nat) XInteger128 | LocalState_ι_uint8 => XHMap (string*nat) XInteger8 | LocalState_ι_address => XHMap (string*nat) XAddress | LocalState_ι_DTradingPair => XHMap (string*nat) TradingPair | LocalState_ι_cell => XHMap (string*nat) TvmCell | LocalState_ι_DXchgPair => XHMap (string*nat) XchgPair | LocalState_ι_bool => XHMap (string*nat) XBool | LocalState_ι_uint256Index => XHMap string nat | LocalState_ι_uint128Index => XHMap string nat | LocalState_ι_uint8Index => XHMap string nat | LocalState_ι_addressIndex => XHMap string nat | LocalState_ι_DTradingPairIndex => XHMap string nat | LocalState_ι_cellIndex => XHMap string nat | LocalState_ι_DXchgPairIndex => XHMap string nat | LocalState_ι_boolIndex => XHMap string nat end .
(* 4 *) Definition LocalState_get (f: LocalStateFields )(r: LocalState ) :  LocalState_field_type f := 
 match f , r with 
 | LocalState_ι_uint256 , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r1 
 | LocalState_ι_uint128 , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r2 
 | LocalState_ι_uint8 , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r3 
 | LocalState_ι_address , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r4 
 | LocalState_ι_DTradingPair , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r5 
 | LocalState_ι_cell , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r6 
 | LocalState_ι_DXchgPair , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r7 
 | LocalState_ι_bool , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r8 
 | LocalState_ι_uint256Index , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r9 
 | LocalState_ι_uint128Index , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r10 
 | LocalState_ι_uint8Index , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r11 
 | LocalState_ι_addressIndex , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r12 
 | LocalState_ι_DTradingPairIndex , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r13 
 | LocalState_ι_cellIndex , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r14 
 | LocalState_ι_DXchgPairIndex , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r15 
 | LocalState_ι_boolIndex , ( r1 , r2 , r3 , r4 , r5 , r6 , r7 , r8 , r9 , r10 , r11 , r12 , r13 , r14 , r15 , r16 ) => r16 
 end .
(* 5 *) Coercion LocalState_get : LocalStateFields >-> Funclass .
(* 6 *) Definition LocalState_set (f: LocalStateFields ) 
(v: LocalState_field_type f) (r: LocalState ): LocalState  :=
  match f, v with 
| LocalState_ι_uint256 , v' => ( v' , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint128 , v' => ( fst15 r , v' , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint8 , v' => ( fst15 r , snd ( fst14 r ) , v' , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_address , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , v' , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DTradingPair , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , v' , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_cell , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DXchgPair , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_bool , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint256Index , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint128Index , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint8Index , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_addressIndex , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DTradingPairIndex , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_cellIndex , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DXchgPairIndex , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | LocalState_ι_boolIndex , v' => ( fst15 r , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
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
 match f with 
 | Ledger_ι_FLeX => fst3 r 
 | Ledger_ι_VMState => snd ( fst2 r ) 
 | Ledger_ι_LocalState => snd ( fst1 r ) 
 | Ledger_ι_LocalStateCopy => snd r 
 end .
(* 5 *) Coercion Ledger_get : LedgerFields >-> Funclass .
(* 6 *) Definition Ledger_set (f: LedgerFields ) 
(v: Ledger_field_type f) (r: Ledger ): Ledger  :=
  match f, v with | Ledger_ι_FLeX , v' => ( v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Ledger_ι_VMState , v' => ( fst3 r , v' , snd ( fst1 r ) , snd r ) 
 | Ledger_ι_LocalState , v' => ( fst3 r , snd ( fst2 r ) , v' , snd r ) 
 | Ledger_ι_LocalStateCopy , v' => ( fst3 r , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
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
 
 Lemma projinj_T1 : forall ( t : T1 ) ( s : Ledger ), projEmbed_T1 ( injEmbed_T1 t s ) = t . 
 Proof. 
         intros. auto. 
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
 intros. auto. 
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
 intros. auto. 
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

Lemma injcommute_T1_T2: 
               forall ( u : T2 ) ( t : T1 ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT2) u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT2) u s ) ).
Proof.
 intros.  auto.
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
 intros. auto.
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
 intros. auto.
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
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 

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
(****************************************************************************)

Definition  FLeX_ι_tons_cfg_TonsConfig  :
 PruvendoRecord (field_type (R:=FLeX) 
                 FLeX_ι_tons_cfg_ ) TonsConfigFields := TonsConfig_PruvendoRecord.

Existing Instance FLeX_ι_tons_cfg_TonsConfig.

Existing Instance Ledger_PruvendoRecord.

(****************************************************************************)

(***************************************************************)

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

Transparent FLeX.

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
Definition  LocalState_ι_DTradingPairIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_DTradingPairIndex l.

Definition  LocalState_ι_DTradingPairIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_DTradingPairIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_DTradingPairIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_DTradingPairIndex_Embedded_projEmbed (LocalState_ι_DTradingPairIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_DTradingPairIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_DTradingPairIndex_Embedded_injEmbed (LocalState_ι_DTradingPairIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_DTradingPairIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_DTradingPairIndex_Embedded_injEmbed t1 (LocalState_ι_DTradingPairIndex_Embedded_injEmbed t2 s) = LocalState_ι_DTradingPairIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_DTradingPairIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_DTradingPairIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_DTradingPairIndex_Embedded_injEmbed;
  projinj := LocalState_ι_DTradingPairIndex_Embedded_projinj;
  injproj := LocalState_ι_DTradingPairIndex_Embedded_injproj;
  injinj := LocalState_ι_DTradingPairIndex_Embedded_injinj
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
Definition  LocalState_ι_DXchgPairIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_DXchgPairIndex l.

Definition  LocalState_ι_DXchgPairIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_DXchgPairIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_DXchgPairIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_DXchgPairIndex_Embedded_projEmbed (LocalState_ι_DXchgPairIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_DXchgPairIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_DXchgPairIndex_Embedded_injEmbed (LocalState_ι_DXchgPairIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_DXchgPairIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_DXchgPairIndex_Embedded_injEmbed t1 (LocalState_ι_DXchgPairIndex_Embedded_injEmbed t2 s) = LocalState_ι_DXchgPairIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_DXchgPairIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_DXchgPairIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_DXchgPairIndex_Embedded_injEmbed;
  projinj := LocalState_ι_DXchgPairIndex_Embedded_projinj;
  injproj := LocalState_ι_DXchgPairIndex_Embedded_injproj;
  injinj := LocalState_ι_DXchgPairIndex_Embedded_injinj
}.




Definition  LocalState_ι_boolIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_boolIndex l.

Definition  LocalState_ι_boolIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_boolIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_boolIndex_Embedded_projinj : 
              forall (t : XHMap string nat) (s : LedgerLocalState), 
              LocalState_ι_boolIndex_Embedded_projEmbed (LocalState_ι_boolIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_boolIndex_Embedded_injproj : forall s : LedgerLocalState, 
                      LocalState_ι_boolIndex_Embedded_injEmbed (LocalState_ι_boolIndex_Embedded_projEmbed s) s = s.
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

(****************************************************************************)

Class LocalStateField (X:Type): Type := 
{
    local_index_embedded:> EmbeddedType LedgerLocalState (XHMap string nat) ;
    local_state_field: LedgerLocalFields;
    local_field_type_correct: field_type (PruvendoRecord:=LedgerLocalPruvendoRecord) local_state_field = XHMap (string*nat)%type X;
}.

(* 
(* Global Instance LocalState_ι_uint256Index: LocalStateField XInteger256 :=
{
  local_index_embedded := LocalState_ι_uint256Index_Embedded;
  local_state_field := LocalState_ι_uint256; 
  local_field_type_correct := eq_refl
}.
 *)

*)
(* 
Global Instance LocalState_ι_cellIndex: LocalStateField TvmCell :=
{
  local_index_embedded := LocalState_ι_cellIndex_Embedded;
  local_state_field := LocalState_ι_cell; 
  local_field_type_correct := eq_refl
}. *)

(*

Global Instance LocalState_ι_uint8Index: LocalStateField XInteger8 :=
{
  local_index_embedded := LocalState_ι_uint8Index_Embedded;
  local_state_field := LocalState_ι_uint8; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_addressIndex: LocalStateField XAddress :=
{
  local_index_embedded := LocalState_ι_addressIndex_Embedded;
  local_state_field := LocalState_ι_address; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_uint128Index: LocalStateField XInteger128 :=
{
  local_index_embedded := LocalState_ι_uint128Index_Embedded;
  local_state_field := LocalState_ι_uint128; 
  local_field_type_correct := eq_refl
}.

Global Instance LocalState_ι_DTradingPairIndex : LocalStateField TradingPair :=
{
  local_index_embedded := LocalState_ι_DTradingPairIndex_Embedded;
  local_state_field := LocalState_ι_DTradingPair; 
  local_field_type_correct := eq_refl
}.


Global Instance LocalState_ι_DXchgPairIndex: LocalStateField XchgPair :=
{
  local_index_embedded := LocalState_ι_DXchgPairIndex_Embedded;
  local_state_field := LocalState_ι_DXchgPair; 
  local_field_type_correct := eq_refl
}. *)

Global Instance LocalStateField_XInteger: LocalStateField XInteger8 :=
{
  local_index_embedded := LocalState_ι_uint8Index_Embedded;
  local_state_field := LocalState_ι_uint8; 
  local_field_type_correct := eq_refl
}.

Global Instance LocalStateField_XBool: LocalStateField XBool :=
{
  local_index_embedded := LocalState_ι_boolIndex_Embedded;
  local_state_field := LocalState_ι_bool; 
  local_field_type_correct := eq_refl
}.

Global Instance LocalStateField_TvmCell : LocalStateField TvmCell :=
{
  local_index_embedded := LocalState_ι_cellIndex_Embedded;
  local_state_field := LocalState_ι_cell; 
  local_field_type_correct := eq_refl
}.

Definition LedgerVMStateEmbedded := embeddedT2. 
Definition LedgerVMStateField := Ledger_ι_VMState .
Definition isoVMState := iso_T2.


End LedgerClass .
