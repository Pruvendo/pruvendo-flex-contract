Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
Require Import FinProof.StateMonad21.
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.


Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.
Require Import UMLang.ExecGenerator.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.
Require Import Project.CommonNotations.
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.FlexClient.Ledger.
Require Import Contracts.FlexClient.Functions.FuncSig.
Require Import Contracts.FlexClient.Functions.FuncNotations.
Require Import Contracts.FlexClient.Functions.Funcs.
Require  Contracts.FlexClient.Interface.

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.


Module EvalExecAuto (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .


Module Export FuncsModule := Funcs co dc.

Import FuncsInternal.
Import co.
(* Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module Import TONTonkenWalletModuleForFlexClient := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .
(* Export SpecModuleForFuncNotations(* ForFuncs *).CommonNotationsModule. *)
 *)
Module Import xxx := SpecModuleForFuncNotations.LedgerModuleForFuncSig.

Module Import generator := execGenerator XTypesModule StateMonadModule xxx.
 
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.


(*move somewhere*)

Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.


(*  
Compute default : LocalStateLRecord.
 *) 
 Definition LocalStateDefault := (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil))),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
 (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)))),
 (Datatypes.nil, Datatypes.nil))%xprod
: LocalStateLRecord.
 
 Opaque LocalStateDefault.
 Import URSUS_.

Ltac generate_proof gen :=
  let e := fresh "e" in
  let H := fresh "H" in
  let gen_nf := eval hnf in gen in
  generate_both gen_nf e H; cycle -1;
  (only 1: (exists e; subst e; reflexivity));
  eexists; reflexivity.

Ltac proof_of t :=
  let e := fresh "e" in
  let H := fresh "H" in
  let E := fresh "E" in
  destruct t as [e H] eqn:E; rewrite <- H; replace e with
  (let (e', _) := t in e');
  try reflexivity ;try (rewrite E; reflexivity).
 (* ----------------------------------------- *)
Section constructor. 
Definition constructor_exec_P (l : Ledger) ( pubkey : ( uint256 ) ) ( trading_pair_code : ( TvmCells.cell ) ) ( xchg_pair_code : ( TvmCells.cell ) ): 
{l' | l' = exec_state (Uinterpreter (constructor pubkey trading_pair_code xchg_pair_code)) l}.
  generate_proof (exec_expression l (constructor pubkey trading_pair_code xchg_pair_code)).
Defined.

Definition constructor_auto_exec (l : Ledger) ( pubkey : ( uint256 ) ) ( trading_pair_code : ( TvmCells.cell ) ) ( xchg_pair_code : ( TvmCells.cell ) ): Ledger.
intros. term_of (constructor_exec_P l pubkey trading_pair_code xchg_pair_code).
Defined.

Theorem constructor_exec_proof_next (l : Ledger) ( pubkey : ( uint256 ) ) ( trading_pair_code : ( TvmCells.cell ) ) ( xchg_pair_code : ( TvmCells.cell ) ) :
  constructor_auto_exec l pubkey trading_pair_code xchg_pair_code =
  exec_state (Uinterpreter (constructor pubkey trading_pair_code xchg_pair_code)) l.
Proof.
  intros. proof_of (constructor_exec_P l pubkey trading_pair_code xchg_pair_code).
Qed.

(* no eval  *)
End constructor.
(* ----------------------------------------- *)
Section setFlexCfg.
Definition setFlexCfg_exec_P (l : Ledger) ( tons_cfg : ( TonsConfigLRecord ) ) 
( flex : ( address ) ): 
{l' | l' = exec_state (Uinterpreter (setFlexCfg tons_cfg flex)) l}.
  generate_proof (exec_expression l (setFlexCfg tons_cfg flex)).
Defined.
Definition setFlexCfg_auto_exec (l : Ledger) ( tons_cfg : ( TonsConfigLRecord ) ) 
( flex : ( address ) ): Ledger.
intros. term_of (setFlexCfg_exec_P l tons_cfg flex).
Defined.
Theorem setFlexCfg_exec_proof_next (l : Ledger) ( tons_cfg : ( TonsConfigLRecord ) ) 
( flex : ( address ) ) :
  setFlexCfg_auto_exec l tons_cfg flex =
  exec_state (Uinterpreter (setFlexCfg tons_cfg flex)) l.
Proof.
  intros. proof_of (setFlexCfg_exec_P l tons_cfg flex).
Qed.
(* no eval*)
End setFlexCfg.
(* ----------------------------------------- *)
Section setExtWalletCode.
Definition setExtWalletCode_exec_P (l : Ledger) ( ext_wallet_code : ( TvmCells.cell ) ): 
{l' | l' = exec_state (Uinterpreter (setExtWalletCode ext_wallet_code)) l}.
  generate_proof (exec_expression l (setExtWalletCode ext_wallet_code)).
Defined.
Definition setExtWalletCode_auto_exec (l : Ledger) ( ext_wallet_code : ( TvmCells.cell ) ): Ledger.
intros. term_of (setExtWalletCode_exec_P l ext_wallet_code).
Defined.
Theorem setExtWalletCode_exec_proof_next (l : Ledger) ( ext_wallet_code : ( TvmCells.cell ) ) :
  setExtWalletCode_auto_exec l ext_wallet_code =
  exec_state (Uinterpreter (setExtWalletCode ext_wallet_code)) l.
Proof.
  intros. proof_of (setExtWalletCode_exec_P l ext_wallet_code).
Qed.
(* no eval *)
End setExtWalletCode.
(* ----------------------------------------- *)
Section setFlexWalletCode.
Definition setFlexWalletCode_exec_P (l : Ledger) ( flex_wallet_code : ( TvmCells.cell ) ): 
{l' | l' = exec_state (Uinterpreter (setFlexWalletCode flex_wallet_code)) l}.
  generate_proof (exec_expression l (setFlexWalletCode flex_wallet_code)).
Defined.
Definition setFlexWalletCode_auto_exec (l : Ledger) ( flex_wallet_code : ( TvmCells.cell ) ): Ledger.
intros. term_of (setFlexWalletCode_exec_P l flex_wallet_code).
Defined.
Theorem setFlexWalletCode_exec_proof_next (l : Ledger) ( flex_wallet_code : ( TvmCells.cell ) ) :
  setFlexWalletCode_auto_exec l flex_wallet_code =
  exec_state (Uinterpreter (setFlexWalletCode flex_wallet_code)) l.
Proof.
  intros. proof_of (setFlexWalletCode_exec_P l flex_wallet_code).
Qed.
End setFlexWalletCode.
(* ----------------------------------------- *)
Section setFlexWrapperCode.
Definition setFlexWrapperCode_exec_P (l : Ledger) ( flex_wrapper_code : ( TvmCells.cell ) ): 
{l' | l' = exec_state (Uinterpreter (setFlexWrapperCode flex_wrapper_code)) l}.
  generate_proof (exec_expression l (setFlexWrapperCode flex_wrapper_code)).
Defined.
Definition setFlexWrapperCode_auto_exec (l : Ledger) ( flex_wrapper_code : ( TvmCells.cell ) ): Ledger.
intros. term_of (setFlexWrapperCode_exec_P l flex_wrapper_code).
Defined.
Theorem setFlexWrapperCode_exec_proof_next (l : Ledger) ( flex_wrapper_code : ( TvmCells.cell ) ) :
  setFlexWrapperCode_auto_exec l flex_wrapper_code =
  exec_state (Uinterpreter (setFlexWrapperCode flex_wrapper_code)) l.
Proof.
  intros. proof_of (setFlexWrapperCode_exec_P l flex_wrapper_code).
Qed.
End setFlexWrapperCode.
(* ----------------------------------------- *)
Section prepare_trading_pair_state_init_and_addr.    

Definition prepare_trading_pair_state_init_and_addr_exec_P (l : Ledger) ( pair_data : TradingPairClassTypes.DTradingPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ): 
{l' | l' = exec_state (Uinterpreter (prepare_trading_pair_state_init_and_addr pair_data pair_code)) l}. 
  generate_proof (exec_expression l (prepare_trading_pair_state_init_and_addr pair_data pair_code)).
Defined.
Definition prepare_trading_pair_state_init_and_addr_auto_exec (l : Ledger) ( pair_data : TradingPairClassTypes.DTradingPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ): Ledger.
intros. term_of (prepare_trading_pair_state_init_and_addr_exec_P l pair_data pair_code).
Defined.
Theorem prepare_trading_pair_state_init_and_addr_exec_proof_next (l : Ledger) ( pair_data : TradingPairClassTypes.DTradingPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ) :
  prepare_trading_pair_state_init_and_addr_auto_exec l pair_data pair_code =
  exec_state (Uinterpreter (prepare_trading_pair_state_init_and_addr pair_data pair_code)) l.
Proof.
  intros. (* proof_of (prepare_trading_pair_state_init_and_addr_exec_P l pair_data pair_code). *)
  destruct (prepare_trading_pair_state_init_and_addr_exec_P l pair_data pair_code) as [e H] eqn:E. rewrite <- H.
replace e with
  (let (e', _) := ( prepare_trading_pair_state_init_and_addr_exec_P l pair_data pair_code ) in e').
unfold prepare_trading_pair_state_init_and_addr_exec_P.
  reflexivity.
  rewrite E.
  reflexivity.
Qed.

Definition prepare_trading_pair_state_init_and_addr_eval_P (l : Ledger) ( pair_data : TradingPairClassTypes.DTradingPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_trading_pair_state_init_and_addr pair_data pair_code)) l)}.
  generate_proof (eval_expression l (prepare_trading_pair_state_init_and_addr pair_data pair_code)).
Defined.

Definition prepare_trading_pair_state_init_and_addr_auto_eval (l : Ledger) ( pair_data : TradingPairClassTypes.DTradingPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ): (StateInitLRecord # uint256).
intros. term_of (prepare_trading_pair_state_init_and_addr_eval_P l pair_data pair_code).
Defined.

Theorem prepare_trading_pair_state_init_and_addr_eval_proof_next (l : Ledger) ( pair_data : TradingPairClassTypes.DTradingPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ) :
  prepare_trading_pair_state_init_and_addr_auto_eval l pair_data pair_code =
  toValue (eval_state (Uinterpreter (prepare_trading_pair_state_init_and_addr pair_data pair_code)) l).
Proof.
  intros. proof_of (prepare_trading_pair_state_init_and_addr_eval_P l pair_data pair_code).
Qed.

End prepare_trading_pair_state_init_and_addr.
(* ----------------------------------------- *)
Section deployTradingPair.

Definition deployTradingPair_exec_P (l : Ledger) ( tip3_root : ( address ) ) 
                              ( deploy_min_value : ( uint128 ) ) 
                              ( deploy_value : ( uint128 ) ) 
                              ( min_trade_amount : ( uint128 ) ) 
                              ( notify_addr : ( address ) ): 
{l' | l' = exec_state (Uinterpreter (deployTradingPair tip3_root deploy_min_value deploy_value min_trade_amount notify_addr)) l}.
  generate_proof (exec_expression l (deployTradingPair tip3_root deploy_min_value deploy_value min_trade_amount notify_addr)).
Defined.

Definition deployTradingPair_auto_exec (l : Ledger) ( tip3_root : ( address ) ) 
                              ( deploy_min_value : ( uint128 ) ) 
                              ( deploy_value : ( uint128 ) ) 
                              ( min_trade_amount : ( uint128 ) ) 
                              ( notify_addr : ( address ) ): Ledger.
intros. term_of (deployTradingPair_exec_P l tip3_root deploy_min_value deploy_value min_trade_amount notify_addr).
Defined.

Theorem deployTradingPair_exec_proof_next (l : Ledger) ( tip3_root : ( address ) ) 
                              ( deploy_min_value : ( uint128 ) ) 
                              ( deploy_value : ( uint128 ) ) 
                              ( min_trade_amount : ( uint128 ) ) 
                              ( notify_addr : ( address ) ) :
  deployTradingPair_auto_exec l tip3_root deploy_min_value deploy_value min_trade_amount notify_addr =
  exec_state (Uinterpreter (deployTradingPair tip3_root deploy_min_value deploy_value min_trade_amount notify_addr)) l.
Proof.
  intros. (* proof_of (deployTradingPair_exec_P l tip3_root deploy_min_value deploy_value min_trade_amount notify_addr). *)
  destruct (deployTradingPair_exec_P l tip3_root deploy_min_value deploy_value min_trade_amount notify_addr) as [e H] eqn:E. rewrite <- H. 
replace e with
  (let (e', _) := ( deployTradingPair_exec_P l tip3_root deploy_min_value deploy_value min_trade_amount notify_addr) in e').
unfold deployTradingPair_exec_P.
  (* reflexivity.
  rewrite E.
  reflexivity.
Qed. *)
Admitted. 

(* TODO eval true *)
Definition deployTradingPair_eval_P (l : Ledger) ( tip3_root : ( address ) ) 
                              ( deploy_min_value : ( uint128 ) ) 
                              ( deploy_value : ( uint128 ) ) 
                              ( min_trade_amount : ( uint128 ) ) 
                              ( notify_addr : ( address ) ): 
{v | v =  (eval_state (Uinterpreter (deployTradingPair tip3_root deploy_min_value deploy_value min_trade_amount notify_addr)) l)}.
  generate_proof (eval_expression l (deployTradingPair tip3_root deploy_min_value deploy_value min_trade_amount notify_addr)).
Defined.

Definition deployTradingPair_auto_eval (l : Ledger) ( tip3_root : ( address ) ) 
                              ( deploy_min_value : ( uint128 ) ) 
                              ( deploy_value : ( uint128 ) ) 
                              ( min_trade_amount : ( uint128 ) ) 
                              ( notify_addr : ( address ) ): ControlResult (address) true.
intros. term_of (deployTradingPair_eval_P l tip3_root deploy_min_value deploy_value min_trade_amount notify_addr).
Defined.
Theorem deployTradingPair_eval_proof_next (l : Ledger) ( tip3_root : ( address ) ) 
                              ( deploy_min_value : ( uint128 ) ) 
                              ( deploy_value : ( uint128 ) ) 
                              ( min_trade_amount : ( uint128 ) ) 
                              ( notify_addr : ( address ) ) :
  deployTradingPair_auto_eval l tip3_root deploy_min_value deploy_value min_trade_amount notify_addr =
   (eval_state (Uinterpreter (deployTradingPair tip3_root deploy_min_value deploy_value min_trade_amount notify_addr)) l).
Proof.
  intros. proof_of (deployTradingPair_eval_P l tip3_root deploy_min_value deploy_value min_trade_amount notify_addr).
Qed.
End deployTradingPair.
(* ----------------------------------------- *)
Section prepare_xchg_pair_state_init_and_addr.
Definition prepare_xchg_pair_state_init_and_addr_exec_P (l : Ledger) ( pair_data : XchgPairClassTypes.DXchgPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ): 
{l' | l' = exec_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l}.
  generate_proof (exec_expression l (prepare_xchg_pair_state_init_and_addr pair_data pair_code)).
Defined.
Definition prepare_xchg_pair_state_init_and_addr_auto_exec (l : Ledger) ( pair_data : XchgPairClassTypes.DXchgPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ): Ledger.
intros. term_of (prepare_xchg_pair_state_init_and_addr_exec_P l pair_data pair_code).
Defined.
Theorem prepare_xchg_pair_state_init_and_addr_exec_proof_next (l : Ledger) ( pair_data : XchgPairClassTypes.DXchgPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ) :
  prepare_xchg_pair_state_init_and_addr_auto_exec l pair_data pair_code =
  exec_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l.
Proof.
  intros. proof_of (prepare_xchg_pair_state_init_and_addr_exec_P l pair_data pair_code).
Qed.
Definition prepare_xchg_pair_state_init_and_addr_eval_P (l : Ledger) ( pair_data : XchgPairClassTypes.DXchgPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l)}.
  generate_proof (eval_expression l (prepare_xchg_pair_state_init_and_addr pair_data pair_code)).
Defined.
Definition prepare_xchg_pair_state_init_and_addr_auto_eval (l : Ledger) ( pair_data : XchgPairClassTypes.DXchgPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ): (StateInitLRecord # uint256).
intros. term_of (prepare_xchg_pair_state_init_and_addr_eval_P l pair_data pair_code).
Defined.
Theorem prepare_xchg_pair_state_init_and_addr_eval_proof_next (l : Ledger) ( pair_data : XchgPairClassTypes.DXchgPairLRecord ) 
                                                    ( pair_code : TvmCells.cell  ) :
  prepare_xchg_pair_state_init_and_addr_auto_eval l pair_data pair_code =
  toValue (eval_state (Uinterpreter (prepare_xchg_pair_state_init_and_addr pair_data pair_code)) l).
Proof.
  intros. proof_of (prepare_xchg_pair_state_init_and_addr_eval_P l pair_data pair_code).
Qed.
End prepare_xchg_pair_state_init_and_addr.
(* ----------------------------------------- *)
Section deployXchgPair.
Definition deployXchgPair_exec_P (l : Ledger) ( tip3_major_root : ( address_t ) ) 
                           ( tip3_minor_root : ( address_t ) ) 
                           ( deploy_min_value : ( uint128 ) ) 
                           ( deploy_value : ( uint128 ) ) 
                           ( min_trade_amount : ( uint128 ) ) 
                           ( notify_addr : ( address_t ) ): 
{l' | l' = exec_state (Uinterpreter (deployXchgPair tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr)) l}.
  generate_proof (exec_expression l (deployXchgPair tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr)).
Defined.
Definition deployXchgPair_auto_exec (l : Ledger) ( tip3_major_root : ( address_t ) ) 
                           ( tip3_minor_root : ( address_t ) ) 
                           ( deploy_min_value : ( uint128 ) ) 
                           ( deploy_value : ( uint128 ) ) 
                           ( min_trade_amount : ( uint128 ) ) 
                           ( notify_addr : ( address_t ) ): Ledger.
intros. term_of (deployXchgPair_exec_P l tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr).
Defined.
Theorem deployXchgPair_exec_proof_next (l : Ledger) ( tip3_major_root : ( address_t ) ) 
                           ( tip3_minor_root : ( address_t ) ) 
                           ( deploy_min_value : ( uint128 ) ) 
                           ( deploy_value : ( uint128 ) ) 
                           ( min_trade_amount : ( uint128 ) ) 
                           ( notify_addr : ( address_t ) ) :
  deployXchgPair_auto_exec l tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr =
  exec_state (Uinterpreter (deployXchgPair tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr)) l.
Proof.
  intros. proof_of (deployXchgPair_exec_P l tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr).
Qed.


(*  TODO eval true *)
Definition deployXchgPair_eval_P (l : Ledger) ( tip3_major_root : ( address_t ) ) 
                           ( tip3_minor_root : ( address_t ) ) 
                           ( deploy_min_value : ( uint128 ) ) 
                           ( deploy_value : ( uint128 ) ) 
                           ( min_trade_amount : ( uint128 ) ) 
                           ( notify_addr : ( address_t ) ): 
{v | v =  (eval_state (Uinterpreter (deployXchgPair tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr)) l)}.
  generate_proof (eval_expression l (deployXchgPair tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr)).
Defined.
Definition deployXchgPair_auto_eval (l : Ledger) ( tip3_major_root : ( address_t ) ) 
                           ( tip3_minor_root : ( address_t ) ) 
                           ( deploy_min_value : ( uint128 ) ) 
                           ( deploy_value : ( uint128 ) ) 
                           ( min_trade_amount : ( uint128 ) ) 
                           ( notify_addr : ( address_t ) ): ControlResult address true.
intros. term_of (deployXchgPair_eval_P l tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr).
Defined.
Theorem deployXchgPair_eval_proof_next (l : Ledger) ( tip3_major_root : ( address_t ) ) 
                           ( tip3_minor_root : ( address_t ) ) 
                           ( deploy_min_value : ( uint128 ) ) 
                           ( deploy_value : ( uint128 ) ) 
                           ( min_trade_amount : ( uint128 ) ) 
                           ( notify_addr : ( address_t ) ) :
  deployXchgPair_auto_eval l tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr =
   (eval_state (Uinterpreter (deployXchgPair tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr)) l).
Proof.
  intros. proof_of (deployXchgPair_eval_P l tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr).
Qed.



End deployXchgPair.
(* ----------------------------------------- *)
Section prepare_price_state_init_and_addr.
Definition prepare_price_state_init_and_addr_exec_P (l : Ledger) ( price_data : PriceClassTypes.DPriceLRecord ) 
                                             ( price_code : TvmCells.cell ): 
{l' | l' = exec_state (Uinterpreter (prepare_price_state_init_and_addr price_data price_code)) l}.
  generate_proof (exec_expression l (prepare_price_state_init_and_addr price_data price_code)).
Defined.
Definition prepare_price_state_init_and_addr_auto_exec (l : Ledger) ( price_data : PriceClassTypes.DPriceLRecord ) 
                                             ( price_code : TvmCells.cell ): Ledger.
intros. term_of (prepare_price_state_init_and_addr_exec_P l price_data price_code).
Defined.
Theorem prepare_price_state_init_and_addr_exec_proof_next (l : Ledger) ( price_data : PriceClassTypes.DPriceLRecord ) 
                                             ( price_code : TvmCells.cell ) :
  prepare_price_state_init_and_addr_auto_exec l price_data price_code =
  exec_state (Uinterpreter (prepare_price_state_init_and_addr price_data price_code)) l.
Proof.
  intros. proof_of (prepare_price_state_init_and_addr_exec_P l price_data price_code).
Qed.
Definition prepare_price_state_init_and_addr_eval_P (l : Ledger) ( price_data : PriceClassTypes.DPriceLRecord ) 
                                             ( price_code : TvmCells.cell ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_price_state_init_and_addr price_data price_code)) l)}.
  generate_proof (eval_expression l (prepare_price_state_init_and_addr price_data price_code)).
Defined.
Definition prepare_price_state_init_and_addr_auto_eval (l : Ledger) ( price_data : PriceClassTypes.DPriceLRecord ) 
                                             ( price_code : TvmCells.cell ): (StateInitLRecord # uint256).
intros. term_of (prepare_price_state_init_and_addr_eval_P l price_data price_code).
Defined.
Theorem prepare_price_state_init_and_addr_eval_proof_next (l : Ledger) ( price_data : PriceClassTypes.DPriceLRecord ) 
                                             ( price_code : TvmCells.cell ) :
  prepare_price_state_init_and_addr_auto_eval l price_data price_code =
  toValue (eval_state (Uinterpreter (prepare_price_state_init_and_addr price_data price_code)) l).
Proof.
  intros. proof_of (prepare_price_state_init_and_addr_eval_P l price_data price_code).
Qed.

End prepare_price_state_init_and_addr.

(* ----------------------------------------- *)
Section preparePrice.
Definition preparePrice_exec_P (l : Ledger) (price min_amount : uint128 ) (deals_limit : uint8 )
                        (tip3_code: TvmCells.cell  )
                        (tip3cfg: Tip3ConfigLRecord ) (price_code: TvmCells.cell  )
                        (notify_addr: address  ): 
{l' | l' = exec_state (Uinterpreter (preparePrice price min_amount deals_limit tip3_code tip3cfg price_code notify_addr)) l}.
  generate_proof (exec_expression l (preparePrice price min_amount deals_limit tip3_code tip3cfg price_code notify_addr)).
Defined.
Definition preparePrice_auto_exec (l : Ledger) (price min_amount : uint128 ) (deals_limit : uint8 )
                        (tip3_code: TvmCells.cell  )
                        (tip3cfg: Tip3ConfigLRecord ) (price_code: TvmCells.cell  )
                        (notify_addr: address  ): Ledger.
intros. term_of (preparePrice_exec_P l price min_amount deals_limit tip3_code tip3cfg price_code notify_addr).
Defined.
Theorem preparePrice_exec_proof_next (l : Ledger) (price min_amount : uint128 ) (deals_limit : uint8 )
                        (tip3_code: TvmCells.cell  )
                        (tip3cfg: Tip3ConfigLRecord ) (price_code: TvmCells.cell  )
                        (notify_addr: address  ) :
  preparePrice_auto_exec l price min_amount deals_limit tip3_code tip3cfg price_code notify_addr =
  exec_state (Uinterpreter (preparePrice price min_amount deals_limit tip3_code tip3cfg price_code notify_addr)) l.
Proof.
  intros. proof_of (preparePrice_exec_P l price min_amount deals_limit tip3_code tip3cfg price_code notify_addr).
Qed.
Definition preparePrice_eval_P (l : Ledger) (price min_amount : uint128 ) (deals_limit : uint8 )
                        (tip3_code: TvmCells.cell  )
                        (tip3cfg: Tip3ConfigLRecord ) (price_code: TvmCells.cell  )
                        (notify_addr: address  ): 
{v | v = toValue (eval_state (Uinterpreter (preparePrice price min_amount deals_limit tip3_code tip3cfg price_code notify_addr)) l)}.
  generate_proof (eval_expression l (preparePrice price min_amount deals_limit tip3_code tip3cfg price_code notify_addr)).
Defined.
Definition preparePrice_auto_eval (l : Ledger) (price min_amount : uint128 ) (deals_limit : uint8 )
                        (tip3_code: TvmCells.cell  )
                        (tip3cfg: Tip3ConfigLRecord ) (price_code: TvmCells.cell  )
                        (notify_addr: address  ): (StateInitLRecord # (address # uint256)).
intros. term_of (preparePrice_eval_P l price min_amount deals_limit tip3_code tip3cfg price_code notify_addr).
Defined.
Theorem preparePrice_eval_proof_next (l : Ledger) (price min_amount : uint128 ) (deals_limit : uint8 )
                        (tip3_code: TvmCells.cell  )
                        (tip3cfg: Tip3ConfigLRecord ) (price_code: TvmCells.cell  )
                        (notify_addr: address  ) :
  preparePrice_auto_eval l price min_amount deals_limit tip3_code tip3cfg price_code notify_addr =
  toValue (eval_state (Uinterpreter (preparePrice price min_amount deals_limit tip3_code tip3cfg price_code notify_addr)) l).
Proof.
  intros. proof_of (preparePrice_eval_P l price min_amount deals_limit tip3_code tip3cfg price_code notify_addr).
Qed.

End preparePrice.
(* ----------------------------------------- *)
(* ----------------------------------------- *)
Section deployPriceWithSell.
Definition deployPriceWithSell_exec_P (l : Ledger) ( price : ( uint128 ) ) 
( amount : ( uint128 ) ) 
( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) 
( tons_value : ( uint128 ) ) 
( price_code : ( TvmCells.cell ) ) 
( my_tip3_addr : ( address ) ) 
( receive_wallet : ( address ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ): 
{l' | l' = exec_state (Uinterpreter (deployPriceWithSell price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr)) l}.
  generate_proof (exec_expression l (deployPriceWithSell price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr)).
Defined.
Definition deployPriceWithSell_auto_exec (l : Ledger) ( price : ( uint128 ) ) 
( amount : ( uint128 ) ) 
( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) 
( tons_value : ( uint128 ) ) 
( price_code : ( TvmCells.cell ) ) 
( my_tip3_addr : ( address ) ) 
( receive_wallet : ( address ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ): Ledger.
intros. term_of (deployPriceWithSell_exec_P l price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr).
Defined.
Theorem deployPriceWithSell_exec_proof_next (l : Ledger) ( price : ( uint128 ) ) 
( amount : ( uint128 ) ) 
( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) 
( tons_value : ( uint128 ) ) 
( price_code : ( TvmCells.cell ) ) 
( my_tip3_addr : ( address ) ) 
( receive_wallet : ( address ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ) :
  deployPriceWithSell_auto_exec l price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr =
  exec_state (Uinterpreter (deployPriceWithSell price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr)) l.
Proof.
  intros. proof_of (deployPriceWithSell_exec_P l price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr).
Qed.

(* TODO eval true *)

Definition deployPriceWithSell_eval_P (l : Ledger) ( price : ( uint128 ) ) 
( amount : ( uint128 ) ) 
( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) 
( tons_value : ( uint128 ) ) 
( price_code : ( TvmCells.cell ) ) 
( my_tip3_addr : ( address ) ) 
( receive_wallet : ( address ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ): 
{v | v =  (eval_state (Uinterpreter (deployPriceWithSell price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr)) l)}.
  generate_proof (eval_expression l (deployPriceWithSell price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr)).
Defined.
Definition deployPriceWithSell_auto_eval (l : Ledger) ( price : ( uint128 ) ) 
( amount : ( uint128 ) ) 
( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) 
( tons_value : ( uint128 ) ) 
( price_code : ( TvmCells.cell ) ) 
( my_tip3_addr : ( address ) ) 
( receive_wallet : ( address ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ): ControlResult address true.
intros. term_of (deployPriceWithSell_eval_P l price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr).
Defined.
Theorem deployPriceWithSell_eval_proof_next (l : Ledger) ( price : ( uint128 ) ) 
( amount : ( uint128 ) ) 
( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) 
( tons_value : ( uint128 ) ) 
( price_code : ( TvmCells.cell ) ) 
( my_tip3_addr : ( address ) ) 
( receive_wallet : ( address ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ) :
  deployPriceWithSell_auto_eval l price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr =
   (eval_state (Uinterpreter (deployPriceWithSell price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr)) l).
Proof.
  intros. proof_of (deployPriceWithSell_eval_P l price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr).
Qed.

End deployPriceWithSell.
(* ----------------------------------------- *)
Section deployPriceWithBuy.
Definition deployPriceWithBuy_exec_P (l : Ledger) ( price : ( uint128 ) ) ( amount : ( uint128 ) ) 
( order_finish_time : ( uint32 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( deploy_value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address_t ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ): 
{l' | l' = exec_state (Uinterpreter (deployPriceWithBuy price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr)) l}.
  generate_proof (exec_expression l (deployPriceWithBuy price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr)).
Defined.
Definition deployPriceWithBuy_auto_exec (l : Ledger) ( price : ( uint128 ) ) ( amount : ( uint128 ) ) 
( order_finish_time : ( uint32 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( deploy_value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address_t ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ): Ledger.
intros. term_of (deployPriceWithBuy_exec_P l price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr).
Defined.
Theorem deployPriceWithBuy_exec_proof_next (l : Ledger) ( price : ( uint128 ) ) ( amount : ( uint128 ) ) 
( order_finish_time : ( uint32 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( deploy_value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address_t ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ) :
  deployPriceWithBuy_auto_exec l price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr =
  exec_state (Uinterpreter (deployPriceWithBuy price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr)) l.
Proof.
  intros. proof_of (deployPriceWithBuy_exec_P l price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr).
Qed.

(* TODO eval true *)
Definition deployPriceWithBuy_eval_P (l : Ledger) ( price : ( uint128 ) ) ( amount : ( uint128 ) ) 
( order_finish_time : ( uint32 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( deploy_value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address_t ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ): 
{v | v =  (eval_state (Uinterpreter (deployPriceWithBuy price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr)) l)}.
  generate_proof (eval_expression l (deployPriceWithBuy price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr)).
Defined.
Definition deployPriceWithBuy_auto_eval (l : Ledger) ( price : ( uint128 ) ) ( amount : ( uint128 ) ) 
( order_finish_time : ( uint32 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( deploy_value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address_t ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ): ControlResult address true.
intros. term_of (deployPriceWithBuy_eval_P l price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr).
Defined.
Theorem deployPriceWithBuy_eval_proof_next (l : Ledger) ( price : ( uint128 ) ) ( amount : ( uint128 ) ) 
( order_finish_time : ( uint32 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( deploy_value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address_t ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ) :
  deployPriceWithBuy_auto_eval l price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr =
   (eval_state (Uinterpreter (deployPriceWithBuy price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr)) l).
Proof.
  intros. proof_of (deployPriceWithBuy_eval_P l price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr).
Qed.

End deployPriceWithBuy.
(* ----------------------------------------- *)
Section cancelSellOrder.
Definition cancelSellOrder_exec_P (l : Ledger) ( price : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ): 
{l' | l' = exec_state (Uinterpreter (cancelSellOrder price min_amount deals_limit value price_code tip3cfg notify_addr)) l}.
  generate_proof (exec_expression l (cancelSellOrder price min_amount deals_limit value price_code tip3cfg notify_addr)).
Defined.
Definition cancelSellOrder_auto_exec (l : Ledger) ( price : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ): Ledger.
intros. term_of (cancelSellOrder_exec_P l price min_amount deals_limit value price_code tip3cfg notify_addr).
Defined.
Theorem cancelSellOrder_exec_proof_next (l : Ledger) ( price : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ) :
  cancelSellOrder_auto_exec l price min_amount deals_limit value price_code tip3cfg notify_addr =
  exec_state (Uinterpreter (cancelSellOrder price min_amount deals_limit value price_code tip3cfg notify_addr)) l.
Proof.
  intros. proof_of (cancelSellOrder_exec_P l price min_amount deals_limit value price_code tip3cfg notify_addr).
Qed.
(* no eval *) 
End cancelSellOrder.
(* ----------------------------------------- *)
Section cancelBuyOrder.
Definition cancelBuyOrder_exec_P (l : Ledger) ( price : ( uint128 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) ( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ): 
{l' | l' = exec_state (Uinterpreter (cancelBuyOrder price min_amount deals_limit value price_code tip3cfg notify_addr)) l}.
  generate_proof (exec_expression l (cancelBuyOrder price min_amount deals_limit value price_code tip3cfg notify_addr)).
Defined.
Definition cancelBuyOrder_auto_exec (l : Ledger) ( price : ( uint128 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) ( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ): Ledger.
intros. term_of (cancelBuyOrder_exec_P l price min_amount deals_limit value price_code tip3cfg notify_addr).
Defined.
Theorem cancelBuyOrder_exec_proof_next (l : Ledger) ( price : ( uint128 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( value : ( uint128 ) ) ( price_code : ( TvmCells.cell ) ) ( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ) :
  cancelBuyOrder_auto_exec l price min_amount deals_limit value price_code tip3cfg notify_addr =
  exec_state (Uinterpreter (cancelBuyOrder price min_amount deals_limit value price_code tip3cfg notify_addr)) l.
Proof.
  intros. proof_of (cancelBuyOrder_exec_P l price min_amount deals_limit value price_code tip3cfg notify_addr).
Qed.
(* no eval *)
End cancelBuyOrder.
(* ----------------------------------------- *)
Section prepare_price_xchg_state_init_and_addr.
Definition prepare_price_xchg_state_init_and_addr_exec_P (l : Ledger) ( price_data : PriceXchgClassTypesModule.DPriceXchgLRecord ) 
                                             ( price_code : TvmCells.cell ): 
{l' | l' = exec_state (Uinterpreter (prepare_price_xchg_state_init_and_addr price_data price_code)) l}.
  generate_proof (exec_expression l (prepare_price_xchg_state_init_and_addr price_data price_code)).
Defined.
Definition prepare_price_xchg_state_init_and_addr_auto_exec (l : Ledger) ( price_data : PriceXchgClassTypesModule.DPriceXchgLRecord ) 
                                             ( price_code : TvmCells.cell ): Ledger.
intros. term_of (prepare_price_xchg_state_init_and_addr_exec_P l price_data price_code).
Defined.
Theorem prepare_price_xchg_state_init_and_addr_exec_proof_next (l : Ledger) ( price_data : PriceXchgClassTypesModule.DPriceXchgLRecord ) 
                                             ( price_code : TvmCells.cell ) :
  prepare_price_xchg_state_init_and_addr_auto_exec l price_data price_code =
  exec_state (Uinterpreter (prepare_price_xchg_state_init_and_addr price_data price_code)) l.
Proof.
  intros. proof_of (prepare_price_xchg_state_init_and_addr_exec_P l price_data price_code).
Qed.
Definition prepare_price_xchg_state_init_and_addr_eval_P (l : Ledger) ( price_data : PriceXchgClassTypesModule.DPriceXchgLRecord ) 
                                             ( price_code : TvmCells.cell ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_price_xchg_state_init_and_addr price_data price_code)) l)}.
  generate_proof (eval_expression l (prepare_price_xchg_state_init_and_addr price_data price_code)).
Defined.
Definition prepare_price_xchg_state_init_and_addr_auto_eval (l : Ledger) ( price_data : PriceXchgClassTypesModule.DPriceXchgLRecord ) 
                                             ( price_code : TvmCells.cell ): (StateInitLRecord # uint256).
intros. term_of (prepare_price_xchg_state_init_and_addr_eval_P l price_data price_code).
Defined.
Theorem prepare_price_xchg_state_init_and_addr_eval_proof_next (l : Ledger) ( price_data : PriceXchgClassTypesModule.DPriceXchgLRecord ) 
                                             ( price_code : TvmCells.cell ) :
  prepare_price_xchg_state_init_and_addr_auto_eval l price_data price_code =
  toValue (eval_state (Uinterpreter (prepare_price_xchg_state_init_and_addr price_data price_code)) l).
Proof.
  intros. proof_of (prepare_price_xchg_state_init_and_addr_eval_P l price_data price_code).
Qed.
End prepare_price_xchg_state_init_and_addr.
(* ----------------------------------------- *)
Section preparePriceXchg.
Definition preparePriceXchg_exec_P (l : Ledger) ( price_num : ( uint128 ) ) 
( price_denum : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( major_tip3cfg : ( Tip3ConfigLRecord ) ) 
( minor_tip3cfg : ( Tip3ConfigLRecord ) ) ( price_code : ( TvmCells.cell ) )
 ( notify_addr : ( address ) ) : 
{l' | l' = exec_state (Uinterpreter (preparePriceXchg price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr)) l}.
  generate_proof (exec_expression l (preparePriceXchg price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr)).
Defined.
Definition preparePriceXchg_auto_exec (l : Ledger) ( price_num : ( uint128 ) ) 
( price_denum : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( major_tip3cfg : ( Tip3ConfigLRecord ) ) 
( minor_tip3cfg : ( Tip3ConfigLRecord ) ) ( price_code : ( TvmCells.cell ) )
 ( notify_addr : ( address ) ) : Ledger.
intros. term_of (preparePriceXchg_exec_P l price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr).
Defined.
Theorem preparePriceXchg_exec_proof_next (l : Ledger) ( price_num : ( uint128 ) ) 
( price_denum : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( major_tip3cfg : ( Tip3ConfigLRecord ) ) 
( minor_tip3cfg : ( Tip3ConfigLRecord ) ) ( price_code : ( TvmCells.cell ) )
 ( notify_addr : ( address ) )  :
  preparePriceXchg_auto_exec l price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr =
  exec_state (Uinterpreter (preparePriceXchg price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr)) l.
Proof.
  intros. proof_of (preparePriceXchg_exec_P l price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr).
Qed.
(* TODO eval true *)
Definition preparePriceXchg_eval_P (l : Ledger) ( price_num : ( uint128 ) ) 
( price_denum : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( major_tip3cfg : ( Tip3ConfigLRecord ) ) 
( minor_tip3cfg : ( Tip3ConfigLRecord ) ) ( price_code : ( TvmCells.cell ) )
 ( notify_addr : ( address ) ) : 
{v | v =  (eval_state (Uinterpreter (preparePriceXchg price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr)) l)}.
  generate_proof (eval_expression l (preparePriceXchg price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr)).
Defined.
Definition preparePriceXchg_auto_eval (l : Ledger) ( price_num : ( uint128 ) ) 
( price_denum : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( major_tip3cfg : ( Tip3ConfigLRecord ) ) 
( minor_tip3cfg : ( Tip3ConfigLRecord ) ) ( price_code : ( TvmCells.cell ) )
 ( notify_addr : ( address_t ) ) : ControlResult ( StateInitLRecord # ( address # uint256 ) ) true.
intros. term_of (preparePriceXchg_eval_P l price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr).
Defined.
Theorem preparePriceXchg_eval_proof_next (l : Ledger) ( price_num : ( uint128 ) ) 
( price_denum : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( major_tip3cfg : ( Tip3ConfigLRecord ) ) 
( minor_tip3cfg : ( Tip3ConfigLRecord ) ) ( price_code : ( TvmCells.cell ) )
 ( notify_addr : ( address_t ) )  :
  preparePriceXchg_auto_eval l price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr =
   (eval_state (Uinterpreter (preparePriceXchg price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr)) l).
Proof.
  intros. proof_of (preparePriceXchg_eval_P l price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr).
Qed. 
End preparePriceXchg.
(* ----------------------------------------- *)
Section deployPriceXchg.
Definition deployPriceXchg_exec_P (l : Ledger) ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( amount : ( uint128 ) ) ( lend_amount : ( uint128 ) ) ( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( tons_value : ( uint128 ) ) 
( xchg_price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address ) ) ( receive_wallet : ( address ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ): 
{l' | l' = exec_state (Uinterpreter (deployPriceXchg sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr)) l}.
  generate_proof (exec_expression l (deployPriceXchg sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr)).
Defined.
Definition deployPriceXchg_auto_exec (l : Ledger) ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( amount : ( uint128 ) ) ( lend_amount : ( uint128 ) ) ( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( tons_value : ( uint128 ) ) 
( xchg_price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address ) ) ( receive_wallet : ( address ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ): Ledger.
intros. term_of (deployPriceXchg_exec_P l sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr).
Defined.
Theorem deployPriceXchg_exec_proof_next (l : Ledger) ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( amount : ( uint128 ) ) ( lend_amount : ( uint128 ) ) ( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( tons_value : ( uint128 ) ) 
( xchg_price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address ) ) ( receive_wallet : ( address ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ) :
  deployPriceXchg_auto_exec l sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr =
  exec_state (Uinterpreter (deployPriceXchg sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr)) l.
Proof.
  intros. proof_of (deployPriceXchg_exec_P l sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr).
Qed.
(* TODO eval true *)
Definition deployPriceXchg_eval_P (l : Ledger) ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( amount : ( uint128 ) ) ( lend_amount : ( uint128 ) ) ( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( tons_value : ( uint128 ) ) 
( xchg_price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address ) ) ( receive_wallet : ( address ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ): 
{v | v =  (eval_state (Uinterpreter (deployPriceXchg sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr)) l)}.
  generate_proof (eval_expression l (deployPriceXchg sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr)).
Defined.
Definition deployPriceXchg_auto_eval (l : Ledger) ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( amount : ( uint128 ) ) ( lend_amount : ( uint128 ) ) ( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( tons_value : ( uint128 ) ) 
( xchg_price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address ) ) ( receive_wallet : ( address ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ): ControlResult address true.
intros. term_of (deployPriceXchg_eval_P l sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr).
Defined.
Theorem deployPriceXchg_eval_proof_next (l : Ledger) ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( amount : ( uint128 ) ) ( lend_amount : ( uint128 ) ) ( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( tons_value : ( uint128 ) ) 
( xchg_price_code : ( TvmCells.cell ) ) ( my_tip3_addr : ( address ) ) ( receive_wallet : ( address ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address ) ) :
  deployPriceXchg_auto_eval l sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr =
   (eval_state (Uinterpreter (deployPriceXchg sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr)) l).
Proof.
  intros. proof_of (deployPriceXchg_eval_P l sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr).
Qed.
End deployPriceXchg.
(* ----------------------------------------- *)
Section cancelXchgOrder.
Definition cancelXchgOrder_exec_P (l : Ledger) ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( value : ( uint128 ) ) ( xchg_price_code : ( TvmCells.cell ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address_t ) ): 
{l' | l' = exec_state (Uinterpreter (cancelXchgOrder sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr)) l}.
  generate_proof (exec_expression l (cancelXchgOrder sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr)).
Defined.
Definition cancelXchgOrder_auto_exec (l : Ledger) ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( value : ( uint128 ) ) ( xchg_price_code : ( TvmCells.cell ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address_t ) ): Ledger.
intros. term_of (cancelXchgOrder_exec_P l sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr).
Defined.
Theorem cancelXchgOrder_exec_proof_next (l : Ledger) ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( value : ( uint128 ) ) ( xchg_price_code : ( TvmCells.cell ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address_t ) ) :
  cancelXchgOrder_auto_exec l sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr =
  exec_state (Uinterpreter (cancelXchgOrder sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr)) l.
Proof.
  intros. proof_of (cancelXchgOrder_exec_P l sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr).
Qed.
(* no eval *)
End cancelXchgOrder.
(* ----------------------------------------- *)
Section transfer.
Definition transfer_exec_P (l : Ledger) ( dest : ( address_t ) ) ( value : ( uint128 ) ) ( bounce : ( XBool ) ): 
{l' | l' = exec_state (Uinterpreter (transfer dest value bounce)) l}.
  generate_proof (exec_expression l (transfer dest value bounce)).
Defined.
Definition transfer_auto_exec (l : Ledger) ( dest : ( address_t ) ) ( value : ( uint128 ) ) ( bounce : ( XBool ) ): Ledger.
intros. term_of (transfer_exec_P l dest value bounce).
Defined.
Theorem transfer_exec_proof_next (l : Ledger) ( dest : ( address_t ) ) ( value : ( uint128 ) ) ( bounce : ( XBool ) ) :
  transfer_auto_exec l dest value bounce =
  exec_state (Uinterpreter (transfer dest value bounce)) l.
Proof.
  intros. proof_of (transfer_exec_P l dest value bounce).
Qed.
(* no eval*)
End transfer.
(* ----------------------------------------- *)
Section prepare_wallet_state_init_and_addr.
Definition prepare_wallet_state_init_and_addr_exec_P (l : Ledger) (wallet_data : TonsConfigFields ): 
{l' | l' = exec_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l}.
  generate_proof (exec_expression l (prepare_wallet_state_init_and_addr wallet_data)).
Defined.
Definition prepare_wallet_state_init_and_addr_auto_exec (l : Ledger) (wallet_data : TonsConfigFields ): Ledger.
intros. term_of (prepare_wallet_state_init_and_addr_exec_P l wallet_data).
Defined.
Theorem prepare_wallet_state_init_and_addr_exec_proof_next (l : Ledger) (wallet_data : TonsConfigFields ) :
  prepare_wallet_state_init_and_addr_auto_exec l wallet_data =
  exec_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l.
Proof.
  intros. proof_of (prepare_wallet_state_init_and_addr_exec_P l wallet_data).
Qed.
Definition prepare_wallet_state_init_and_addr_eval_P (l : Ledger) (wallet_data : TonsConfigFields ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l)}.
  generate_proof (eval_expression l (prepare_wallet_state_init_and_addr wallet_data)).
Defined.
Definition prepare_wallet_state_init_and_addr_auto_eval (l : Ledger) (wallet_data : TonsConfigFields ): ( StateInitLRecord # uint256 ).
intros. term_of (prepare_wallet_state_init_and_addr_eval_P l wallet_data).
Defined.
Theorem prepare_wallet_state_init_and_addr_eval_proof_next (l : Ledger) (wallet_data : TonsConfigFields ) :
  prepare_wallet_state_init_and_addr_auto_eval l wallet_data =
  toValue (eval_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l).
Proof.
  intros. proof_of (prepare_wallet_state_init_and_addr_eval_P l wallet_data).
Qed.
End prepare_wallet_state_init_and_addr.
(* ----------------------------------------- *)
Section prepare_wrapper_state_init_and_addr.
Definition prepare_wrapper_state_init_and_addr_exec_P (l : Ledger) ( wrapper_code : TvmCells.cell ) 
                                               ( wrapper_data : WrapperClassTypesModule.DWrapperLRecord ): 
{l' | l' = exec_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l}.
  generate_proof (exec_expression l (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)).
Defined.
Definition prepare_wrapper_state_init_and_addr_auto_exec (l : Ledger) ( wrapper_code : TvmCells.cell ) 
                                               ( wrapper_data : WrapperClassTypesModule.DWrapperLRecord ): Ledger.
intros. term_of (prepare_wrapper_state_init_and_addr_exec_P l wrapper_code wrapper_data).
Defined.
Theorem prepare_wrapper_state_init_and_addr_exec_proof_next (l : Ledger) ( wrapper_code : TvmCells.cell ) 
                                               ( wrapper_data : WrapperClassTypesModule.DWrapperLRecord ) :
  prepare_wrapper_state_init_and_addr_auto_exec l wrapper_code wrapper_data =
  exec_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l.
Proof.
  intros. proof_of (prepare_wrapper_state_init_and_addr_exec_P l wrapper_code wrapper_data).
Qed.
Definition prepare_wrapper_state_init_and_addr_eval_P (l : Ledger) ( wrapper_code : TvmCells.cell ) 
                                               ( wrapper_data : WrapperClassTypesModule.DWrapperLRecord ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l)}.
  generate_proof (eval_expression l (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)).
Defined.
Definition prepare_wrapper_state_init_and_addr_auto_eval (l : Ledger) ( wrapper_code : TvmCells.cell ) 
                                               ( wrapper_data : WrapperClassTypesModule.DWrapperLRecord ): (StateInitLRecord # uint256).
intros. term_of (prepare_wrapper_state_init_and_addr_eval_P l wrapper_code wrapper_data).
Defined.
Theorem prepare_wrapper_state_init_and_addr_eval_proof_next (l : Ledger) ( wrapper_code : TvmCells.cell ) 
                                               ( wrapper_data : WrapperClassTypesModule.DWrapperLRecord ) :
  prepare_wrapper_state_init_and_addr_auto_eval l wrapper_code wrapper_data =
  toValue (eval_state (Uinterpreter (prepare_wrapper_state_init_and_addr wrapper_code wrapper_data)) l).
Proof.
  intros. proof_of (prepare_wrapper_state_init_and_addr_eval_P l wrapper_code wrapper_data).
Qed.
End prepare_wrapper_state_init_and_addr.
(* ----------------------------------------- *)
Section prepare_internal_wallet_state_init_and_addr.
Definition prepare_internal_wallet_state_init_and_addr_exec_P (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  ( uint8 ) )
 ( root_public_key :  ( uint256 ) )
 ( wallet_public_key :  ( uint256 ) ) 
( root_address :  ( address ) ) 
( owner_address :  ( XMaybe address ) ) 
( code :  ( TvmCells.cell ) ) 
( workchain_id :  ( int ) ) : 
{l' | l' = exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )) l}.
  generate_proof (exec_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_exec (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  ( uint8 ) )
 ( root_public_key :  ( uint256 ) )
 ( wallet_public_key :  ( uint256 ) ) 
( root_address :  ( address ) ) 
( owner_address :  ( XMaybe address ) ) 
( code :  ( TvmCells.cell ) ) 
( workchain_id :  ( int ) ) : Ledger.
intros. term_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  ( uint8 ) )
 ( root_public_key :  ( uint256 ) )
 ( wallet_public_key :  ( uint256 ) ) 
( root_address :  ( address ) ) 
( owner_address :  ( XMaybe address ) ) 
( code :  ( TvmCells.cell ) ) 
( workchain_id :  ( int ) )  :
  prepare_internal_wallet_state_init_and_addr_auto_exec l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id  =
  exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )) l.
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ).
Qed.
Definition prepare_internal_wallet_state_init_and_addr_eval_P (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  ( uint8 ) )
 ( root_public_key :  ( uint256 ) )
 ( wallet_public_key :  ( uint256 ) ) 
( root_address :  ( address ) ) 
( owner_address :  ( XMaybe address ) ) 
( code :  ( TvmCells.cell ) ) 
( workchain_id :  ( int ) ) : 
{v | v = toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )) l)}.
  generate_proof (eval_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_eval (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  ( uint8 ) )
 ( root_public_key :  ( uint256 ) )
 ( wallet_public_key :  ( uint256 ) ) 
( root_address :  ( address ) ) 
( owner_address :  ( XMaybe address ) ) 
( code :  ( TvmCells.cell ) ) 
( workchain_id :  ( int ) ) : ( StateInitLRecord * uint256 ).
intros. term_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  ( uint8 ) )
 ( root_public_key :  ( uint256 ) )
 ( wallet_public_key :  ( uint256 ) ) 
( root_address :  ( address ) ) 
( owner_address :  ( XMaybe address ) ) 
( code :  ( TvmCells.cell ) ) 
( workchain_id :  ( int ) )  :
  prepare_internal_wallet_state_init_and_addr_auto_eval l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id  =
  toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id )) l).
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ).
Qed.
End prepare_internal_wallet_state_init_and_addr.
(* ----------------------------------------- *)
Section deployEmptyFlexWallet.
Definition deployEmptyFlexWallet_exec_P (l : Ledger) ( pubkey : ( uint256 ) ) ( tons_to_wallet : ( uint128 ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ): 
{l' | l' = exec_state (Uinterpreter (deployEmptyFlexWallet pubkey tons_to_wallet tip3cfg)) l}.
  generate_proof (exec_expression l (deployEmptyFlexWallet pubkey tons_to_wallet tip3cfg)).
Defined.
Definition deployEmptyFlexWallet_auto_exec (l : Ledger) ( pubkey : ( uint256 ) ) ( tons_to_wallet : ( uint128 ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ): Ledger.
intros. term_of (deployEmptyFlexWallet_exec_P l pubkey tons_to_wallet tip3cfg).
Defined.
Theorem deployEmptyFlexWallet_exec_proof_next (l : Ledger) ( pubkey : ( uint256 ) ) ( tons_to_wallet : ( uint128 ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) :
  deployEmptyFlexWallet_auto_exec l pubkey tons_to_wallet tip3cfg =
  exec_state (Uinterpreter (deployEmptyFlexWallet pubkey tons_to_wallet tip3cfg)) l.
Proof.
  intros. proof_of (deployEmptyFlexWallet_exec_P l pubkey tons_to_wallet tip3cfg).
Qed.
(* TODO eval true *)
Definition deployEmptyFlexWallet_eval_P (l : Ledger) ( pubkey : ( uint256 ) ) ( tons_to_wallet : ( uint128 ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ): 
{v | v =  (eval_state (Uinterpreter (deployEmptyFlexWallet pubkey tons_to_wallet tip3cfg)) l)}.
  generate_proof (eval_expression l (deployEmptyFlexWallet pubkey tons_to_wallet tip3cfg)).
Defined.
Definition deployEmptyFlexWallet_auto_eval (l : Ledger) ( pubkey : ( uint256 ) ) ( tons_to_wallet : ( uint128 ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ): ControlResult address true.
intros. term_of (deployEmptyFlexWallet_eval_P l pubkey tons_to_wallet tip3cfg).
Defined.
Theorem deployEmptyFlexWallet_eval_proof_next (l : Ledger) ( pubkey : ( uint256 ) ) ( tons_to_wallet : ( uint128 ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) :
  deployEmptyFlexWallet_auto_eval l pubkey tons_to_wallet tip3cfg =
   (eval_state (Uinterpreter (deployEmptyFlexWallet pubkey tons_to_wallet tip3cfg)) l).
Proof.
  intros. proof_of (deployEmptyFlexWallet_eval_P l pubkey tons_to_wallet tip3cfg).
Qed.
End deployEmptyFlexWallet.
(* ----------------------------------------- *)
Section burnWallet.
Definition burnWallet_exec_P (l : Ledger) ( tons_value : ( uint128 ) ) ( out_pubkey : ( uint256 ) ) 
( out_internal_owner : ( address_t ) ) ( my_tip3_addr : ( address_t ) ): 
{l' | l' = exec_state (Uinterpreter (burnWallet tons_value out_pubkey out_internal_owner my_tip3_addr)) l}.
  generate_proof (exec_expression l (burnWallet tons_value out_pubkey out_internal_owner my_tip3_addr)).
Defined.
Definition burnWallet_auto_exec (l : Ledger) ( tons_value : ( uint128 ) ) ( out_pubkey : ( uint256 ) ) 
( out_internal_owner : ( address_t ) ) ( my_tip3_addr : ( address_t ) ): Ledger.
intros. term_of (burnWallet_exec_P l tons_value out_pubkey out_internal_owner my_tip3_addr).
Defined.
Theorem burnWallet_exec_proof_next (l : Ledger) ( tons_value : ( uint128 ) ) ( out_pubkey : ( uint256 ) ) 
( out_internal_owner : ( address_t ) ) ( my_tip3_addr : ( address_t ) ) :
  burnWallet_auto_exec l tons_value out_pubkey out_internal_owner my_tip3_addr =
  exec_state (Uinterpreter (burnWallet tons_value out_pubkey out_internal_owner my_tip3_addr)) l.
Proof.
  intros. proof_of (burnWallet_exec_P l tons_value out_pubkey out_internal_owner my_tip3_addr).
Qed.
(* no eval *)
End burnWallet.
(* ----------------------------------------- *)
Section registerWrapper.
Definition registerWrapper_exec_P (l : Ledger) ( wrapper_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3cfg : ( Tip3ConfigLRecord ) ): 
{l' | l' = exec_state (Uinterpreter (registerWrapper wrapper_pubkey value tip3cfg)) l}.
  generate_proof (exec_expression l (registerWrapper wrapper_pubkey value tip3cfg)).
Defined.
Definition registerWrapper_auto_exec (l : Ledger) ( wrapper_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3cfg : ( Tip3ConfigLRecord ) ): Ledger.
intros. term_of (registerWrapper_exec_P l wrapper_pubkey value tip3cfg).
Defined.
Theorem registerWrapper_exec_proof_next (l : Ledger) ( wrapper_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3cfg : ( Tip3ConfigLRecord ) ) :
  registerWrapper_auto_exec l wrapper_pubkey value tip3cfg =
  exec_state (Uinterpreter (registerWrapper wrapper_pubkey value tip3cfg)) l.
Proof.
  intros. proof_of (registerWrapper_exec_P l wrapper_pubkey value tip3cfg).
Qed.
(* no eval *)
End registerWrapper.
(* ----------------------------------------- *)
Section registerTradingPair.
Definition registerTradingPair_exec_P (l : Ledger) ( request_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3_root : ( address ) ) ( min_amount : ( uint128 ) ) ( notify_addr : ( address ) ): 
{l' | l' = exec_state (Uinterpreter (registerTradingPair request_pubkey value tip3_root min_amount notify_addr )) l}.
  generate_proof (exec_expression l (registerTradingPair request_pubkey value tip3_root min_amount notify_addr )).
Defined.
Definition registerTradingPair_auto_exec (l : Ledger) ( request_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3_root : ( address ) ) ( min_amount : ( uint128 ) ) ( notify_addr : ( address ) ): Ledger.
intros. term_of (registerTradingPair_exec_P l request_pubkey value tip3_root min_amount notify_addr ).
Defined.
Theorem registerTradingPair_exec_proof_next (l : Ledger) ( request_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3_root : ( address ) ) ( min_amount : ( uint128 ) ) ( notify_addr : ( address ) ) :
  registerTradingPair_auto_exec l request_pubkey value tip3_root min_amount notify_addr  =
  exec_state (Uinterpreter (registerTradingPair request_pubkey value tip3_root min_amount notify_addr )) l.
Proof.
  intros. proof_of (registerTradingPair_exec_P l request_pubkey value tip3_root min_amount notify_addr ).
Qed.
(* no eval*)
End registerTradingPair.
(* ----------------------------------------- *)
Section registerXchgPair.
Definition registerXchgPair_exec_P (l : Ledger) ( request_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3_major_root : ( address ) ) ( tip3_minor_root : ( address ) ) ( min_amount : ( uint128 ) ) ( notify_addr : ( address ) ): 
{l' | l' = exec_state (Uinterpreter (registerXchgPair request_pubkey value tip3_major_root tip3_minor_root min_amount notify_addr)) l}.
  generate_proof (exec_expression l (registerXchgPair request_pubkey value tip3_major_root tip3_minor_root min_amount notify_addr)).
Defined.
Definition registerXchgPair_auto_exec (l : Ledger) ( request_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3_major_root : ( address ) ) ( tip3_minor_root : ( address ) ) ( min_amount : ( uint128 ) ) ( notify_addr : ( address ) ): Ledger.
intros. term_of (registerXchgPair_exec_P l request_pubkey value tip3_major_root tip3_minor_root min_amount notify_addr).
Defined.
Theorem registerXchgPair_exec_proof_next (l : Ledger) ( request_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3_major_root : ( address ) ) ( tip3_minor_root : ( address ) ) ( min_amount : ( uint128 ) ) ( notify_addr : ( address ) ) :
  registerXchgPair_auto_exec l request_pubkey value tip3_major_root tip3_minor_root min_amount notify_addr =
  exec_state (Uinterpreter (registerXchgPair request_pubkey value tip3_major_root tip3_minor_root min_amount notify_addr)) l.
Proof.
  intros. proof_of (registerXchgPair_exec_P l request_pubkey value tip3_major_root tip3_minor_root min_amount notify_addr).
Qed.
(* no eval *)
End registerXchgPair.
End EvalExecAuto.



