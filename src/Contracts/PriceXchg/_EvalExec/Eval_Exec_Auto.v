(* Require Import Coq.Program.Basics. 
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

Require Import Project.CommonAxioms.
Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.
Require Import Project.CommonNotations.
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.PriceXchg.Ledger.
Require Import Contracts.PriceXchg.Functions.FuncSig.
Require Import Contracts.PriceXchg.Functions.FuncNotations.
Require Import Contracts.PriceXchg.Functions.Funcs.
Require Contracts.PriceXchg.Interface.

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.


Module EvalExecAuto (co: CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .


Module Export FuncsModule := Funcs co dc.

Import FuncsInternal.
(* Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module Import TONTonkenWalletModuleForPriceXchg := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .
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

(***************************************************************************)		


Import URSUS_.



(* ---------------------------------------------- *)
Section minor_cost.
Definition minor_cost_exec_P (l : Ledger) (amount: uint128) (price: price_t): 
{l' | l' = exec_state (Uinterpreter (minor_cost amount price)) l}.
  generate_proof (exec_expression l (minor_cost amount price)).
Defined.
Definition minor_cost_auto_exec (l : Ledger) (amount: uint128) (price: price_t): Ledger.
intros. term_of (minor_cost_exec_P l amount price).
Defined.
Theorem minor_cost_exec_proof_next (l : Ledger) (amount: uint128) (price: price_t) :
  minor_cost_auto_exec l amount price =
  exec_state (Uinterpreter (minor_cost amount price)) l.
Proof.
  intros. proof_of (minor_cost_exec_P l amount price).
Qed.
Definition minor_cost_eval_P (l : Ledger) (amount: uint128) (price: price_t): 
{v | v =  (eval_state (Uinterpreter (minor_cost amount price)) l)}.
  generate_proof (eval_expression l (minor_cost amount price)).
Defined.
Definition minor_cost_auto_eval (l : Ledger) (amount: uint128) (price: price_t): (ControlResult (optional uint128) true).
intros. term_of (minor_cost_eval_P l amount price).
Defined.
Theorem minor_cost_eval_proof_next (l : Ledger) (amount: uint128) (price: price_t) :
  minor_cost_auto_eval l amount price =
   (eval_state (Uinterpreter (minor_cost amount price)) l).
Proof.
  intros. proof_of (minor_cost_eval_P l amount price).
Qed.
End minor_cost.
(* ----------------------------------------- *)
Section is_active_time.
Definition is_active_time_exec_P (l : Ledger) ( order_finish_time : uint32 ): 
{l' | l' = exec_state (Uinterpreter (is_active_time order_finish_time)) l}.
  generate_proof (exec_expression l (is_active_time order_finish_time)).
Defined.
Definition is_active_time_auto_exec (l : Ledger) ( order_finish_time : uint32 ): Ledger.
intros. term_of (is_active_time_exec_P l order_finish_time).
Defined.
Theorem is_active_time_exec_proof_next (l : Ledger) ( order_finish_time : uint32 ) :
  is_active_time_auto_exec l order_finish_time =
  exec_state (Uinterpreter (is_active_time order_finish_time)) l.
Proof.
  intros. proof_of (is_active_time_exec_P l order_finish_time).
Qed.
Definition is_active_time_eval_P (l : Ledger) ( order_finish_time : uint32 ): 
{v | v = toValue (eval_state (Uinterpreter (is_active_time order_finish_time)) l)}.
  generate_proof (eval_expression l (is_active_time order_finish_time)).
Defined.
Definition is_active_time_auto_eval (l : Ledger) ( order_finish_time : uint32 ): XBool.
intros. term_of (is_active_time_eval_P l order_finish_time).
Defined.
Theorem is_active_time_eval_proof_next (l : Ledger)  ( order_finish_time : uint32 ):
  is_active_time_auto_eval l  order_finish_time =
  toValue (eval_state (Uinterpreter (is_active_time order_finish_time)) l).
Proof.
  intros. proof_of (is_active_time_eval_P l order_finish_time).
Qed.
End is_active_time.
(* ----------------------------------------- *)
Section prepare_internal_wallet_state_init_and_addr.
Definition prepare_internal_wallet_state_init_and_addr_exec_P (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : cell ) 
														( workchain_id : int ): 
{l' | l' = exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l}.
  generate_proof (exec_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_exec (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : cell ) 
														( workchain_id : int ): Ledger.
intros. term_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : cell ) 
														( workchain_id : int ) :
  prepare_internal_wallet_state_init_and_addr_auto_exec l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l.
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.
Definition prepare_internal_wallet_state_init_and_addr_eval_P (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : cell ) 
														( workchain_id : int ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l)}.
  generate_proof (eval_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_eval (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : cell ) 
														( workchain_id : int ): ( StateInitLRecord * uint256 ).
intros. term_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : cell ) 
														( workchain_id : int ) :
  prepare_internal_wallet_state_init_and_addr_auto_eval l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l).
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.
End prepare_internal_wallet_state_init_and_addr.
(* ----------------------------------------- *)
Section expected_wallet_address.
Definition expected_wallet_address_exec_P (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
								   ( wallet_pubkey : uint256 ) 
								   ( internal_owner : uint256 ): 
{l' | l' = exec_state (Uinterpreter (expected_wallet_address cfg wallet_pubkey internal_owner)) l}.
  generate_proof (exec_expression l (expected_wallet_address cfg wallet_pubkey internal_owner)).
Defined.
Definition expected_wallet_address_auto_exec (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
								   ( wallet_pubkey : uint256 ) 
								   ( internal_owner : uint256 ): Ledger.
intros. term_of (expected_wallet_address_exec_P l cfg wallet_pubkey internal_owner).
Defined.
Theorem expected_wallet_addressroof_next (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
								   ( wallet_pubkey : uint256 ) 
								   ( internal_owner : uint256 ) :
  expected_wallet_address_auto_exec l cfg wallet_pubkey internal_owner =
  exec_state (Uinterpreter (expected_wallet_address  cfg wallet_pubkey internal_owner)) l.
Proof.
  intros. proof_of (expected_wallet_address_exec_P l cfg wallet_pubkey internal_owner).
Qed.
Definition expected_wallet_address_eval_P (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
								   ( wallet_pubkey : uint256 ) 
								   ( internal_owner : uint256 ): 
{v | v = toValue (eval_state (Uinterpreter (expected_wallet_address cfg wallet_pubkey internal_owner)) l)}.
  generate_proof (eval_expression l (expected_wallet_address cfg wallet_pubkey internal_owner)).
Defined.
Definition expected_wallet_address_auto_eval (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
								   ( wallet_pubkey : uint256 ) 
								   ( internal_owner : uint256 ): uint256.
intros. term_of (expected_wallet_address_eval_P l cfg wallet_pubkey internal_owner).
Defined.
Theorem expected_wallet_address_eval_proof_next (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
								   ( wallet_pubkey : uint256 ) 
								   ( internal_owner : uint256 ) :
  expected_wallet_address_auto_eval l cfg wallet_pubkey internal_owner =
  toValue (eval_state (Uinterpreter (expected_wallet_address cfg wallet_pubkey internal_owner)) l).
Proof.
  intros. proof_of (expected_wallet_address_eval_P l cfg wallet_pubkey internal_owner).
Qed.
End expected_wallet_address.
(* ----------------------------------------- *)
Section verify_tip3_addr.
Definition verify_tip3_addr_exec_P (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
							( tip3_wallet : address ) 
							( wallet_pubkey : uint256 ) 
							( internal_owner : uint256 ): 
{l' | l' = exec_state (Uinterpreter (verify_tip3_addr cfg tip3_wallet wallet_pubkey internal_owner)) l}.
  generate_proof (exec_expression l (verify_tip3_addr cfg tip3_wallet wallet_pubkey internal_owner)).
Defined.
Definition verify_tip3_addr_auto_exec (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
							( tip3_wallet : address ) 
							( wallet_pubkey : uint256 ) 
							( internal_owner : uint256 ): Ledger.
intros. term_of (verify_tip3_addr_exec_P l cfg tip3_wallet wallet_pubkey internal_owner).
Defined.
Theorem verify_tip3_addr_exec_proof_next (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
							( tip3_wallet : address ) 
							( wallet_pubkey : uint256 ) 
							( internal_owner : uint256 ) :
  verify_tip3_addr_auto_exec l cfg tip3_wallet wallet_pubkey internal_owner =
  exec_state (Uinterpreter (verify_tip3_addr cfg tip3_wallet wallet_pubkey internal_owner)) l.
Proof.
  intros. proof_of (verify_tip3_addr_exec_P l cfg tip3_wallet wallet_pubkey internal_owner).
Qed.
Definition verify_tip3_addr_eval_P (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
							( tip3_wallet : address ) 
							( wallet_pubkey : uint256 ) 
							( internal_owner : uint256 ): 
{v | v = toValue (eval_state (Uinterpreter (verify_tip3_addr cfg tip3_wallet wallet_pubkey internal_owner)) l)}.
  generate_proof (eval_expression l (verify_tip3_addr cfg tip3_wallet wallet_pubkey internal_owner)).
Defined.
Definition verify_tip3_addr_auto_eval (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
							( tip3_wallet : address ) 
							( wallet_pubkey : uint256 ) 
							( internal_owner : uint256 ): boolean.
intros. term_of (verify_tip3_addr_eval_P l cfg tip3_wallet wallet_pubkey internal_owner).
Defined.
Theorem verify_tip3_addr_eval_proof_next (l : Ledger) ( cfg : Tip3ConfigLRecord ) 
							( tip3_wallet : address ) 
							( wallet_pubkey : uint256 ) 
							( internal_owner : uint256 ) :
  verify_tip3_addr_auto_eval l cfg tip3_wallet wallet_pubkey internal_owner =
  toValue (eval_state (Uinterpreter (verify_tip3_addr cfg tip3_wallet wallet_pubkey internal_owner)) l).
Proof.
  intros. proof_of (verify_tip3_addr_eval_P l cfg tip3_wallet wallet_pubkey internal_owner).
Qed.
End verify_tip3_addr.
(* ----------------------------------------- *)
Section on_ord_fail.
Definition on_ord_fail_exec_P (l : Ledger) (ec: uint) (wallet_in : address (* ITONTokenWalletPtrLRecord *)) (amount: uint128): 
{l' | l' = exec_state (Uinterpreter (on_ord_fail ec wallet_in amount )) l}.
  generate_proof (exec_expression l (on_ord_fail ec wallet_in amount )).
Defined.
Definition on_ord_fail_auto_exec (l : Ledger) (ec: uint) (wallet_in : address (* ITONTokenWalletPtrLRecord *)) (amount: uint128): Ledger.
intros. term_of (on_ord_fail_exec_P l ec wallet_in amount ).
Defined.
Theorem on_ord_fail_exec_proof_next (l : Ledger) (ec: uint) (wallet_in : address (* ITONTokenWalletPtrLRecord *)) (amount: uint128) :
  on_ord_fail_auto_exec l ec wallet_in amount  =
  exec_state (Uinterpreter (on_ord_fail ec wallet_in amount )) l.
Proof.
  intros. proof_of (on_ord_fail_exec_P l ec wallet_in amount ).
Qed.
Definition on_ord_fail_eval_P (l : Ledger) (ec: uint) (wallet_in : address (* ITONTokenWalletPtrLRecord *)) (amount: uint128): 
{v | v = toValue (eval_state (Uinterpreter (on_ord_fail ec wallet_in amount )) l)}.
  generate_proof (eval_expression l (on_ord_fail ec wallet_in amount )).
Defined.
Definition on_ord_fail_auto_eval (l : Ledger) (ec: uint) (wallet_in : address (* ITONTokenWalletPtrLRecord *)) (amount: uint128): OrderRetLRecord.
intros. term_of (on_ord_fail_eval_P l ec wallet_in amount ).
Defined.
Theorem on_ord_fail_eval_proof_next (l : Ledger) (ec: uint) (wallet_in : address (* ITONTokenWalletPtrLRecord *)) (amount: uint128) :
  on_ord_fail_auto_eval l ec wallet_in amount  =
  toValue (eval_state (Uinterpreter (on_ord_fail ec wallet_in amount )) l).
Proof.
  intros. proof_of (on_ord_fail_eval_P l ec wallet_in amount ).
Qed.
End on_ord_fail.
(* ----------------------------------------- *)
Section process_queue_impl.
Definition process_queue_impl_exec_P (l : Ledger) ( tip3root_sell : address ) 
							  ( tip3root_buy : address ) 
							  ( notify_addr : address (* IFlexNotifyPtr *) ) 
							  ( price : price_t ) 
							  ( deals_limit : uint8 ) 
							  ( tons_cfg : TonsConfigLRecord ) 
							  ( sell_idx : uint ) 
							  ( buy_idx : uint ) 
							  ( sells_amount : uint128 ) 
							  ( sells : queue OrderInfoXchgLRecord ) 
							  ( buys_amount : uint128 ) 
							  ( buys : queue OrderInfoXchgLRecord ): 
{l' | l' = exec_state (Uinterpreter (process_queue_impl tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)) l}.
  generate_proof (exec_expression l (process_queue_impl tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)).
Defined.
Definition process_queue_impl_auto_exec (l : Ledger) ( tip3root_sell : address ) 
							  ( tip3root_buy : address ) 
							  ( notify_addr : address (* IFlexNotifyPtr *) ) 
							  ( price : price_t ) 
							  ( deals_limit : uint8 ) 
							  ( tons_cfg : TonsConfigLRecord ) 
							  ( sell_idx : uint ) 
							  ( buy_idx : uint ) 
							  ( sells_amount : uint128 ) 
							  ( sells : queue OrderInfoXchgLRecord ) 
							  ( buys_amount : uint128 ) 
							  ( buys : queue OrderInfoXchgLRecord ): Ledger.
intros. term_of (process_queue_impl_exec_P l tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys).
Defined.
Theorem process_queue_impl_exec_proof_next (l : Ledger) ( tip3root_sell : address ) 
							  ( tip3root_buy : address ) 
							  ( notify_addr : address (* IFlexNotifyPtr *) ) 
							  ( price : price_t ) 
							  ( deals_limit : uint8 ) 
							  ( tons_cfg : TonsConfigLRecord ) 
							  ( sell_idx : uint ) 
							  ( buy_idx : uint ) 
							  ( sells_amount : uint128 ) 
							  ( sells : queue OrderInfoXchgLRecord ) 
							  ( buys_amount : uint128 ) 
							  ( buys : queue OrderInfoXchgLRecord ) :
  process_queue_impl_auto_exec l tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys =
  exec_state (Uinterpreter (process_queue_impl tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)) l.
Proof.
  intros. proof_of (process_queue_impl_exec_P l tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys).
Qed.
Definition process_queue_impl_eval_P (l : Ledger) ( tip3root_sell : address ) 
							  ( tip3root_buy : address ) 
							  ( notify_addr : address (* IFlexNotifyPtr *) ) 
							  ( price : price_t ) 
							  ( deals_limit : uint8 ) 
							  ( tons_cfg : TonsConfigLRecord ) 
							  ( sell_idx : uint ) 
							  ( buy_idx : uint ) 
							  ( sells_amount : uint128 ) 
							  ( sells : queue OrderInfoXchgLRecord ) 
							  ( buys_amount : uint128 ) 
							  ( buys : queue OrderInfoXchgLRecord ): 
{v | v =  (eval_state (Uinterpreter (process_queue_impl tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)) l)}.
  generate_proof (eval_expression l (process_queue_impl tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)).
Defined.
Definition process_queue_impl_auto_eval (l : Ledger) ( tip3root_sell : address ) 
							  ( tip3root_buy : address ) 
							  ( notify_addr : address (* IFlexNotifyPtr *) ) 
							  ( price : price_t ) 
							  ( deals_limit : uint8 ) 
							  ( tons_cfg : TonsConfigLRecord ) 
							  ( sell_idx : uint ) 
							  ( buy_idx : uint ) 
							  ( sells_amount : uint128 ) 
							  ( sells : queue OrderInfoXchgLRecord ) 
							  ( buys_amount : uint128 ) 
							  ( buys : queue OrderInfoXchgLRecord ): (ControlResult process_retLRecord true).
intros. term_of (process_queue_impl_eval_P l tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys).
Defined.
Theorem process_queue_impl_eval_proof_next (l : Ledger) ( tip3root_sell : address ) 
							  ( tip3root_buy : address ) 
							  ( notify_addr : address (* IFlexNotifyPtr *) ) 
							  ( price : price_t ) 
							  ( deals_limit : uint8 ) 
							  ( tons_cfg : TonsConfigLRecord ) 
							  ( sell_idx : uint ) 
							  ( buy_idx : uint ) 
							  ( sells_amount : uint128 ) 
							  ( sells : queue OrderInfoXchgLRecord ) 
							  ( buys_amount : uint128 ) 
							  ( buys : queue OrderInfoXchgLRecord ) :
  process_queue_impl_auto_eval l tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys =
   (eval_state (Uinterpreter (process_queue_impl tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)) l).
Proof.
  intros. proof_of (process_queue_impl_eval_P l tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys).
Qed.
End process_queue_impl.
(* ----------------------------------------- *)
Section processQueue.
Definition processQueue_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (processQueue )) l}.
  generate_proof (exec_expression l (processQueue )).
Defined.
Definition processQueue_auto_exec (l : Ledger) : Ledger.
intros. term_of (processQueue_exec_P l ).
Defined.
Theorem processQueue_exec_proof_next (l : Ledger)  :
  processQueue_auto_exec l  =
  exec_state (Uinterpreter (processQueue )) l.
Proof.
  intros. proof_of (processQueue_exec_P l ).
Qed.
(* no eval *)
End processQueue.
(* ----------------------------------------- *)
Section cancelSell.
Definition cancelSell_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (cancelSell )) l}.
  generate_proof (exec_expression l (cancelSell )).
Defined.
Definition cancelSell_auto_exec (l : Ledger) : Ledger.
intros. term_of (cancelSell_exec_P l ).
Defined.
Theorem cancelSell_exec_proof_next (l : Ledger)  :
  cancelSell_auto_exec l  =
  exec_state (Uinterpreter (cancelSell )) l.
Proof.
  intros. proof_of (cancelSell_exec_P l ).
Qed.
End cancelSell.
(* ----------------------------------------- *)
Section cancelBuy.
Definition cancelBuy_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (cancelBuy )) l}.
  generate_proof (exec_expression l (cancelBuy )).
Defined.
Definition cancelBuy_auto_exec (l : Ledger) : Ledger.
intros. term_of (cancelBuy_exec_P l ).
Defined.
Theorem cancelBuy_exec_proof_next (l : Ledger)  :
  cancelBuy_auto_exec l  =
  exec_state (Uinterpreter (cancelBuy )) l.
Proof.
  intros. proof_of (cancelBuy_exec_P l ).
Qed.
End cancelBuy.
(* ----------------------------------------- *)
Section prepare_price_xchg_state_init_and_addr.
Definition prepare_price_xchg_state_init_and_addr_exec_P (l : Ledger) ( price_data : ContractLRecord )
												  ( price_code : cell ): 
{l' | l' = exec_state (Uinterpreter (prepare_price_xchg_state_init_and_addr price_data price_code)) l}.
  generate_proof (exec_expression l (prepare_price_xchg_state_init_and_addr price_data price_code)).
Defined.
Definition prepare_price_xchg_state_init_and_addr_auto_exec (l : Ledger) ( price_data : ContractLRecord )
												  ( price_code : cell ): Ledger.
intros. term_of (prepare_price_xchg_state_init_and_addr_exec_P l price_data price_code).
Defined.
Theorem prepare_price_xchg_state_init_and_addr_exec_proof_next (l : Ledger) ( price_data : ContractLRecord )
												  ( price_code : cell ) :
  prepare_price_xchg_state_init_and_addr_auto_exec l price_data price_code =
  exec_state (Uinterpreter (prepare_price_xchg_state_init_and_addr price_data price_code)) l.
Proof.
  intros. proof_of (prepare_price_xchg_state_init_and_addr_exec_P l price_data price_code).
Qed.
Definition prepare_price_xchg_state_init_and_addr_eval_P (l : Ledger) ( price_data : ContractLRecord )
												  ( price_code : cell ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_price_xchg_state_init_and_addr price_data price_code)) l)}.
  generate_proof (eval_expression l (prepare_price_xchg_state_init_and_addr price_data price_code)).
Defined.
Definition prepare_price_xchg_state_init_and_addr_auto_eval (l : Ledger) ( price_data : ContractLRecord )
												  ( price_code : cell ): ( StateInitLRecord # uint256 ).
intros. term_of (prepare_price_xchg_state_init_and_addr_eval_P l price_data price_code).
Defined.
Theorem prepare_price_xchg_state_init_and_addr_eval_proof_next (l : Ledger) ( price_data : ContractLRecord )
												  ( price_code : cell ) :
  prepare_price_xchg_state_init_and_addr_auto_eval l price_data price_code =
  toValue (eval_state (Uinterpreter (prepare_price_xchg_state_init_and_addr price_data price_code)) l).
Proof.
  intros. proof_of (prepare_price_xchg_state_init_and_addr_eval_P l price_data price_code).
Qed.
End prepare_price_xchg_state_init_and_addr.
End EvalExecAuto.
 *)