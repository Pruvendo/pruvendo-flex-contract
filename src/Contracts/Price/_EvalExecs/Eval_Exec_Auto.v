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
Require Import Contracts.Price.Ledger.
Require Import Contracts.Price.Functions.FuncSig.
Require Import Contracts.Price.Functions.FuncNotations.
Require Import Contracts.Price.Functions.Funcs.
Require Contracts.Price.Interface.

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.


Module EvalExecAuto (co: CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .


Module Export FuncsModule := Funcs co dc.

Import FuncsInternal.
(* Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module Import TONTonkenWalletModuleForPrice := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .
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
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil))),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)))))%xprod
: LocalStateLRecord.

Opaque LocalStateDefault.

(* Import URSUS.
Import FuncsModule.TONTonkenWalletModuleForPrice.CommonTypes.BasicTypesModule.
Import FuncsModule.TONTonkenWalletModuleForPrice.CommonTypes.
 *) Import URSUS_.



(* ---------------------------------------------- *)
Section calc_cost .
Definition calc_cost_exec_P (l : Ledger) ( amount : uint128 ) ( price : uint128 ): 
{l' | l' = exec_state (Uinterpreter (calc_cost amount price)) l}.
  generate_proof (exec_expression l (calc_cost amount price)).
Defined.
Definition calc_cost_auto_exec (l : Ledger) ( amount : uint128 ) ( price : uint128 ): Ledger.
intros. term_of (calc_cost_exec_P l amount price).
Defined.
Theorem calc_cost_exec_proof_next (l : Ledger) ( amount : uint128 ) ( price : uint128 ) :
  calc_cost_auto_exec l amount price =
  exec_state (Uinterpreter (calc_cost amount price)) l.
Proof.
  intros.  proof_of (calc_cost_exec_P l amount price) .
Qed.

Context
(b0 : ULValue uint -> URValue uint false)
(f0 : UExpression ( XMaybe uint128 ) false)
(f1 : ULValue uint -> UExpression ( XMaybe uint128 ) true).
 Definition calc_cost_template  
( amount :  uint128 ) ( price :   uint128 ) : UExpression ( XMaybe uint128 ) true . 
     refine {{ new 'tons_cost : ( uint ) @ "tons_cost" := (#{amount}) * (#{price}) ; { _ } }} . 
 	 	 refine {{ if ( { b0 tons_cost }  ) 
                 then { { f0  } } ; { f1 tons_cost } }} . 
 Defined .
Definition calc_cost_template_eval_P (l : Ledger) ( amount : uint128 ) ( price : uint128 ): 
{v | v = (eval_state (Uinterpreter (calc_cost_template amount price)) l)}.
  generate_proof (eval_expression l (calc_cost_template amount price)).
Defined.
Definition calc_cost_template_auto_eval (l : Ledger) ( amount : uint128 ) ( price : uint128 ):   (ControlResult (optional uint128) true) .
intros. term_of (calc_cost_template_eval_P l amount price).
Defined.
Theorem calc_cost_template_eval_proof_next (l : Ledger) ( amount : uint128 ) ( price : uint128 ) :
  calc_cost_template_auto_eval l amount price =
  (eval_state (Uinterpreter (calc_cost_template amount price)) l).
Proof.
  intros. proof_of (calc_cost_template_eval_P l amount price).
Qed. 
End calc_cost.

(* ----------------------------------------- *)
Section is_active_time.
Lemma is_active_time_exec : forall ( order_finish_time : uint32 )
(s s0 : ContractLRecord)  (v : VMStateLRecord)  (m m0 : MessagesAndEventsLRecord) (l : LocalStateLRecord),
let ll : Ledger  := (s, (s0, (v, (m, (m0, (LocalStateDefault , l))))))%xprod in 
exec_state (Uinterpreter (is_active_time order_finish_time )) ll =  ll.
Proof.
    auto.
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
														( owner_address : optional address ) ( code : TvmCell ) 
														( workchain_id : int ): 
{l' | l' = exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l}.
  generate_proof (exec_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_exec (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : TvmCell ) 
														( workchain_id : int ): Ledger.
intros. term_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : TvmCell ) 
														( workchain_id : int ) :
  prepare_internal_wallet_state_init_and_addr_auto_exec l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  exec_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l.
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_exec_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.
Definition prepare_internal_wallet_state_init_and_addr_eval_P (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : TvmCell ) 
														( workchain_id : int ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l)}.
  generate_proof (eval_expression l (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)).
Defined.
Definition prepare_internal_wallet_state_init_and_addr_auto_eval (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : TvmCell ) 
														( workchain_id : int ): ( StateInitLRecord * uint256 ).
intros. term_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Defined.
Theorem prepare_internal_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : address ) 
														( owner_address : optional address ) ( code : TvmCell ) 
														( workchain_id : int ) :
  prepare_internal_wallet_state_init_and_addr_auto_eval l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id =
  toValue (eval_state (Uinterpreter (prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id)) l).
Proof.
  intros. proof_of (prepare_internal_wallet_state_init_and_addr_eval_P l name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id).
Qed.
End prepare_internal_wallet_state_init_and_addr.
(* ----------------------------------------- *)
Section expected_wallet_address.
Definition expected_wallet_address_exec_P (l : Ledger) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ): 
{l' | l' = exec_state (Uinterpreter (expected_wallet_address wallet_pubkey internal_owner)) l}.
  generate_proof (exec_expression l (expected_wallet_address wallet_pubkey internal_owner)).
Defined.
Definition expected_wallet_address_auto_exec (l : Ledger) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ): Ledger.
intros. term_of (expected_wallet_address_exec_P l wallet_pubkey internal_owner).
Defined.
Theorem expected_wallet_address_exec_proof_next (l : Ledger) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ) :
  expected_wallet_address_auto_exec l wallet_pubkey internal_owner =
  exec_state (Uinterpreter (expected_wallet_address wallet_pubkey internal_owner)) l.
Proof.
  intros. proof_of (expected_wallet_address_exec_P l wallet_pubkey internal_owner).
Qed.
Definition expected_wallet_address_eval_P (l : Ledger) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ): 
{v | v = toValue (eval_state (Uinterpreter (expected_wallet_address wallet_pubkey internal_owner)) l)}.
  generate_proof (eval_expression l (expected_wallet_address wallet_pubkey internal_owner)).
Defined.
Definition expected_wallet_address_auto_eval (l : Ledger) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ): uint256.
intros. term_of (expected_wallet_address_eval_P l wallet_pubkey internal_owner).
Defined.
Theorem expected_wallet_address_eval_proof_next (l : Ledger) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ) :
  expected_wallet_address_auto_eval l wallet_pubkey internal_owner =
  toValue (eval_state (Uinterpreter (expected_wallet_address wallet_pubkey internal_owner)) l).
Proof.
  intros. proof_of (expected_wallet_address_eval_P l wallet_pubkey internal_owner).
Qed.
End expected_wallet_address.
(* ----------------------------------------- *)
Section verify_tip3_addr.
Definition verify_tip3_addr_exec_P (l : Ledger) ( tip3_wallet : address ) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ): 
{l' | l' = exec_state (Uinterpreter (verify_tip3_addr tip3_wallet wallet_pubkey internal_owner)) l}.
  generate_proof (exec_expression l (verify_tip3_addr tip3_wallet wallet_pubkey internal_owner)).
Defined.
Definition verify_tip3_addr_auto_exec (l : Ledger) ( tip3_wallet : address ) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ): Ledger.
intros. term_of (verify_tip3_addr_exec_P l tip3_wallet wallet_pubkey internal_owner).
Defined.
Theorem verify_tip3_addr_exec_proof_next (l : Ledger) ( tip3_wallet : address ) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ) :
  verify_tip3_addr_auto_exec l tip3_wallet wallet_pubkey internal_owner =
  exec_state (Uinterpreter (verify_tip3_addr tip3_wallet wallet_pubkey internal_owner)) l.
Proof.
  intros. proof_of (verify_tip3_addr_exec_P l tip3_wallet wallet_pubkey internal_owner).
Qed.
Definition verify_tip3_addr_eval_P (l : Ledger) ( tip3_wallet : address ) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ): 
{v | v = toValue (eval_state (Uinterpreter (verify_tip3_addr tip3_wallet wallet_pubkey internal_owner)) l)}.
  generate_proof (eval_expression l (verify_tip3_addr tip3_wallet wallet_pubkey internal_owner)).
Defined.
Definition verify_tip3_addr_auto_eval (l : Ledger) ( tip3_wallet : address ) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ): boolean.
intros. term_of (verify_tip3_addr_eval_P l tip3_wallet wallet_pubkey internal_owner).
Defined.
Theorem verify_tip3_addr_eval_proof_next (l : Ledger) ( tip3_wallet : address ) ( wallet_pubkey : uint256 ) ( internal_owner : uint256 ) :
  verify_tip3_addr_auto_eval l tip3_wallet wallet_pubkey internal_owner =
  toValue (eval_state (Uinterpreter (verify_tip3_addr tip3_wallet wallet_pubkey internal_owner)) l).
Proof.
  intros. proof_of (verify_tip3_addr_eval_P l tip3_wallet wallet_pubkey internal_owner).
Qed.
End verify_tip3_addr.
(* ----------------------------------------- *)
Section on_sell_fail.
Definition on_sell_fail_exec_P (l : Ledger) ( ec : uint ) ( wallet_in : ( address (* ITONTokenWalletPtrLRecord *) ) ) 
					    ( amount : uint128 ): 
{l' | l' = exec_state (Uinterpreter (on_sell_fail ec wallet_in amount)) l}.
  generate_proof (exec_expression l (on_sell_fail ec wallet_in amount)).
Defined.
Definition on_sell_fail_auto_exec (l : Ledger) ( ec : uint ) ( wallet_in : ( address (* ITONTokenWalletPtrLRecord *) ) ) 
					    ( amount : uint128 ): Ledger.
intros. term_of (on_sell_fail_exec_P l ec wallet_in amount).
Defined.
Theorem on_sell_fail_exec_proof_next (l : Ledger) ( ec : uint ) ( wallet_in : ( address (* ITONTokenWalletPtrLRecord *) ) ) 
					    ( amount : uint128 ) :
  on_sell_fail_auto_exec l ec wallet_in amount =
  exec_state (Uinterpreter (on_sell_fail ec wallet_in amount)) l.
Proof.
  intros. proof_of (on_sell_fail_exec_P l ec wallet_in amount).
Qed.
Definition on_sell_fail_eval_P (l : Ledger) ( ec : uint ) ( wallet_in : ( address (* ITONTokenWalletPtrLRecord *) ) ) 
					    ( amount : uint128 ): 
{v | v = toValue (eval_state (Uinterpreter (on_sell_fail ec wallet_in amount)) l)}.
  generate_proof (eval_expression l (on_sell_fail ec wallet_in amount)).
Defined.
Definition on_sell_fail_auto_eval (l : Ledger) ( ec : uint ) ( wallet_in : ( address (* ITONTokenWalletPtrLRecord *) ) ) 
					    ( amount : uint128 ): OrderRetLRecord.
intros. term_of (on_sell_fail_eval_P l ec wallet_in amount).
Defined.
Theorem on_sell_fail_eval_proof_next (l : Ledger) ( ec : uint ) ( wallet_in : ( address (* ITONTokenWalletPtrLRecord *) ) ) 
					    ( amount : uint128 ) :
  on_sell_fail_auto_eval l ec wallet_in amount =
  toValue (eval_state (Uinterpreter (on_sell_fail ec wallet_in amount)) l).
Proof.
  intros. proof_of (on_sell_fail_eval_P l ec wallet_in amount).
Qed.
End on_sell_fail.
(* ----------------------------------------- *)
Section process_queue_impl.
Definition process_queue_impl_exec_P (l : Ledger) ( tip3root : address ) ( notify_addr : address (* IFlexNotifyPtrLRecord *)) 
							   ( price : uint128 ) ( deals_limit : uint8 ) ( tons_cfg : TonsConfigLRecord ) 
							   ( sell_idx : uint ) ( buy_idx : uint ) ( sells_amount : uint128 ) ( sells : queue OrderInfoLRecord ) 
                               ( buys_amount : uint128 ) ( buys : queue OrderInfoLRecord ): 
{l' | l' = exec_state (Uinterpreter (process_queue_impl tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)) l}.
  generate_proof (exec_expression l (process_queue_impl tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)).
Defined.
Definition process_queue_impl_auto_exec (l : Ledger) ( tip3root : address ) ( notify_addr : address (* IFlexNotifyPtrLRecord *)) 
							   ( price : uint128 ) ( deals_limit : uint8 ) ( tons_cfg : TonsConfigLRecord ) 
							   ( sell_idx : uint ) ( buy_idx : uint ) ( sells_amount : uint128 ) ( sells : queue OrderInfoLRecord ) 
                               ( buys_amount : uint128 ) ( buys : queue OrderInfoLRecord ): Ledger.
intros. term_of (process_queue_impl_exec_P l tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys).
Defined.
Theorem process_queue_impl_exec_proof_next (l : Ledger) ( tip3root : address ) ( notify_addr : address (* IFlexNotifyPtrLRecord *)) 
							   ( price : uint128 ) ( deals_limit : uint8 ) ( tons_cfg : TonsConfigLRecord ) 
							   ( sell_idx : uint ) ( buy_idx : uint ) ( sells_amount : uint128 ) ( sells : queue OrderInfoLRecord ) 
                               ( buys_amount : uint128 ) ( buys : queue OrderInfoLRecord ) :
  process_queue_impl_auto_exec l tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys =
  exec_state (Uinterpreter (process_queue_impl tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)) l.
Proof.
  intros. proof_of (process_queue_impl_exec_P l tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys).
Qed.
(* TODO eval true *)
Definition process_queue_impl_eval_P (l : Ledger) ( tip3root : address ) ( notify_addr : address (* IFlexNotifyPtrLRecord *)) 
							   ( price : uint128 ) ( deals_limit : uint8 ) ( tons_cfg : TonsConfigLRecord ) 
							   ( sell_idx : uint ) ( buy_idx : uint ) ( sells_amount : uint128 ) ( sells : queue OrderInfoLRecord ) 
                               ( buys_amount : uint128 ) ( buys : queue OrderInfoLRecord ): 
{v | v = (eval_state (Uinterpreter (process_queue_impl tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)) l)}.
  generate_proof (eval_expression l (process_queue_impl tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)).
Defined.
Definition process_queue_impl_auto_eval (l : Ledger) ( tip3root : address ) ( notify_addr : address (* IFlexNotifyPtrLRecord *)) 
							   ( price : uint128 ) ( deals_limit : uint8 ) ( tons_cfg : TonsConfigLRecord ) 
							   ( sell_idx : uint ) ( buy_idx : uint ) ( sells_amount : uint128 ) ( sells : queue OrderInfoLRecord ) 
                               ( buys_amount : uint128 ) ( buys : queue OrderInfoLRecord ): ControlResult (process_retLRecord) true.
intros. term_of (process_queue_impl_eval_P l tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys).
Defined.
Theorem process_queue_impl_eval_proof_next (l : Ledger) ( tip3root : address ) ( notify_addr : address (* IFlexNotifyPtrLRecord *)) 
							   ( price : uint128 ) ( deals_limit : uint8 ) ( tons_cfg : TonsConfigLRecord ) 
							   ( sell_idx : uint ) ( buy_idx : uint ) ( sells_amount : uint128 ) ( sells : queue OrderInfoLRecord ) 
                               ( buys_amount : uint128 ) ( buys : queue OrderInfoLRecord ) :
  process_queue_impl_auto_eval l tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys =
  (eval_state (Uinterpreter (process_queue_impl tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys)) l).
Proof.
  intros. proof_of (process_queue_impl_eval_P l tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys).
Qed.
End process_queue_impl.
(* ----------------------------------------- *)
Section buyTip3.
Definition buyTip3_exec_P (l : Ledger) ( amount : uint128 ) ( receive_tip3_wallet : address ) ( order_finish_time : uint32 ): 
{l' | l' = exec_state (Uinterpreter (buyTip3 amount receive_tip3_wallet order_finish_time)) l}.
  generate_proof (exec_expression l (buyTip3 amount receive_tip3_wallet order_finish_time)).
Defined.
Definition buyTip3_auto_exec (l : Ledger) ( amount : uint128 ) ( receive_tip3_wallet : address ) ( order_finish_time : uint32 ): Ledger.
intros. term_of (buyTip3_exec_P l amount receive_tip3_wallet order_finish_time).
Defined.
Theorem buyTip3_exec_proof_next (l : Ledger) ( amount : uint128 ) ( receive_tip3_wallet : address ) ( order_finish_time : uint32 ) :
  buyTip3_auto_exec l amount receive_tip3_wallet order_finish_time =
  exec_state (Uinterpreter (buyTip3 amount receive_tip3_wallet order_finish_time)) l.
Proof.
  intros. proof_of (buyTip3_exec_P l amount receive_tip3_wallet order_finish_time).
Qed.
(* TODO eval true *)
Definition buyTip3_eval_P (l : Ledger) ( amount : uint128 ) ( receive_tip3_wallet : address ) ( order_finish_time : uint32 ): 
{v | v =  (eval_state (Uinterpreter (buyTip3 amount receive_tip3_wallet order_finish_time)) l)}.
  generate_proof (eval_expression l (buyTip3 amount receive_tip3_wallet order_finish_time)).
Defined.
Definition buyTip3_auto_eval (l : Ledger) ( amount : uint128 ) ( receive_tip3_wallet : address ) ( order_finish_time : uint32 ): ControlResult (OrderRetLRecord) true.
intros. term_of (buyTip3_eval_P l amount receive_tip3_wallet order_finish_time).
Defined.
Theorem buyTip3_eval_proof_next (l : Ledger) ( amount : uint128 ) ( receive_tip3_wallet : address ) ( order_finish_time : uint32 ) :
  buyTip3_auto_eval l amount receive_tip3_wallet order_finish_time =
   (eval_state (Uinterpreter (buyTip3 amount receive_tip3_wallet order_finish_time)) l).
Proof.
  intros. proof_of (buyTip3_eval_P l amount receive_tip3_wallet order_finish_time).
Qed.

End buyTip3.
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
(* no eval *)
End cancelBuy.
(* ----------------------------------------- *)
Section prepare_price_state_init_and_addr.
Definition prepare_price_state_init_and_addr_exec_P (l : Ledger) ( price_data : DPriceLRecord ) 
											 ( price_code : TvmCell ): 
{l' | l' = exec_state (Uinterpreter (prepare_price_state_init_and_addr price_data price_code)) l}.
  generate_proof (exec_expression l (prepare_price_state_init_and_addr price_data price_code)).
Defined.
Definition prepare_price_state_init_and_addr_auto_exec (l : Ledger) ( price_data : DPriceLRecord ) 
											 ( price_code : TvmCell ): Ledger.
intros. term_of (prepare_price_state_init_and_addr_exec_P l price_data price_code).
Defined.
Theorem prepare_price_state_init_and_addr_exec_proof_next (l : Ledger) ( price_data : DPriceLRecord ) 
											 ( price_code : TvmCell ) :
  prepare_price_state_init_and_addr_auto_exec l price_data price_code =
  exec_state (Uinterpreter (prepare_price_state_init_and_addr price_data price_code)) l.
Proof.
  intros. proof_of (prepare_price_state_init_and_addr_exec_P l price_data price_code).
Qed.
Definition prepare_price_state_init_and_addr_eval_P (l : Ledger) ( price_data : DPriceLRecord ) 
											 ( price_code : TvmCell ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_price_state_init_and_addr price_data price_code)) l)}.
  generate_proof (eval_expression l (prepare_price_state_init_and_addr price_data price_code)).
Defined.
Definition prepare_price_state_init_and_addr_auto_eval (l : Ledger) ( price_data : DPriceLRecord ) 
											 ( price_code : TvmCell ): ( StateInitLRecord * uint256 ).
intros. term_of (prepare_price_state_init_and_addr_eval_P l price_data price_code).
Defined.
Theorem prepare_price_state_init_and_addr_eval_proof_next (l : Ledger) ( price_data : DPriceLRecord ) 
											 ( price_code : TvmCell ) :
  prepare_price_state_init_and_addr_auto_eval l price_data price_code =
  toValue (eval_state (Uinterpreter (prepare_price_state_init_and_addr price_data price_code)) l).
Proof.
  intros. proof_of (prepare_price_state_init_and_addr_eval_P l price_data price_code).
Qed.
(* ---------------------------------------------- *)
Section extract_active_order.
Context 
(f_while : ULValue (optional OrderInfoWithIdx) ->
ULValue (queue OrderInfoLRecord) ->
ULValue uint128 ->
ULValue boolean ->UExpression ( ( optional OrderInfoWithIdx ) # ( ( queue OrderInfoLRecord ) # uint128 ) ) true).
Definition  extract_active_order_template ( cur_order : optional OrderInfoWithIdx ) 
( orders : queue OrderInfoLRecord  ) 
( all_amount : uint128 ) 
( sell : boolean ) : UExpression ( ( optional OrderInfoWithIdx ) # ( ( queue OrderInfoLRecord ) # uint128 ) ) true  .
vararg cur_order "cur_order".
vararg orders "orders".
vararg all_amount "all_amount".
vararg sell "sell".
refine {{ if !{ cur_order } then { { _:UEt  } } ; { _ } }} .
refine {{ exit_ [ !{ cur_order } , !{ orders } , !{ all_amount } ] }} .
refine {{ { f_while  cur_order orders all_amount sell } ; { _ } }}.
refine {{ return_ [ !{cur_order} , !{orders} , !{all_amount} ] }} . 
Defined . 
Definition extract_active_order_template_exec_P (l : Ledger) ( cur_order : optional OrderInfoWithIdx ) 
( orders : queue OrderInfoLRecord  ) 
( all_amount : uint128 ) 
( sell : boolean ): 
{l' | l' = exec_state (Uinterpreter (extract_active_order_template cur_order orders all_amount sell)) l}.
  generate_proof (exec_expression l (extract_active_order_template cur_order orders all_amount sell)).
Defined.
Definition extract_active_order_template_auto_exec (l : Ledger) ( cur_order : optional OrderInfoWithIdx ) 
( orders : queue OrderInfoLRecord  ) 
( all_amount : uint128 ) 
( sell : boolean ): Ledger.
intros. term_of (extract_active_order_template_exec_P l cur_order orders all_amount sell).
Defined.
Theorem extract_active_order_template_exec_proof_next (l : Ledger) ( cur_order : optional OrderInfoWithIdx ) 
( orders : queue OrderInfoLRecord  ) 
( all_amount : uint128 ) 
( sell : boolean ) :
  extract_active_order_template_auto_exec l cur_order orders all_amount sell =
  exec_state (Uinterpreter (extract_active_order_template cur_order orders all_amount sell)) l.
Proof.
  intros. proof_of (extract_active_order_template_exec_P l cur_order orders all_amount sell).
Qed.
Definition extract_active_order_template_eval_P (l : Ledger) ( cur_order : optional OrderInfoWithIdx ) 
( orders : queue OrderInfoLRecord  ) 
( all_amount : uint128 ) 
( sell : boolean ): 
{v | v =  (eval_state (Uinterpreter (extract_active_order_template cur_order orders all_amount sell)) l)}.
  generate_proof (eval_expression l (extract_active_order_template cur_order orders all_amount sell)).
Defined.
Definition extract_active_order_template_auto_eval (l : Ledger) ( cur_order : optional OrderInfoWithIdx ) 
( orders : queue OrderInfoLRecord  ) 
( all_amount : uint128 ) 
( sell : boolean ): ControlResult ( ( optional OrderInfoWithIdx ) # ( ( queue OrderInfoLRecord ) # uint128 ) ) true.
intros. term_of (extract_active_order_template_eval_P l cur_order orders all_amount sell).
Defined.
Theorem extract_active_order_template_eval_proof_next (l : Ledger) ( cur_order : optional OrderInfoWithIdx ) 
( orders : queue OrderInfoLRecord  ) 
( all_amount : uint128 ) 
( sell : boolean ) :
  extract_active_order_template_auto_eval l cur_order orders all_amount sell =
   (eval_state (Uinterpreter (extract_active_order_template cur_order orders all_amount sell)) l).
Proof.
  intros. proof_of (extract_active_order_template_eval_P l cur_order orders all_amount sell).
Qed.
End extract_active_order.

(* ---------------------------------------------- *)
Section make_deal.
Context
(d_a : ULValue OrderInfoLRecord -> ULValue OrderInfoLRecord -> URValue uint false)
(s_o_t : ULValue OrderInfoLRecord ->  ULValue uint128 -> URValue boolean false )
(b_o_t : ULValue OrderInfoLRecord ->  ULValue uint128 -> URValue boolean false )
(l_t_s : ULValue uint -> ULValue OrderInfoLRecord -> URValue boolean false)
(b_c :  ULValue (optional uint) -> URValue uint128 true)
(f0  : ULValue OrderInfoLRecord -> ULValue OrderInfoLRecord -> ULValue uint -> UExpression ( boolean # (boolean # uint128) ) false )
(b0 : ULValue boolean -> ULValue boolean -> URValue boolean false)
( cc : ULValue uint -> ULValue dealerLRecord -> URValue (optional uint) true )
(f01 : ULValue uint128 -> ULValue dealerLRecord -> UExpression ( boolean # (boolean # uint128) ) false)
(f02 : ULValue uint128 -> ULValue dealerLRecord -> UExpression ( boolean # (boolean # uint128) ) false)
(f1 : ULValue boolean -> ULValue boolean -> UExpression ( boolean # (boolean # uint128) ) true )
(f2 : ULValue OrderInfoLRecord ->
ULValue OrderInfoLRecord ->
ULValue uint128 -> ULValue uint128 -> UExpression ( boolean # (boolean # uint128) ) false )
( f3 : ULValue OrderInfoLRecord ->
 ULValue (optional uint) -> UExpression ( boolean # (boolean # uint128) ) true )
(f4 : ULValue dealerLRecord ->
ULValue OrderInfoLRecord ->
ULValue OrderInfoLRecord ->
ULValue uint -> ULValue (optional uint) -> UExpression ( boolean # (boolean # uint128) ) true )
(f41 : ULValue dealerLRecord -> ULValue uint -> UExpression ( boolean # (boolean # uint128) ) false)
(f42 :  ULValue uint -> UExpression ( boolean # (boolean # uint128) ) false).
 Definition make_deal_template (this : ULValue dealerLRecord) ( sell : ULValue OrderInfoLRecord ) ( buy : ULValue OrderInfoLRecord ) : UExpression ( boolean # (boolean # uint128) ) true .
 refine {{ new 'deal_amount : uint @ "deal_amount" :=  { d_a sell buy } ; { _ } }} . 
 refine {{ new 'last_tip3_sell : boolean @ "last_tip3_sell" :=  { l_t_s deal_amount sell} ; { _ } }} .
 refine {{ { f0 sell buy deal_amount : UEf } ; { _ }  }}.
 refine {{ new 'cost : optional uint @ "cost" :=   { cc deal_amount this}  ; { _ } }} .
 refine {{ new 'sell_costs : uint128 @ "sell_costs" := 0 ; { _ } }} . 
 refine {{ new 'buy_costs : uint128 @ "buy_costs" :=    { b_c cost } ; { _ } }} . 
 refine {{ if ( !{last_tip3_sell} ) then { { _:UEf } } 
 else { { _:UEf } } ; { _ } }} . 
 refine {{ { f01  sell_costs  this }   }}.
 refine {{ { f02  sell_costs  this }   }}.
 refine {{ new 'sell_out_of_tons : boolean @ "sell_out_of_tons" :=   { s_o_t sell sell_costs } ; { _ } }} . 
 refine {{ new 'buy_out_of_tons : boolean @ "buy_out_of_tons" :=  { b_o_t buy buy_costs } ; { _ } }} . 
 refine {{ if (  {b0 sell_out_of_tons buy_out_of_tons} ) then { { _ :UEt } } ; { _ } }} . 
 refine {{ { f1 sell_out_of_tons buy_out_of_tons}  }}.
 refine {{ { f2 sell buy sell_costs buy_costs   } ; { _ }  }}.
 refine {{ {f4 this sell buy deal_amount cost  } }}.
 Defined .
 Definition make_deal_template_exec_P (l : Ledger) (this : ULValue dealerLRecord) ( sell : ULValue OrderInfoLRecord ) ( buy : ULValue OrderInfoLRecord ): 
 {l' | l' = exec_state (Uinterpreter (make_deal_template this sell buy)) l}.
   generate_proof (exec_expression l (make_deal_template this sell buy)).
 Defined.
 Definition make_deal_template_auto_exec (l : Ledger) (this : ULValue dealerLRecord) ( sell : ULValue OrderInfoLRecord ) ( buy : ULValue OrderInfoLRecord ): Ledger.
 intros. term_of (make_deal_template_exec_P l this sell buy).
 Defined.
 Theorem make_deal_template_exec_proof_next (l : Ledger) (this : ULValue dealerLRecord) ( sell : ULValue OrderInfoLRecord ) ( buy : ULValue OrderInfoLRecord ) :
   make_deal_template_auto_exec l this sell buy =
   exec_state (Uinterpreter (make_deal_template this sell buy)) l.
 Proof.
   intros. proof_of (make_deal_template_exec_P l this sell buy). 
 Qed.
End make_deal.
End prepare_price_state_init_and_addr.
End EvalExecAuto.
