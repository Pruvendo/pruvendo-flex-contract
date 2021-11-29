Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
From elpi Require Import elpi.
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonTypes.
Require Import Project.CommonNotations.
Require Import Project.CommonConstSig.

(*Fully qualified name are mandatory in multi-contract environment*)
Require Import TradingPair.Ledger.
Require Import TradingPair.Functions.FuncSig.
Require Import TradingPair.Functions.FuncNotations.

(* Require TradingPair.Interface. *)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.

Module Funcs (co : CompilerOptions) (dc : ConstsTypesSig XTypesModule StateMonadModule) .

Import co.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Parameter set_int_return_flag : UExpression boolean false .
Notation " 'set_int_return_flag_' '(' ')' " := 
 ( set_int_return_flag ) 
 (in custom ULValue at level 0 ) : ursus_scope .

Definition onDeploy ( min_amount : uint128 ) ( deploy_value : uint128 ) ( notify_addr : raw_address ) : UExpression boolean true . 
	refine {{ require_ ( ( int_value () ) > #{ deploy_value }  ,  error_code::not_enough_tons  ) ; { _ } }} . 
	refine {{ require_ ( ~  _min_amount_  , error_code::double_deploy  ) ; { _ } }} .

	refine {{ require_ ( ( #{ min_amount } ) > 0 ,  error_code::zero_min_amount ) ; { _ } }} . 
	refine {{ _min_amount_ := (#{ min_amount }) ; { _ } }} . 
	refine {{ _notify_addr_ := (#{ notify_addr }) ; { _ } }} . 
	refine {{ tvm_rawreserve ( #{deploy_value} , rawreserve_flag::up_to  ) ; { _ } }} .  
	refine {{ set_int_return_flag_ ( ) (* SEND_ALL_GAS *) ; { _ } }} . 
	refine {{ return_ TRUE }} .
Defined.

Definition getFlexAddr : UExpression raw_address false . 
	refine {{ return_ _flex_addr_ }} . 
Defined . 
 
Definition getTip3Root : UExpression raw_address false . 
	refine {{ return_ _tip3_root_ }} . 
Defined . 

Definition getMinAmount : UExpression uint128 false . 
	refine {{ return_ _min_amount_ }} . 
Defined . 
 
Definition getNotifyAddr : UExpression raw_address false . 
	refine {{ return_ _notify_addr_ }} . 
Defined . 
 
Definition _fallback ( _ : TvmCell ) ( _ : TvmSlice ) : UExpression uint false . 
	refine {{ return_ 0 }} . 
Defined . 
 
Definition prepare_persistent_data { X Y } (persistent_data_header : X) 
                                           (base : Y): UExpression TvmCell false .
	refine {{ return_ {} }} .  
Defined .

Definition prepare_persistent_data_right { X Y a1 a2 }  
                                    ( persistent_data_header : URValue X a1 ) 
                                    ( base : URValue Y a2 ) : URValue TvmCell (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args ( LedgerableWithArgs:= λ2 ) prepare_persistent_data persistent_data_header base ) . 
 
Notation " 'prepare_persistent_data_' '(' a ',' b ')' " := ( prepare_persistent_data_right a b ) 
 (in custom URValue at level 0 , a custom URValue at level 0 , b custom URValue at level 0 ) : ursus_scope . 

Definition prepare_trading_pair_state_init_and_addr ( pair_data : ContractLRecord) ( pair_code : TvmCell ) 
													: UExpression ( StateInitLRecord * uint256 ) false . 
	refine {{ new 'pair_data_cl : TvmCell @ "pair_data_cl" := 
			prepare_persistent_data_ ( {} , #{pair_data} ) ; { _ } }} . 
	refine {{ new 'pair_init : StateInitLRecord @ "pair_init" :=
				[ {} , {} , (#{pair_code}) -> set () , (!{pair_data_cl}) -> set () , {} ] ; { _ } }} . 
	refine {{ new 'pair_init_cl : TvmCell @ "pair_init_cl" := {} ; { _ } }} . 
	refine {{ { pair_init_cl } := {} (* build ( !{ pair_init } ) . make_cell ( ) *) ; { _ } }} . 
	refine {{ return_ [ !{ pair_init } , tvm_hash ( !{pair_init_cl} ) ] }} . 
Defined . 

End FuncsInternal.
End Funcs.








