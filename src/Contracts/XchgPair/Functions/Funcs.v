Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonAxioms.
Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.

(*Fully qualified name are mandatory in multi-contract environment*)
Require Import XchgPair.ClassTypes.
Require Import XchgPair.Ledger.
Require Import XchgPair.Functions.FuncSig.
Require Import XchgPair.Functions.FuncNotations.
(* Require Contracts.XchgPair.Interface. *)

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


Definition onDeploy (min_amount: uint128) (deploy_value: uint128) (notify_addr: address) : UExpression boolean true . 
    refine {{ require_ ( int_value () > #{ deploy_value } , error_code::not_enough_tons ) ; { _ } }} . 
    refine {{ require_ ( ~ _min_amount_ ,  error_code::double_deploy  ) ; { _ } }} .  
    refine {{ require_ ( #{ min_amount } > 0  , error_code::zero_min_amount ) ; { _ } }} .

    refine {{ _min_amount_ := #{ min_amount } ; { _ } }} . 
    refine {{ _notify_addr_ := #{ notify_addr } ; { _ } }} . 
    refine {{ tvm_rawreserve ( #{deploy_value} , rawreserve_flag::up_to) ; { _ } }} .  
    refine {{ set_int_return_flag ( # {SEND_ALL_GAS} ) ; { _ } }} . 
    refine {{ return_ TRUE  }} . 
 Defined . 
 
Definition getFlexAddr : UExpression address false . 
    refine {{ return_ _flex_addr_  }} . 
Defined . 
 
Definition getTip3MajorRoot : UExpression address false . 
    refine {{ return_ _tip3_major_root_  }} . 
Defined . 
 
Definition getTip3MinorRoot : UExpression address false . 
    refine {{ return_ _tip3_minor_root_ }} . 
Defined . 

Definition getMinAmount : UExpression uint128 false . 
    refine {{ return_ _min_amount_ }} . 
Defined . 
 
Definition getNotifyAddr : UExpression address false . 
    refine {{ return_ _notify_addr_ }} . 
Defined . 
 
Definition _fallback ( msg : cell_ ) ( msg_body : slice_ ) : UExpression uint false . 
 	refine {{ return_ 0 }} . 
Defined . 


(* inline
std::pair<StateInit, uint256> prepare_xchg_pair_state_init_and_addr(DXchgPair pair_data, cell pair_code) {
  cell pair_data_cl = prepare_persistent_data<IXchgPair, void, DXchgPair>({}, pair_data);
  StateInit pair_init {
    /*split_depth*/{}, /*special*/{},
    pair_code, pair_data_cl, /*library*/{}
  };
  cell pair_init_cl = build(pair_init).make_cell();
  return { pair_init, uint256(tvm_hash(pair_init_cl)) };
} *)

(* Set Universe Polymorphism. *)
Definition prepare_xchg_pair_state_init_and_addr ( pair_data : ContractLRecord ) 
                                                 ( pair_code : cell ) : UExpression ( StateInitLRecord # uint256 ) false . 
    refine {{ new 'pair_data_cl : cell @ "pair_data_cl" := prepare_persistent_data_ ( {} , #{pair_data} ) ; { _ } }} . 
    refine {{ new 'pair_init : StateInitLRecord @ "pair_init" := 
                      [ {} , {} , ( #{pair_code} ) -> set () , ( !{pair_data_cl} ) -> set () , {} ] ; { _ } }} . 
    refine {{ new 'pair_init_cl : cell @ "pair_init_cl" :=  build ( σ !{pair_init} ) -> make_cell ()  ; { _ } }} .    
    refine {{ return_ [ !{ pair_init } , tvm_hash ( !{pair_init_cl} )  ] }} .    
Defined . 

End FuncsInternal.
End Funcs.