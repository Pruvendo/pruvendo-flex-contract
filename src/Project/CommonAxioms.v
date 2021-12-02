Require Import Strings.String.
Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import CommonTypes.
Require Import CommonNotations.

Module CommonAxioms (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Import stdTypesNotations := stdTypesNotations xt sm cs.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope string_scope.

(* Variable x: URValue StateInitLRecord false.
Check || build ( {x} ) ||. *)

(* Module Export BasicTypesModule := BasicTypes xt sm.
Module Export CommonVMStateModule := VMStateModule xt sm.
 *)

(* inline cell prepare_persistent_data(persistent_data_header_t<IContract, ReplayAttackProtection> persistent_data_header,
                                    DContract base) {
  using namespace schema;
  auto data_tup = to_std_tuple(base);
  if constexpr (persistent_header_info<IContract, ReplayAttackProtection>::non_empty) {
    auto data_tup_combined = std::tuple_cat(std::make_tuple(bool_t(false), persistent_data_header), data_tup);
    auto chain_tup = make_chain_tuple(data_tup_combined);
    return build(chain_tup).make_cell();
  } else {
    auto data_tup_combined = std::tuple_cat(std::make_tuple(bool_t(false)), data_tup);
    auto chain_tup = make_chain_tuple(data_tup_combined);
    return build(chain_tup).make_cell();
  }
} *)
Check cell.

Polymorphic
Definition prepare_persistent_data {Y} (persistent_data_header : PhantomType) 
                                        (base : Y): UExpression cell false .
 refine {{ return_ {} }} .  
Qed.

Polymorphic
Definition prepare_persistent_data_right { Y a1 a2 }  
                                    ( persistent_data_header : URValue PhantomType a1 ) 
                                    ( base : URValue Y a2 ) : URValue cell (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args ( LedgerableWithArgs:= λ2 ) prepare_persistent_data persistent_data_header base ) . 
 
Notation " 'prepare_persistent_data_' '(' a ',' b ')' " := 
 ( prepare_persistent_data_right  a b ) 
 (in custom URValue at level 0 , a custom URValue at level 0 , b custom URValue at level 0 ) : ursus_scope . 


Definition serialize {b X}  (x: URValue X b):  URValue XUInteger b.
pose proof (urvalue_bind x (fun _ => || 0 || )).
rewrite right_or_false in X0.
refine X0.
Qed.

Notation " 'σ' x ":= ( serialize x ) (in custom URValue at level 0 , x custom URValue at level 0).


(* Variable x: URValue StateInitLRecord false.
Check || build ( {x} ) ||. *)

(* Require Import Coq.Strings.String.
Local Open Scope string_scope. *)

(* Declare Instance foo : LocalStateField cell_.
Declare Instance bar :LocalStateField StateInitLRecord.

Definition prepare_xchg_pair_state_init_and_addr ( pair_data : StateInitLRecord ) 
                                                 ( pair_code : cell_ ) : UExpression ( StateInitLRecord # XUInteger256 ) false . 
    refine {{ new 'pair_data_cl : cell_ @ "pair_data_cl" := 
            prepare_persistent_data_ ( {} , #{pair_data} ) ; { _ } }} . 
    refine {{ new 'pair_init : StateInitLRecord @ "pair_init" := {} ; { _ } }} . 
    refine {{ new 'pair_init_cl : cell_ @ "pair_init_cl" := {} ; { _ } }} . 
    Check builder_build.
    Eval compute in builder.
    About TvmCell_.
    Check || build ( !{pair_init} ) -> make_cell () ||.
    refine {{ {pair_init_cl} :=  build ( !{pair_init} ) -> make_cell ()  ; { _ } }} . *)

End CommonAxioms.