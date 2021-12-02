Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.tvmFunc.

Require Import CommonTypes.
Require Import CommonNotations.

Module CommonAxioms (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.

Import UrsusNotations.
Local Open Scope ursus_scope.

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

Definition prepare_persistent_data {Y} (persistent_data_header : PhantomType) 
                                        (base : Y): UExpression cell false .
 refine {{ return_ {} }} .  
Qed.

Print cell.

Definition prepare_persistent_data_right { Y a1 a2 }  
                                    ( persistent_data_header : URValue PhantomType a1 ) 
                                    ( base : URValue Y a2 ) : URValue cell (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args ( LedgerableWithArgs:= λ2 ) prepare_persistent_data persistent_data_header base ) . 
 
Notation " 'prepare_persistent_data_' '(' a ',' b ')' " := 
 ( prepare_persistent_data_right  a b ) 
 (in custom URValue at level 0 , a custom URValue at level 0 , b custom URValue at level 0 ) : ursus_scope . 

End CommonAxioms.