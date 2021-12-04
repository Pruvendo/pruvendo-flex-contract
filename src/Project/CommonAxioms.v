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

Require Import CommonConstSig.

Module CommonAxioms (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm) .
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Import stdTypesNotations := stdTypesNotations xt sm cs.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope string_scope.

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

Definition serialize {b X} (x: URValue X b):  URValue XUInteger b.
  pose proof (urvalue_bind x (fun _ => || 0 || )).
  rewrite right_or_false in X0.
  refine X0.
Qed.

Definition deserialize {b X}`{XDefault X} (x: URValue XUInteger b) : URValue X b .
  pose proof (urvalue_bind x (fun _ => #default )).
  rewrite right_or_false in X0.
  refine X0.
Qed.

Notation " 'σ' x ":= ( serialize x ) (in custom URValue at level 0 , x custom URValue at level 0).
Notation " 'δ' x ":= ( deserialize x ) (in custom URValue at level 0 , x custom URValue at level 0).
Notation " x '->' 'sl' '()' " := ( || build (σ {x}) -> endc() -> ctos () || )
(in custom URValue at level 0 , x custom URValue ) : ursus_scope . 


Definition return_func_id : URValue (optional uint32) false .
  exact ( || 0 -> set () || ).
Qed.
Notation " 'return_func_id_' '()' " := (return_func_id) (in custom URValue at level 0) : ursus_scope .

Parameter parse : forall X (b be: bool) (x: URValue slice b) (e: URValue ErrorType be) , URValue X true.
Arguments parse {X} {b} {be}.

Definition parser {b} (x: URValue slice b) := x.

Parameter tvm_ldu32 : forall b (s: URValue slice b), URValue uint32 b.
Arguments tvm_ldu32 {b}.

Notation " 'parse' '(' x , e ')' " := (parse x e) (in custom URValue at level 2, x custom URValue , e custom URValue) : ursus_scope .   
Notation " 'parser' '(' x ')' " := (parser x) (in custom URValue at level 2, x custom URValue) : ursus_scope .   
Notation " x '->' 'ldu' '(' '32' ')' " := (tvm_ldu32 x) (in custom URValue at level 2, x custom URValue) : ursus_scope .

Parameter tvm_ldi32 : forall b (s: URValue slice b), URValue int b.
Arguments tvm_ldi32 {b}.
Notation " x '->' 'ldi' '(' '32' ')' " := (tvm_ldi32 x) (in custom URValue at level 2, x custom URValue) : ursus_scope .


Definition msg_header_t := internal_msg_headerLRecord.
Definition msg_header_with_answer_id_t := internal_msg_header_with_answer_idLRecord.


Parameter parse_continue : forall X (b be: bool) (x: URValue slice b) (e: URValue ErrorType be) , URValue (X # slice) true.
Arguments parse_continue {X} {b} {be}.

Notation " 'parse_continue' '(' x , e ')' " := (parse_continue x e) (in custom URValue at level 2, x custom URValue , e custom URValue) : ursus_scope .   

Definition external_wallet_replay_protection_init: URValue PhantomType false.
  exact || {} ||.
Qed.

Notation " 'external_wallet_replay_protection_t::init' '()' " := 
	(external_wallet_replay_protection_init) (in custom URValue at level 0) : ursus_scope .

Definition root_replay_protection_init: URValue PhantomType false.
  exact || {} ||.
Qed.

Notation " 'root_replay_protection_t::init' '()' " := 
	(root_replay_protection_init) (in custom URValue at level 0) : ursus_scope .

Definition wallet_replay_protection_init: URValue PhantomType false.
  exact || {} ||.
Qed.

Notation " 'wallet_replay_protection_t::init' '()' " := 
	(wallet_replay_protection_init) (in custom URValue at level 0) : ursus_scope .

Definition flex_replay_protection_init: URValue PhantomType false.
  exact || {} ||.
Qed.

Notation " 'flex_replay_protection_t::init' '()' " := 
	(flex_replay_protection_init) (in custom URValue at level 0) : ursus_scope .

Definition wrapper_replay_protection_init: URValue PhantomType false.
  exact || {} ||.
Qed.

Notation " 'wrapper_replay_protection_t::init' '()' " := 
	(wrapper_replay_protection_init) (in custom URValue at level 0) : ursus_scope .
  

End CommonAxioms.