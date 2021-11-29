Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.

Require Import XchgPair.ClassTypes.
Require Import XchgPair.Ledger.
Require Import XchgPair.Functions.FuncSig.

Require Import XchgPair.Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module XchgPairPublicInterface := XchgPair.Interface.PublicInterface xt sm.
(* обращения к внешним интерфейсам нет *)

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

(* Fail Check OutgoingMessage_default. *)

Import UrsusNotations.
Local Open Scope ucpp_scope.
Local Open Scope ursus_scope.

(********************************************************************************************************************)
(*state fields*)
 
Definition flex_addr__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_flex_addr_ ) : ULValue raw_address ) . 
Definition flex_addr__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_flex_addr_ ) : URValue raw_address false ) . 
Notation " '_flex_addr_' " := ( flex_addr__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " '_flex_addr_' " := ( flex_addr__right ) (in custom URValue at level 0) : ursus_scope. 

Definition tip3_major_root__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_tip3_major_root_ ) : ULValue raw_address ) . 
Definition tip3_major_root__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_tip3_major_root_ ) : URValue raw_address false ) . 
Notation " '_tip3_major_root_' " := ( tip3_major_root__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " '_tip3_major_root_' " := ( tip3_major_root__right ) (in custom URValue at level 0) : ursus_scope. 

Definition tip3_minor_root__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_tip3_minor_root_ ) : ULValue raw_address ) . 
Definition tip3_minor_root__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_tip3_minor_root_ ) : URValue raw_address false ) . 
Notation " '_tip3_minor_root_' " := ( tip3_minor_root__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " '_tip3_minor_root_' " := ( tip3_minor_root__right ) (in custom URValue at level 0) : ursus_scope. 

Definition min_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_min_amount_ ) : ULValue uint128 ) . 
Definition min_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_min_amount_ ) : URValue uint128 false ) . 
Notation " '_min_amount_' " := ( min_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " '_min_amount_' " := ( min_amount__right ) (in custom URValue at level 0) : ursus_scope. 

Definition notify_addr__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_notify_addr_ ) : ULValue raw_address ) . 
Definition notify_addr__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DXchgPair_ι_notify_addr_ ) : URValue raw_address false ) . 
Notation " '_notify_addr_' " := ( notify_addr__left ) (in custom ULValue at level 0) : ursus_scope. 
Notation " '_notify_addr_' " := ( notify_addr__right ) (in custom URValue at level 0) : ursus_scope. 

Definition self_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_XchgPair ) : 
                                   ULValue ( mapping raw_address (queue (OutgoingMessage XchgPairPublicInterfaceModule.IXchgPair )) )) . 
Definition self_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_XchgPair ) : 
                                   URValue ( mapping raw_address (queue (OutgoingMessage XchgPairPublicInterface.IXchgPair ))) false) . 

Notation " 'error_code::not_enough_tons' " := (sInject not_enough_tons) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::double_deploy' " := (sInject double_deploy) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::zero_min_amount' " := (sInject zero_min_amount) (in custom URValue at level 0) : ursus_scope. 
Notation " 'rawreserve_flag::up_to' " := (sInject rawreserve_flag_ι_up_to) (in custom URValue at level 0) : ursus_scope. 



Notation " 'IXchgPairPtr' " := ( self_messages_left ) (in custom ULValue at level 0) : ursus_scope. 

Check {{ IXchgPairPtr [[ {_} ]] with { _ } ⤳ .onDeploy ( {} ,  {} ,  {} ) }}.


Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

(**************************************************************************************************)

 Definition onDeploy_right { a1 a2 a3 }  ( min_amount : URValue uint128 a1 ) 
                                         ( deploy_value : URValue uint128 a2 ) 
                                         ( notify_addr : URValue raw_address a3 ) : URValue boolean true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) onDeploy 
 min_amount deploy_value notify_addr ) . 
 
 Notation " 'onDeploy_' '(' min_amount deploy_value notify_addr ')' " := 
 ( onDeploy_right min_amount deploy_value notify_addr ) 
 (in custom URValue at level 0 , min_amount custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

 Definition getFlexAddr_right  : URValue raw_address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getFlexAddr ) . 
 
 Notation " 'getFlexAddr_' '(' ')' " := 
 ( getFlexAddr_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getTip3MajorRoot_right  : URValue raw_address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTip3MajorRoot ) . 
 
 Notation " 'getTip3MajorRoot_' '(' ')' " := 
 ( getTip3MajorRoot_right  ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getTip3MinorRoot_right  : URValue raw_address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTip3MinorRoot ) . 
 
 Notation " 'getTip3MinorRoot_' '(' ')' " := 
 ( getTip3MinorRoot_right ) (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition getMinAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getMinAmount ) . 
 
 Notation " 'getMinAmount_' '(' ')' " := 
 ( getMinAmount_right ) (in custom URValue at level 0 ) : ursus_scope . 

 Definition getNotifyAddr_right  : URValue raw_address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getNotifyAddr ) . 
 
 Notation " 'getNotifyAddr_' '(' ')' " := 
 ( getNotifyAddr_right ) (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition _fallback_right { a1 a2 }  ( msg : URValue TvmCell a1 ) 
                                       ( msg_body : URValue TvmSlice a2 ) : URValue uint ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback msg msg_body ) . 
 
 Notation " '_fallback_' '(' msg msg_body ')' " := 
 ( _fallback_right msg msg_body ) (in custom URValue at level 0 , msg custom URValue at level 0 , msg_body custom URValue at level 0 ) : ursus_scope .

 Definition prepare_xchg_pair_state_init_and_addr_right { a1 a2 }  ( pair_data : URValue ContractLRecord a1 ) 
                                                                   ( pair_code : URValue TvmCell a2 ) : URValue ( StateInitLRecord # uint256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_xchg_pair_state_init_and_addr pair_data pair_code ) . 
 
 Notation " 'prepare_xchg_pair_state_init_and_addr_' '(' pair_data pair_code ')' " := 
 ( prepare_xchg_pair_state_init_and_addr_right pair_data pair_code ) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 , pair_code custom URValue at level 0 ) : ursus_scope . 

End Calls. 

End FuncNotations.

