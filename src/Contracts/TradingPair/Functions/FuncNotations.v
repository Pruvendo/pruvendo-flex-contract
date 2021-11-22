
Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Require Import Project.CommonConstSig.

Require Import Contracts.TradingPair.Ledger.
Require Import Contracts.TradingPair.Functions.FuncSig.

(* здесь инмпортируем все внешние интерфейсы *)
Require Import Contracts.TradingPair.Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module TradingPairPublicInterface := PublicInterface xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Fail Check OutgoingMessage_default.

Import UrsusNotations.

Local Open Scope ursus_scope.

 
Notation " 'TickTock.tick' " := ( TickTock_ι_tick ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TickTock.tick' " := ( TickTock_ι_tick ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TickTock.tock' " := ( TickTock_ι_tock ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TickTock.tock' " := ( TickTock_ι_tock ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.split_depth' " := ( StateInit_ι_split_depth ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.split_depth' " := ( StateInit_ι_split_depth ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.special' " := ( StateInit_ι_special ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.special' " := ( StateInit_ι_special ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.code' " := ( StateInit_ι_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.code' " := ( StateInit_ι_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.data' " := ( StateInit_ι_data ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.data' " := ( StateInit_ι_data ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.library' " := ( StateInit_ι_library ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.library' " := ( StateInit_ι_library ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex_addr__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType flex_addr_ ) : ULValue XAddress ) . 
 Definition flex_addr__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType flex_addr_ ) : URValue XAddress false ) . 
 Notation " '_flex_addr_' " := ( flex_addr__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_addr_' " := ( flex_addr__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tip3_root__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tip3_root_ ) : ULValue XAddress ) . 
 Definition tip3_root__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tip3_root_ ) : URValue XAddress false ) . 
 Notation " '_tip3_root_' " := ( tip3_root__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tip3_root_' " := ( tip3_root__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition min_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType min_amount_ ) : ULValue XInteger128 ) . 
 Definition min_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType min_amount_ ) : URValue XInteger128 false ) . 
 Notation " '_min_amount_' " := ( min_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_min_amount_' " := ( min_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition notify_addr__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType notify_addr_ ) : ULValue XAddress ) . 
 Definition notify_addr__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType notify_addr_ ) : URValue XAddress false ) . 
 Notation " '_notify_addr_' " := ( notify_addr__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_notify_addr_' " := ( notify_addr__right ) (in custom URValue at level 0) : ursus_scope. 



Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.


Definition onDeploy_right { a1 a2 a3 }  ( min_amount : URValue ( XInteger128 ) a1 ) ( deploy_value : URValue ( XInteger128 ) a2 ) ( notify_addr : URValue ( XAddress ) a3 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) onDeploy 
 min_amount deploy_value notify_addr ) . 
 
 Notation " 'onDeploy_' '(' min_amount deploy_value notify_addr ')' " := 
 ( onDeploy_right 
 min_amount deploy_value notify_addr ) 
 (in custom URValue at level 0 , min_amount custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition getFlexAddr_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getFlexAddr 
 ) . 
 
 Notation " 'getFlexAddr_' '(' ')' " := 
 ( getFlexAddr_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getTip3Root_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTip3Root 
 ) . 
 
 Notation " 'getTip3Root_' '(' ')' " := 
 ( getTip3Root_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getMinAmount_right  : URValue XInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getMinAmount 
 ) . 
 
 Notation " 'getMinAmount_' '(' ')' " := 
 ( getMinAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getNotifyAddr_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getNotifyAddr 
 ) . 
 
 Notation " 'getNotifyAddr_' '(' ')' " := 
 ( getNotifyAddr_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition _fallback_right { a1 a2 }  ( msg : URValue ( XCell ) a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue XInteger ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 msg msg_body ) . 
 
 Notation " '_fallback_' '(' msg msg_body ')' " := 
 ( _fallback_right 
 msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope .

 Definition prepare_trading_pair_state_init_and_addr_right { a1 a2 }  
( pair_data : URValue ( ContractLRecord ) a1 )
 ( pair_code : URValue ( XCell ) a2 ) 
: URValue ( StateInitLRecord * XInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_trading_pair_state_init_and_addr 
 pair_data pair_code ) . 
 
 Notation " 'prepare_trading_pair_state_init_and_addr_' '(' pair_data pair_code ')' " := 
 ( prepare_trading_pair_state_init_and_addr_right 
 pair_data pair_code ) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 
 , pair_code custom URValue at level 0 ) : ursus_scope . 



End Calls. 

End FuncNotations.