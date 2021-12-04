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
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonConstSig.

Require Import CommonAxioms.
Require Import Contracts.RootTokenContract.Ledger.
Require Import Contracts.RootTokenContract.Functions.FuncSig.
Require Import Contracts.RootTokenContract.ClassTypes.
Require Import Contracts.TONTokenWallet.ClassTypes.
Require Import Project.CommonTypes.


(* здесь инмпортируем все внешние интерфейсы *)
Require Import Contracts.TONTokenWallet.Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

Module TONTokenWalletPublicInterface := Contracts.TONTokenWallet.Interface.PublicInterface xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Import UrsusNotations.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.


Definition ITONTokenWalletPtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_ITONTokenWallet ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage TONTokenWalletPublicInterface.ITONTokenWallet )) )) . 
Definition ITONTokenWalletPtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_ITONTokenWallet ) : 
                                   URValue ( mapping address (queue (OutgoingMessage TONTokenWalletPublicInterface.ITONTokenWallet ))) false) . 
Notation " 'ITONTokenWalletPtr' " := ( ITONTokenWalletPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.


 Definition name__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_name_ ) : ULValue XString ) . 
 Definition name__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_name_ ) : URValue XString false ) . 
 Notation " '_name_' " := ( name__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_name_' " := ( name__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition symbol__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_symbol_ ) : ULValue XString ) . 
 Definition symbol__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_symbol_ ) : URValue XString false ) . 
 Notation " '_symbol_' " := ( symbol__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_symbol_' " := ( symbol__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition decimals__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_decimals_ ) : ULValue XUInteger8 ) . 
 Definition decimals__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_decimals_ ) : URValue XUInteger8 false ) . 
 Notation " '_decimals_' " := ( decimals__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_decimals_' " := ( decimals__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition root_public_key__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_root_public_key_ ) : ULValue XUInteger256 ) . 
 Definition root_public_key__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_root_public_key_ ) : URValue XUInteger256 false ) . 
 Notation " '_root_public_key_' " := ( root_public_key__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_root_public_key_' " := ( root_public_key__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition total_supply__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_total_supply_ ) : ULValue XUInteger128 ) . 
 Definition total_supply__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_total_supply_ ) : URValue XUInteger128 false ) . 
 Notation " '_total_supply_' " := ( total_supply__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_total_supply_' " := ( total_supply__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition total_granted__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_total_granted_ ) : ULValue XUInteger128 ) . 
 Definition total_granted__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_total_granted_ ) : URValue XUInteger128 false ) . 
 Notation " '_total_granted_' " := ( total_granted__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_total_granted_' " := ( total_granted__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition wallet_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_wallet_code_ ) : ULValue (XMaybe cell) ) . 
 Definition wallet_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_wallet_code_ ) : URValue (XMaybe cell) false ) . 
 Notation " '_wallet_code_' " := ( wallet_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_wallet_code_' " := ( wallet_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition owner_address__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_owner_address_ ) : ULValue ( XMaybe address ) ) . 
 Definition owner_address__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_owner_address_ ) : URValue ( XMaybe address ) false ) . 
 Notation " '_owner_address_' " := ( owner_address__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_owner_address_' " := ( owner_address__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition start_balance__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_start_balance_ ) : ULValue XUInteger ) . 
 Definition start_balance__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_start_balance_ ) : URValue XUInteger false ) . 
 Notation " '_start_balance_' " := ( start_balance__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_start_balance_' " := ( start_balance__right ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'error_code::internal_owner_disabled' " := (sInject error_code_ι_internal_owner_disabled) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_message_sender_is_not_my_owner) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::internal_owner_enabled' " := (sInject error_code_ι_internal_owner_enabled) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::define_pubkey_or_internal_owner' " := (sInject error_code_ι_define_pubkey_or_internal_owner) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::too_big_decimals' " := (sInject error_code_ι_too_big_decimals) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::cant_override_wallet_code' " := (sInject error_code_ι_cant_override_wallet_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::not_enough_balance' " := (sInject error_code_ι_not_enough_balance) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::define_pubkey_or_internal_owner' " := (sInject error_code_ι_define_pubkey_or_internal_owner) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::wrong_bounced_header' " := (sInject error_code_ι_wrong_bounced_header) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::wrong_bounced_args' " := (sInject error_code_ι_wrong_bounced_args) (in custom URValue at level 0) : ursus_scope. 

Notation " 'rawreserve_flag::up_to' " := (sInject rawreserve_flag_ι_up_to) (in custom URValue at level 0) : ursus_scope. 
Notation " 'SEND_ALL_GAS_' " := (sInject SEND_ALL_GAS) (in custom URValue at level 0) : ursus_scope.
 
Notation " 'global_id::answer_id' " := (sInject global_id_ι_answer_id) (in custom URValue at level 0) : ursus_scope.

Definition save_persistent_data_left { R a1 } (x: URValue DRootTokenContractLRecord a1) : UExpression R a1 := 
 wrapULExpression ( ursus_call_with_args (LedgerableWithArgs:= λ0 ) (save_persistent_data x) ) .  

Notation " 'save_persistent_data' '(' x ')' " := (save_persistent_data_left x)  (in custom ULValue at level 0, x custom URValue) : ursus_scope .


Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

(**************************************************************************************************)

 Definition constructor_left { R a1 a2 a3 a4 a5 a6 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XUInteger8 ) a3 ) ( root_public_key : URValue ( XUInteger256 ) a4 ) ( root_owner : URValue ( address ) a5 ) ( total_supply : URValue ( XUInteger128 ) a6 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) constructor 
 name symbol decimals root_public_key root_owner total_supply ) . 
 
 Notation " 'constructor_' '(' name symbol decimals root_public_key root_owner total_supply ')' " := 
 ( constructor_left 
 name symbol decimals root_public_key root_owner total_supply ) 
 (in custom ULValue at level 0 , name custom URValue at level 0 
 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 
 , root_public_key custom URValue at level 0 
 , root_owner custom URValue at level 0 
 , total_supply custom URValue at level 0 ) : ursus_scope . 
 Definition setWalletCode_right { a1 }  ( wallet_code : URValue cell a1 ) : URValue boolean true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setWalletCode 
 wallet_code ) . 
 
 Notation " 'setWalletCode_' '(' wallet_code ')' " := 
 ( setWalletCode_right 
 wallet_code ) 
 (in custom URValue at level 0 , wallet_code custom URValue at level 0 ) : ursus_scope . 
 Definition deployWallet_right { a1 a2 a3 a4 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( internal_owner : URValue ( address ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) ( grams : URValue ( XUInteger128 ) a4 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) deployWallet 
 pubkey internal_owner tokens grams ) . 
 
 Notation " 'deployWallet_' '(' pubkey internal_owner tokens grams ')' " := 
 ( deployWallet_right 
 pubkey internal_owner tokens grams ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 Definition deployEmptyWallet_right { a1 a2 a3 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( internal_owner : URValue ( address ) a2 ) ( grams : URValue ( XUInteger128 ) a3 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) deployEmptyWallet 
 pubkey internal_owner grams ) . 
 
 Notation " 'deployEmptyWallet_' '(' pubkey internal_owner grams ')' " := 
 ( deployEmptyWallet_right 
 pubkey internal_owner grams ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 
 Definition grant_left { R a1 a2 a3 }  ( dest : URValue ( address ) a1 ) ( tokens : URValue ( XUInteger128 ) a2 ) ( grams : URValue ( XUInteger128 ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) grant 
 dest tokens grams ) . 
 
 Notation " 'grant_' '(' dest tokens grams ')' " := 
 ( grant_left 
 dest tokens grams ) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 Definition mint_right { a1 }  ( tokens : URValue ( XUInteger128 ) a1 ) : URValue boolean true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) mint 
 tokens ) . 
 
 Notation " 'mint_' '(' tokens ')' " := 
 ( mint_right 
 tokens ) 
 (in custom URValue at level 0 , tokens custom URValue at level 0 ) : ursus_scope . 
 Definition requestTotalGranted_right  : URValue XUInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) requestTotalGranted 
 ) . 
 
 Notation " 'requestTotalGranted_' '(' ')' " := 
 ( requestTotalGranted_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getName_right  : URValue XString false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getName 
 ) . 
 
 Notation " 'getName_' '(' ')' " := 
 ( getName_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getSymbol_right  : URValue XString false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSymbol 
 ) . 
 
 Notation " 'getSymbol_' '(' ')' " := 
 ( getSymbol_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getDecimals_right  : URValue XUInteger8 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDecimals 
 ) . 
 
 Notation " 'getDecimals_' '(' ')' " := 
 ( getDecimals_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getRootKey_right  : URValue XUInteger256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootKey 
 ) . 
 
 Notation " 'getRootKey_' '(' ')' " := 
 ( getRootKey_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getTotalSupply_right  : URValue XUInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTotalSupply 
 ) . 
 
 Notation " 'getTotalSupply_' '(' ')' " := 
 ( getTotalSupply_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getTotalGranted_right  : URValue XUInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTotalGranted 
 ) . 
 
 Notation " 'getTotalGranted_' '(' ')' " := 
 ( getTotalGranted_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition hasWalletCode_right  : URValue boolean false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasWalletCode 
 ) . 
 
 Notation " 'hasWalletCode_' '(' ')' " := 
 ( hasWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getWalletCode_right  : URValue cell true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getWalletCode 
 ) . 
 
 Notation " 'getWalletCode_' '(' ')' " := 
 ( getWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getWalletAddress_right { a1 a2 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( owner : URValue ( address ) a2 ) : URValue address ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) getWalletAddress 
 pubkey owner ) . 
 
 Notation " 'getWalletAddress_' '(' pubkey ',' owner ')' " := 
 ( getWalletAddress_right 
 pubkey owner ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , owner custom URValue at level 0 ) : ursus_scope . 

 Definition _on_bounced_right { a1 a2 }  ( msg : URValue cell a1 ) ( msg_body : URValue ( slice ) a2 ) : URValue XUInteger true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _on_bounced 
 msg msg_body ) . 
 
 Notation " '_on_bounced_' '(' cell msg_body ')' " := 
 ( _on_bounced_right 
 cell msg_body ) 
 (in custom URValue at level 0 , cell custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 
 Definition getWalletCodeHash_right  : URValue XUInteger256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getWalletCodeHash 
 ) . 
 
 Notation " 'getWalletCodeHash_' '(' ')' " := 
 ( getWalletCodeHash_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition _fallback_right { a1 a2 }  ( x : URValue cell a1 ) ( y : URValue slice a2 ) : URValue XUInteger (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 x y ) . 
 
 Notation " '_fallback_' '(' x ',' y ')' " := 
 ( _fallback_right 
 x y ) 
 (in custom URValue at level 0 , 
x custom URValue at level 0 ,
y custom URValue at level 0 ) : ursus_scope . 

 Definition optional_owner_right { a1 }  ( owner : URValue ( address ) a1 ) : URValue (XMaybe address) a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) optional_owner 
 owner ) . 
 
 Notation " 'optional_owner_' '(' owner ')' " := 
 ( optional_owner_right 
 owner ) 
 (in custom URValue at level 0 , owner custom URValue at level 0 ) : ursus_scope . 

 Definition workchain_id_right  : URValue int false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) workchain_id 
 ) . 
 
 Notation " 'workchain_id_' '(' ')' " := 
 ( workchain_id_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition calc_wallet_init_right { a1 a2 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( owner_addr : URValue ( address ) a2 ) : URValue ( StateInitLRecord # address ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_wallet_init 
 pubkey owner_addr ) . 
 
 Notation " 'calc_wallet_init_' '(' pubkey owner_addr ')' " := 
 ( calc_wallet_init_right 
 pubkey owner_addr ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , owner_addr custom URValue at level 0 ) : ursus_scope . 

Definition is_internal_owner_right : URValue boolean false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) is_internal_owner ) . 
 
Notation " 'is_internal_owner_' '(' ')' " := ( is_internal_owner_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition check_internal_owner_left { R }  : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_internal_owner 
 ) . 
 
 Notation " 'check_internal_owner_' '(' ')' " := 
 ( check_internal_owner_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition check_external_owner_left { R a1 }  ( allow_pubkey_owner_in_internal_node : URValue ( boolean ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) check_external_owner 
 allow_pubkey_owner_in_internal_node ) . 
 
 Notation " 'check_external_owner_' '(' allow_pubkey_owner_in_internal_node ')' " := 
 ( check_external_owner_left 
 allow_pubkey_owner_in_internal_node ) 
 (in custom ULValue at level 0 , allow_pubkey_owner_in_internal_node custom URValue at level 0 ) : ursus_scope . 
 
 Definition check_owner_left { R a1 }  ( false : URValue boolean a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) check_owner 
 false ) . 
 
 Notation " 'check_owner_' '(' false ')' " := 
 ( check_owner_left 
 false ) 
 (in custom ULValue at level 0 , false custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_root_state_init_and_addr_right { a1 a2 }  ( root_code : URValue cell a1 ) ( root_data : URValue ( DRootTokenContractLRecord ) a2 ) : URValue ( StateInitLRecord # XUInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_root_state_init_and_addr 
 root_code root_data ) . 
 
 Notation " 'prepare_root_state_init_and_addr_' '(' root_code root_data ')' " := 
 ( prepare_root_state_init_and_addr_right 
 root_code root_data ) 
 (in custom URValue at level 0 , root_code custom URValue at level 0 
 , root_data custom URValue at level 0 ) : ursus_scope . 


End Calls. 

End FuncNotations.
