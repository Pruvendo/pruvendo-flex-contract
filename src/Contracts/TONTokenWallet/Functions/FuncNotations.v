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
Require Import Contracts.TONTokenWallet.Ledger.
Require Import Contracts.TONTokenWallet.Functions.FuncSig.
Require Import Contracts.TONTokenWallet.ClassTypes.
Require Import Project.CommonTypes.


(* здесь инмпортируем все внешние интерфейсы *)
Require Import Contracts.TONTokenWallet.Interface.
Require Import Contracts.Wrapper.Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

Module TONTokenWalletPublicInterface := Contracts.TONTokenWallet.Interface.PublicInterface xt sm.
Module WrapperPublicInterfaceModule         := Wrapper.Interface.PublicInterface xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Import UrsusNotations.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Definition ITONTokenWalletPtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_TONTokenWallet ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage TONTokenWalletPublicInterface.ITONTokenWallet )) )) . 
Definition ITONTokenWalletPtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_TONTokenWallet ) : 
                                   URValue ( mapping address (queue (OutgoingMessage TONTokenWalletPublicInterface.ITONTokenWallet ))) false) . 
Notation " 'ITONTokenWalletPtr' " := ( ITONTokenWalletPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

Definition ITONTokenWalletNotifyPtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_TONTokenWalletNotify ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage TONTokenWalletPublicInterface.ITONTokenWalletNotify )) )) . 
Definition ITONTokenWalletNotifyPtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_TONTokenWalletNotify ) : 
                                   URValue ( mapping address (queue (OutgoingMessage TONTokenWalletPublicInterface.ITONTokenWalletNotify ))) false) . 
Notation " 'ITONTokenWalletNotifyPtr' " := ( ITONTokenWalletNotifyPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

Definition IWrapperPtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_Wrapper ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage WrapperPublicInterfaceModule.IWrapper )) )) . 
Definition IWrapperPtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_Wrapper ) : 
                                   URValue ( mapping address (queue (OutgoingMessage WrapperPublicInterfaceModule.IWrapper ))) false) . 
Notation " 'IWrapperPtr' " := ( IWrapperPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.



 Definition name__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_name_ ) : ULValue XString ) . 
 Definition name__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_name_ ) : URValue XString false ) . 
 Notation " '_name_' " := ( name__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_name_' " := ( name__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition symbol__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_symbol_ ) : ULValue XString ) . 
 Definition symbol__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_symbol_ ) : URValue XString false ) . 
 Notation " '_symbol_' " := ( symbol__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_symbol_' " := ( symbol__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition decimals__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_decimals_ ) : ULValue XUInteger8 ) . 
 Definition decimals__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_decimals_ ) : URValue XUInteger8 false ) . 
 Notation " '_decimals_' " := ( decimals__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_decimals_' " := ( decimals__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition balance__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_balance_ ) : ULValue XUInteger128 ) . 
 Definition balance__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_balance_ ) : URValue XUInteger128 false ) . 
 Notation " '_balance_' " := ( balance__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_balance_' " := ( balance__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition root_public_key__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_root_public_key_ ) : ULValue XUInteger256 ) . 
 Definition root_public_key__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_root_public_key_ ) : URValue XUInteger256 false ) . 
 Notation " '_root_public_key_' " := ( root_public_key__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_root_public_key_' " := ( root_public_key__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition wallet_public_key__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_wallet_public_key_ ) : ULValue XUInteger256 ) . 
 Definition wallet_public_key__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_wallet_public_key_ ) : URValue XUInteger256 false ) . 
 Notation " '_wallet_public_key_' " := ( wallet_public_key__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_wallet_public_key_' " := ( wallet_public_key__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition root_address__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_root_address_ ) : ULValue address ) . 
 Definition root_address__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_root_address_ ) : URValue address false ) . 
 Notation " '_root_address_' " := ( root_address__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_root_address_' " := ( root_address__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition owner_address__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_owner_address_ ) : ULValue ( XMaybe address ) ) . 
 Definition owner_address__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_owner_address_ ) : URValue ( XMaybe address ) false ) . 
 Notation " '_owner_address_' " := ( owner_address__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_owner_address_' " := ( owner_address__right ) (in custom URValue at level 0) : ursus_scope. 
 

 Definition lend_ownership__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_lend_ownership_ ) : ULValue (XHMap addr_std_fixed lend_recordLRecord) ) . 
 Definition lend_ownership__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_lend_ownership_ ) : URValue (XHMap addr_std_fixed lend_recordLRecord) false ) . 
 Notation " '_lend_ownership_' " := ( lend_ownership__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_lend_ownership_' " := ( lend_ownership__right ) (in custom URValue at level 0) : ursus_scope. 

 Definition code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_code_ ) : ULValue cell ) . 
 Definition code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_code_ ) : URValue cell false ) . 
 Notation " '_code_' " := ( code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_code_' " := ( code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition allowance__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_allowance_ ) : ULValue ( XMaybe allowance_infoLRecord ) ) . 
 Definition allowance__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_allowance_ ) : URValue ( XMaybe allowance_infoLRecord ) false ) . 
 Notation " '_allowance_' " := ( allowance__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_allowance_' " := ( allowance__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_workchain_id_ ) : ULValue int (* XUInteger8 *) ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_workchain_id_ ) : URValue int (* XUInteger8 *) false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 


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
Notation " 'error_code::only_original_owner_allowed' " := (sInject only_original_owner_allowed) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::wallet_in_lend_owneship' " := (sInject wallet_in_lend_owneship) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::not_enough_tons_to_process' " := (sInject ec_ι_not_enough_tons_to_process) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::transfer_to_zero_address' " := (sInject transfer_to_zero_address) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::message_sender_is_not_my_root' " := (sInject message_sender_is_not_my_root) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::message_sender_is_not_good_wallet' " := (sInject message_sender_is_not_good_wallet) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::destroy_non_empty_wallet' " := (sInject destroy_non_empty_wallet) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::finish_time_must_be_greater_than_now' " := (sInject finish_time_must_be_greater_than_now) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::no_allowance_set' " := (sInject no_allowance_set) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::wrong_spender' " := (sInject wrong_spender) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::not_enough_allowance' " := (sInject not_enough_allowance) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::wrong_public_call' " := (sInject wrong_public_call) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::non_zero_remaining' " := (sInject non_zero_remaining) (in custom URValue at level 0) : ursus_scope. 

Notation " 'rawreserve_flag::up_to' " := (sInject rawreserve_flag_ι_up_to) (in custom URValue at level 0) : ursus_scope. 
Notation " 'SEND_ALL_GAS_' " := (sInject SEND_ALL_GAS) (in custom URValue at level 0) : ursus_scope. 
Notation " 'IGNORE_ACTION_ERRORS_' " := (sInject IGNORE_ACTION_ERRORS) (in custom URValue at level 0) : ursus_scope. 

Notation " 'SENDER_WANTS_TO_PAY_FEES_SEPARATELY_' " := (sInject IGNORE_ACTION_ERRORS ) (in custom URValue at level 0) : ursus_scope. 
Notation " 'DELETE_ME_IF_I_AM_EMPTY_' " := (sInject DELETE_ME_IF_I_AM_EMPTY ) (in custom URValue at level 0) : ursus_scope. 






Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

(**************************************************************************************************)
 
 Definition transfer_left { R a1 a2 a3 a4 a5 }  ( answer_addr : URValue ( address ) a1 ) ( too : URValue ( address ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) ( grams : URValue ( XUInteger128 ) a4 ) ( return_ownership : URValue ( XBool ) a5 ) 
: UExpression R true (* ( orb ( orb ( orb ( orb a5 a4 ) a3 ) a2 ) a1 ) *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) transfer 
 answer_addr too tokens grams return_ownership ) . 
 
 Notation " 'transfer_' '(' answer_addr too tokens grams return_ownership ')' " := 
 ( transfer_left 
 answer_addr too tokens grams return_ownership ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , return_ownership custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferWithNotify_left { R a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( address ) a1 ) ( too : URValue ( address ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) ( grams : URValue ( XUInteger128 ) a4 ) ( return_ownership : URValue ( XBool ) a5 ) ( payload : URValue cell a6 ) 
: UExpression R true (* ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) transferWithNotify 
 answer_addr too tokens grams return_ownership payload ) . 
 
 Notation " 'transferWithNotify_' '(' answer_addr too tokens grams return_ownership payload ')' " := 
 ( transferWithNotify_left 
 answer_addr too tokens grams return_ownership payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferToRecipient_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( address ) a1 ) ( recipient_public_key : URValue ( XUInteger256 ) a2 ) ( recipient_internal_owner : URValue ( address ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) ( deploy : URValue ( XBool ) a6 ) ( return_ownership : URValue ( XBool ) a7 ) 
: UExpression R true (* ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) transferToRecipient 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership ) . 
 
 Notation " 'transferToRecipient_' '(' answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership ')' " := 
 ( transferToRecipient_left 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , recipient_public_key custom URValue at level 0 
 , recipient_internal_owner custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , deploy custom URValue at level 0 
 , return_ownership custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferToRecipientWithNotify_left { R a1 a2 a3 a4 a5 a6 a7 a8 }  ( answer_addr : URValue ( address ) a1 ) ( recipient_public_key : URValue ( XUInteger256 ) a2 ) ( recipient_internal_owner : URValue ( address ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) ( deploy : URValue ( XBool ) a6 ) ( return_ownership : URValue ( XBool ) a7 ) ( payload : URValue cell a8 ) 
: UExpression R true (* ( orb ( orb ( orb ( orb ( orb ( orb ( orb a8 a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ8 ) transferToRecipientWithNotify 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership payload ) . 
 
 Notation " 'transferToRecipientWithNotify_' '(' answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership payload ')' " := 
 ( transferToRecipientWithNotify_left 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , recipient_public_key custom URValue at level 0 
 , recipient_internal_owner custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , deploy custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 Definition requestBalance_right  : URValue XUInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) requestBalance 
 ) . 
 
 Notation " 'requestBalance_' '(' ')' " := 
 ( requestBalance_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition accept_right { a1 a2 a3 }  ( tokens : URValue ( XUInteger128 ) a1 ) ( answer_addr : URValue ( address ) a2 ) ( keep_grams : URValue ( XUInteger128 ) a3 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) accept 
 tokens answer_addr keep_grams ) . 
 
 Notation " 'accept_' '(' tokens answer_addr keep_grams ')' " := 
 ( accept_right 
 tokens answer_addr keep_grams ) 
 (in custom URValue at level 0 , tokens custom URValue at level 0 
 , answer_addr custom URValue at level 0 
 , keep_grams custom URValue at level 0 ) : ursus_scope . 
 
 Definition internalTransfer_left { R a1 a2 a3 a4 a5 a6 }  ( tokens : URValue ( XUInteger128 ) a1 ) ( answer_addr : URValue ( address ) a2 ) ( sender_pubkey : URValue ( XUInteger256 ) a3 ) ( sender_owner : URValue ( address ) a4 ) ( notify_receiver : URValue ( XBool ) a5 ) ( payload : URValue cell a6 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) internalTransfer 
 tokens answer_addr sender_pubkey sender_owner notify_receiver payload ) . 
 
 Notation " 'internalTransfer_' '(' tokens answer_addr sender_pubkey sender_owner notify_receiver payload ')' " := 
 ( internalTransfer_left 
 tokens answer_addr sender_pubkey sender_owner notify_receiver payload ) 
 (in custom ULValue at level 0 , tokens custom URValue at level 0 
 , answer_addr custom URValue at level 0 
 , sender_pubkey custom URValue at level 0 
 , sender_owner custom URValue at level 0 
 , notify_receiver custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition destroy_left { R a1 }  ( dest : URValue ( address ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) destroy 
 dest ) . 
 
 Notation " 'destroy_' '(' dest ')' " := 
 ( destroy_left 
 dest ) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 ) : ursus_scope . 
 
 Definition burn_left { R a1 a2 }  ( out_pubkey : URValue ( XUInteger256 ) a1 ) ( out_internal_owner : URValue ( address ) a2 ) 
: UExpression R true (* orb a2 a1 *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) burn 
 out_pubkey out_internal_owner ) . 
 
 Notation " 'burn_' '(' out_pubkey out_internal_owner ')' " := 
 ( burn_left 
 out_pubkey out_internal_owner ) 
 (in custom ULValue at level 0 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 ) : ursus_scope . 
 
 Definition lendOwnership_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( address ) a1 ) ( grams : URValue ( XUInteger128 ) a2 ) ( std_dest : URValue ( XUInteger256 ) a3 ) ( lend_balance : URValue ( XUInteger128 ) a4 ) ( lend_finish_time : URValue ( XUInteger32 ) a5 ) ( deploy_init_cl : URValue cell a6 ) ( payload : URValue cell a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) lendOwnership 
 answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload ) . 
 
 Notation " 'lendOwnership_' '(' answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload ')' " := 
 ( lendOwnership_left 
 answer_addr grams std_dest lend_balance lend_finish_time deploy_init_cl payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , grams custom URValue at level 0 
 , std_dest custom URValue at level 0 
 , lend_balance custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , deploy_init_cl custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition returnOwnership_left { R a1 }  ( tokens : URValue ( XUInteger128 ) a1 ) : UExpression R true (* a1 *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) returnOwnership 
 tokens ) . 
 
 Notation " 'returnOwnership_' '(' tokens ')' " := 
 ( returnOwnership_left 
 tokens ) 
 (in custom ULValue at level 0 , tokens custom URValue at level 0 ) : ursus_scope . 
 Definition getDetails_right  : URValue details_infoLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDetails 
 ) . 
 
 Notation " 'getDetails_' '(' ')' " := 
 ( getDetails_right 
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
 
 Definition getBalance_right  : URValue XUInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBalance 
 ) . 
 
 Notation " 'getBalance_' '(' ')' " := 
 ( getBalance_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getRootKey_right  : URValue XUInteger256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootKey 
 ) . 
 
 Notation " 'getRootKey_' '(' ')' " := 
 ( getRootKey_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getWalletKey_right  : URValue XUInteger256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getWalletKey 
 ) . 
 
 Notation " 'getWalletKey_' '(' ')' " := 
 ( getWalletKey_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getRootAddress_right  : URValue address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootAddress 
 ) . 
 
 Notation " 'getRootAddress_' '(' ')' " := 
 ( getRootAddress_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getOwnerAddress_right  : URValue address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwnerAddress 
 ) . 
 
 Notation " 'getOwnerAddress_' '(' ')' " := 
 ( getOwnerAddress_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getCode_right  : URValue cell false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getCode 
 ) . 
 
 Notation " 'getCode_' '(' ')' " := 
 ( getCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition allowance_right  : URValue allowance_infoLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) allowance 
 ) . 
 
 Notation " 'allowance_' '(' ')' " := 
 ( allowance_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition approve_left { R a1 a2 a3 }  ( spender : URValue ( address ) a1 ) ( remainingTokens : URValue ( XUInteger128 ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) approve 
 spender remainingTokens tokens ) . 
 
 Notation " 'approve_' '(' spender remainingTokens tokens ')' " := 
 ( approve_left 
 spender remainingTokens tokens ) 
 (in custom ULValue at level 0 , spender custom URValue at level 0 
 , remainingTokens custom URValue at level 0 
 , tokens custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferFrom_left { R a1 a2 a3 a4 a5 }  ( answer_addr : URValue ( address ) a1 ) ( from : URValue ( address ) a2 ) ( too : URValue ( address ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) 
: UExpression R true (* orb ( orb ( orb ( orb a5 a4 ) a3 ) a2 ) a1 *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) transferFrom 
 answer_addr from too tokens grams ) . 
 
 Notation " 'transferFrom_' '(' answer_addr from too tokens grams ')' " := 
 ( transferFrom_left 
 answer_addr from too tokens grams ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , from custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferFromWithNotify_left { R a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( address ) a1 ) ( from : URValue ( address ) a2 ) ( too : URValue ( address ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) ( payload : URValue cell a6 ) 
: UExpression R true (* ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) transferFromWithNotify 
 answer_addr from too tokens grams payload ) . 
 
 Notation " 'transferFromWithNotify_' '(' answer_addr from too tokens grams payload ')' " := 
 ( transferFromWithNotify_left 
 answer_addr from too tokens grams payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , from custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition internalTransferFrom_left { R a1 a2 a3 a4 a5 }  ( answer_addr : URValue ( address ) a1 ) ( too : URValue ( address ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) ( notify_receiver : URValue ( XBool ) a4 ) ( payload : URValue cell a5 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) internalTransferFrom 
 answer_addr too tokens notify_receiver payload ) . 
 
 Notation " 'internalTransferFrom_' '(' answer_addr too tokens notify_receiver payload ')' " := 
 ( internalTransferFrom_left 
 answer_addr too tokens notify_receiver payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , notify_receiver custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition disapprove_left { R }  : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) disapprove 
 ) . 
 
 Notation " 'disapprove_' '(' ')' " := 
 ( disapprove_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 Definition _on_bounced_right { a1 a2 }  ( msg : URValue cell a1 ) ( msg_body : URValue ( slice ) a2 ) : URValue XUInteger true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _on_bounced 
 msg msg_body ) . 
 
 Notation " '_on_bounced_' '(' msg msg_body ')' " := 
 ( _on_bounced_right 
 msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 

 Definition _fallback_right { a1 a2 }  ( cell : URValue cell a1 ) ( msg_body : URValue ( slice ) a2 ) : URValue XUInteger true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 cell msg_body ) . 
 
 Notation " '_fallback_' '(' cell msg_body ')' " := 
 ( _fallback_right 
 cell msg_body ) 
 (in custom URValue at level 0 , cell custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_impl_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( address ) a1 ) ( too : URValue ( address ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) ( grams : URValue ( XUInteger128 ) a4 ) ( return_ownership : URValue ( XBool ) a5 ) ( send_notify : URValue ( XBool ) a6 ) ( payload : URValue cell a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) transfer_impl 
 answer_addr too tokens grams return_ownership send_notify payload ) . 
 
 Notation " 'transfer_impl_' '(' answer_addr too tokens grams return_ownership send_notify payload ')' " := 
 ( transfer_impl_left 
 answer_addr too tokens grams return_ownership send_notify payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , send_notify custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_to_recipient_impl_left { R a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( answer_addr : URValue ( address ) a1 ) ( recipient_public_key : URValue ( XUInteger256 ) a2 ) ( recipient_internal_owner : URValue ( address ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) ( deploy : URValue ( XBool ) a6 ) ( return_ownership : URValue ( XBool ) a7 ) ( send_notify : URValue ( XBool ) a8 ) ( payload : URValue cell a9 ) 
: UExpression R true (* ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) transfer_to_recipient_impl 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ) . 
 
 Notation " 'transfer_to_recipient_impl_' '(' answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ')' " := 
 ( transfer_to_recipient_impl_left 
 answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , recipient_public_key custom URValue at level 0 
 , recipient_internal_owner custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , deploy custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , send_notify custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_from_impl_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( address ) a1 ) ( from : URValue ( address ) a2 ) ( too : URValue ( address ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) ( send_notify : URValue ( XBool ) a6 ) ( payload : URValue cell a7 ) 
: UExpression R true (* ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) *) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) transfer_from_impl 
 answer_addr from too tokens grams send_notify payload ) . 
 
 Notation " 'transfer_from_impl_' '(' answer_addr from too tokens grams send_notify payload ')' " := 
 ( transfer_from_impl_left 
 answer_addr from too tokens grams send_notify payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , from custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , send_notify custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 

 Definition get_owner_addr_right  : URValue address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) get_owner_addr 
 ) . 
 
 Notation " 'get_owner_addr_' '(' ')' " := 
 ( get_owner_addr_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition fixup_answer_addr_right { a1 }  ( answer_addr : URValue ( address ) a1 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) fixup_answer_addr 
 answer_addr ) . 
 
 Notation " 'fixup_answer_addr_' '(' answer_addr ')' " := 
 ( fixup_answer_addr_right 
 answer_addr ) 
 (in custom URValue at level 0 , answer_addr custom URValue at level 0 ) : ursus_scope . 

 Definition check_transfer_requires_right { a1 a2 }  ( tokens : URValue ( XUInteger128 ) a1 ) ( grams : URValue ( XUInteger128 ) a2 ) : URValue XUInteger128 true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_transfer_requires 
 tokens grams ) . 
 
 Notation " 'check_transfer_requires_' '(' tokens grams ')' " := 
 ( check_transfer_requires_right 
 tokens grams ) 
 (in custom URValue at level 0 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 



 
 Definition prepare_transfer_message_flags_right  ( (* & *) grams : ULValue ( XUInteger128 ) ) : URValue XUInteger false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1L ) prepare_transfer_message_flags 
 grams ) . 
 
 Notation " 'prepare_transfer_message_flags_' '(' grams ')' " := 
 ( prepare_transfer_message_flags_right 
 grams ) 
 (in custom URValue at level 0 , grams custom URValue at level 0 ) : ursus_scope . 



 
 Definition update_spent_balance_left { R a1 a2 }  ( tokens : URValue ( XUInteger128 ) a1 ) ( return_ownership : URValue ( XBool ) a2 ) : UExpression R ( orb a2 a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) update_spent_balance 
 tokens return_ownership ) . 
 
 Notation " 'update_spent_balance_' '(' tokens return_ownership ')' " := 
 ( update_spent_balance_left 
 tokens return_ownership ) 
 (in custom ULValue at level 0 , tokens custom URValue at level 0 
 , return_ownership custom URValue at level 0 ) : ursus_scope .

 Definition optional_owner_right { a1 }  ( owner : URValue ( address ) a1 ) : URValue (XMaybe address) a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) optional_owner 
 owner ) . 
 
 Notation " 'optional_owner_' '(' owner ')' " := 
 ( optional_owner_right 
 owner ) 
 (in custom URValue at level 0 , owner custom URValue at level 0 ) : ursus_scope .

 Definition calc_wallet_init_hash_right { a1 a2 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( internal_owner : URValue ( address ) a2 ) : URValue ( StateInitLRecord # XUInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_wallet_init_hash 
 pubkey internal_owner ) . 
 
 Notation " 'calc_wallet_init_hash_' '(' pubkey internal_owner ')' " := 
 ( calc_wallet_init_hash_right 
 pubkey internal_owner ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope . 

 Definition expected_sender_address_right { a1 a2 }  ( sender_public_key : URValue ( XUInteger256 ) a1 ) ( sender_owner : URValue ( address ) a2 ) : URValue XUInteger256 ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) expected_sender_address 
 sender_public_key sender_owner ) . 
 
 Notation " 'expected_sender_address_' '(' sender_public_key sender_owner ')' " := 
 ( expected_sender_address_right 
 sender_public_key sender_owner ) 
 (in custom URValue at level 0 , sender_public_key custom URValue at level 0 
 , sender_owner custom URValue at level 0 ) : ursus_scope .

 Definition calc_wallet_init_right { a1 a2 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( internal_owner : URValue ( address ) a2 ) : URValue ( StateInitLRecord # address ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_wallet_init 
 pubkey internal_owner ) . 
 
 Notation " 'calc_wallet_init_' '(' pubkey internal_owner ')' " := 
 ( calc_wallet_init_right 
 pubkey internal_owner ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope .

 Definition filter_lend_ownerhip_map_right  : URValue ( (XHMap addr_std_fixed lend_recordLRecord) # XUInteger128 ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) filter_lend_ownerhip_map 
 ) . 
 
 Notation " 'filter_lend_ownerhip_map_' '(' ')' " := 
 ( filter_lend_ownerhip_map_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope .
 
Definition is_internal_owner_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) is_internal_owner 
 ) . 
 
 Notation " 'is_internal_owner_' '(' ')' " := 
 ( is_internal_owner_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition check_internal_owner_right { a1 a2 }  ( original_owner_only : URValue ( XBool ) a1 ) ( allowed_for_original_owner_in_lend_state : URValue ( XBool ) a2 ) : URValue XUInteger128 true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_internal_owner 
 original_owner_only allowed_for_original_owner_in_lend_state ) . 
 
 Notation " 'check_internal_owner_' '(' original_owner_only allowed_for_original_owner_in_lend_state ')' " := 
 ( check_internal_owner_right 
 original_owner_only allowed_for_original_owner_in_lend_state ) 
 (in custom URValue at level 0 , original_owner_only custom URValue at level 0 
 , allowed_for_original_owner_in_lend_state custom URValue at level 0 ) : ursus_scope . 

 Definition check_external_owner_right  : URValue XUInteger128 true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_external_owner 
 ) . 
 
 Notation " 'check_external_owner_' '(' ')' " := 
 ( check_external_owner_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition check_owner_right { a1 a2 }  ( original_owner_only : URValue ( XBool ) a1 ) ( allowed_in_lend_state : URValue ( XBool ) a2 ) 
: URValue XUInteger128 true (* ( orb a2 a1 ) *) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_owner 
 original_owner_only allowed_in_lend_state ) . 
 
 Notation " 'check_owner_' '(' original_owner_only allowed_in_lend_state ')' " := 
 ( check_owner_right 
 original_owner_only allowed_in_lend_state ) 
 (in custom URValue at level 0 , original_owner_only custom URValue at level 0 
 , allowed_in_lend_state custom URValue at level 0 ) : ursus_scope .

(* Definition prepare_wallet_data_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XUInteger8 ) a3 ) ( root_public_key : URValue ( XUInteger256 ) a4 ) ( wallet_public_key : URValue ( XUInteger256 ) a5 ) ( root_address : URValue ( address ) a6 ) ( owner_address : URValue ( XMaybe address ) a7 ) ( code : URValue cell a8 ) ( workchain_id : URValue ( XUInteger8 ) a9 ) : URValue DTONTokenWalletLRecord ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_wallet_data 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_wallet_data_' '(' name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ')' " := 
 ( prepare_wallet_data_right 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 
 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 
 , root_public_key custom URValue at level 0 
 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , code custom URValue at level 0 
 , workchain_id custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_wallet_state_init_and_addr_right { a1 }  ( wallet_data : URValue ( DTONTokenWalletLRecord ) a1 ) : URValue ( StateInitLRecord * XUInteger256 ) a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) prepare_wallet_state_init_and_addr 
 wallet_data ) . 
 
 Notation " 'prepare_wallet_state_init_and_addr_' '(' wallet_data ')' " := 
 ( prepare_wallet_state_init_and_addr_right 
 wallet_data ) 
 (in custom URValue at level 0 , wallet_data custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_external_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XUInteger8 ) a3 ) ( root_public_key : URValue ( XUInteger256 ) a4 ) ( wallet_public_key : URValue ( XUInteger256 ) a5 ) ( root_address : URValue ( address ) a6 ) ( owner_address : URValue ( XMaybe address ) a7 ) ( code : URValue cell a8 ) ( workchain_id : URValue ( XUInteger8 ) a9 ) : URValue ( StateInitLRecord * XUInteger256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_external_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_external_wallet_state_init_and_addr_' '(' name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ')' " := 
 ( prepare_external_wallet_state_init_and_addr_right 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 
 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 
 , root_public_key custom URValue at level 0 
 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , code custom URValue at level 0 
 , workchain_id custom URValue at level 0 ) : ursus_scope . 
 Definition prepare_internal_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XUInteger8 ) a3 ) ( root_public_key : URValue ( XUInteger256 ) a4 ) ( wallet_public_key : URValue ( XUInteger256 ) a5 ) ( root_address : URValue ( address ) a6 ) ( owner_address : URValue ( XMaybe address ) a7 ) ( code : URValue cell a8 ) ( workchain_id : URValue ( XUInteger8 ) a9 ) : URValue ( StateInitLRecord * XUInteger256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_internal_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_internal_wallet_state_init_and_addr_' '(' name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ')' " := 
 ( prepare_internal_wallet_state_init_and_addr_right 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 
 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 
 , root_public_key custom URValue at level 0 
 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , code custom URValue at level 0 
 , workchain_id custom URValue at level 0 ) : ursus_scope . 
 Definition prepare_root_state_init_and_addr_right { a1 a2 }  ( root_code : URValue cell a1 ) ( root_data : URValue ( DRootTokenContractLRecord ) a2 ) : URValue ( StateInitLRecord * XUInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_root_state_init_and_addr 
 root_code root_data ) . 
 
 Notation " 'prepare_root_state_init_and_addr_' '(' root_code root_data ')' " := 
 ( prepare_root_state_init_and_addr_right 
 root_code root_data ) 
 (in custom URValue at level 0 , root_code custom URValue at level 0 
 , root_data custom URValue at level 0 ) : ursus_scope . *)

End Calls. 

End FuncNotations.
