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

Require Import Contracts.Wrapper.Ledger.
Require Import Contracts.Wrapper.Functions.FuncSig.

(* здесь инмпортируем все внешние интерфейсы *)

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Fail Check OutgoingMessage_default.

Import UrsusNotations.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Notation " 'WrapperRet.err_code' " := ( WrapperRet_ι_err_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'WrapperRet.err_code' " := ( WrapperRet_ι_err_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'WrapperRet.flex_wallet' " := ( WrapperRet_ι_flex_wallet ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'WrapperRet.flex_wallet' " := ( WrapperRet_ι_flex_wallet ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDeployWalletArgs.pubkey' " := ( FlexDeployWalletArgs_ι_pubkey ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDeployWalletArgs.pubkey' " := ( FlexDeployWalletArgs_ι_pubkey ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDeployWalletArgs.internal_owner' " := ( FlexDeployWalletArgs_ι_internal_owner ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDeployWalletArgs.internal_owner' " := ( FlexDeployWalletArgs_ι_internal_owner ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexDeployWalletArgs.grams' " := ( FlexDeployWalletArgs_ι_grams ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexDeployWalletArgs.grams' " := ( FlexDeployWalletArgs_ι_grams ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.name' " := ( wrapper_details_info_ι_name ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.name' " := ( wrapper_details_info_ι_name ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.symbol' " := ( wrapper_details_info_ι_symbol ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.symbol' " := ( wrapper_details_info_ι_symbol ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.decimals' " := ( wrapper_details_info_ι_decimals ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.decimals' " := ( wrapper_details_info_ι_decimals ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.root_public_key' " := ( wrapper_details_info_ι_root_public_key ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.root_public_key' " := ( wrapper_details_info_ι_root_public_key ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.total_granted' " := ( wrapper_details_info_ι_total_granted ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.total_granted' " := ( wrapper_details_info_ι_total_granted ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.wallet_code' " := ( wrapper_details_info_ι_wallet_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.wallet_code' " := ( wrapper_details_info_ι_wallet_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.owner_address' " := ( wrapper_details_info_ι_owner_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.owner_address' " := ( wrapper_details_info_ι_owner_address ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.external_wallet' " := ( wrapper_details_info_ι_external_wallet ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'wrapper_details_info.external_wallet' " := ( wrapper_details_info_ι_external_wallet ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition name__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType name_ ) : ULValue XString ) . 
 Definition name__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType name_ ) : URValue XString false ) . 
 Notation " '_name_' " := ( name__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_name_' " := ( name__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition symbol__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType symbol_ ) : ULValue XString ) . 
 Definition symbol__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType symbol_ ) : URValue XString false ) . 
 Notation " '_symbol_' " := ( symbol__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_symbol_' " := ( symbol__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition decimals__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType decimals_ ) : ULValue XUInteger8 ) . 
 Definition decimals__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType decimals_ ) : URValue XUInteger8 false ) . 
 Notation " '_decimals_' " := ( decimals__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_decimals_' " := ( decimals__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : ULValue XUInteger8 ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : URValue XUInteger8 false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition root_public_key__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType root_public_key_ ) : ULValue XUInteger256 ) . 
 Definition root_public_key__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType root_public_key_ ) : URValue XUInteger256 false ) . 
 Notation " '_root_public_key_' " := ( root_public_key__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_root_public_key_' " := ( root_public_key__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition total_granted__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType total_granted_ ) : ULValue XUInteger128 ) . 
 Definition total_granted__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType total_granted_ ) : URValue XUInteger128 false ) . 
 Notation " '_total_granted_' " := ( total_granted__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_total_granted_' " := ( total_granted__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition internal_wallet_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType internal_wallet_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition internal_wallet_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType internal_wallet_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_internal_wallet_code_' " := ( internal_wallet_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_internal_wallet_code_' " := ( internal_wallet_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition owner_address__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType owner_address_ ) : ULValue ( XMaybe XAddress ) ) . 
 Definition owner_address__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType owner_address_ ) : URValue ( XMaybe XAddress ) false ) . 
 Notation " '_owner_address_' " := ( owner_address__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_owner_address_' " := ( owner_address__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition start_balance__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType start_balance_ ) : ULValue GramsLRecord ) . 
 Definition start_balance__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType start_balance_ ) : URValue GramsLRecord false ) . 
 Notation " '_start_balance_' " := ( start_balance__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_start_balance_' " := ( start_balance__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition external_wallet__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType external_wallet_ ) : ULValue ( XMaybe ITONTokenWalletPtrLRecord ) ) . 
 Definition external_wallet__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType external_wallet_ ) : URValue ( XMaybe ITONTokenWalletPtrLRecord ) false ) . 
 Notation " '_external_wallet_' " := ( external_wallet__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_external_wallet_' " := ( external_wallet__right ) (in custom URValue at level 0) : ursus_scope. 
 
Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

(**************************************************************************************************)

 Definition getStateInit_right { a1 }  ( &msg : URValue ( ) : URValue StateInitLRecord a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) getStateInit 
 &msg ) . 
 
 Notation " 'getStateInit_' '(' &msg ')' " := 
 ( getStateInit_right 
 &msg ) 
 (in custom URValue at level 0 , &msg custom URValue at level 0 ) : ursus_scope . 
 Definition init_right { a1 }  ( external_wallet : URValue ( XAddress ) a1 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) init 
 external_wallet ) . 
 
 Notation " 'init_' '(' external_wallet ')' " := 
 ( init_right 
 external_wallet ) 
 (in custom URValue at level 0 , external_wallet custom URValue at level 0 ) : ursus_scope . 
 Definition setInternalWalletCode_right { a1 }  ( wallet_code : URValue ( XCell ) a1 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setInternalWalletCode 
 wallet_code ) . 
 
 Notation " 'setInternalWalletCode_' '(' wallet_code ')' " := 
 ( setInternalWalletCode_right 
 wallet_code ) 
 (in custom URValue at level 0 , wallet_code custom URValue at level 0 ) : ursus_scope . 
 Definition deployEmptyWallet_right { a1 a2 a3 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( internal_owner : URValue ( XAddress ) a2 ) ( grams : URValue ( XUInteger128 ) a3 ) : URValue XAddress ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) deployEmptyWallet 
 pubkey internal_owner grams ) . 
 
 Notation " 'deployEmptyWallet_' '(' pubkey internal_owner grams ')' " := 
 ( deployEmptyWallet_right 
 pubkey internal_owner grams ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 Definition onTip3Transfer_right { a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( XAddress ) a1 ) ( balance : URValue ( XUInteger128 ) a2 ) ( new_tokens : URValue ( XUInteger128 ) a3 ) ( sender_pubkey : URValue ( XUInteger256 ) a4 ) ( sender_owner : URValue ( XAddress ) a5 ) ( payload : URValue ( XCell ) a6 ) : URValue WrapperRetLRecord true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) onTip3Transfer 
 answer_addr balance new_tokens sender_pubkey sender_owner payload ) . 
 
 Notation " 'onTip3Transfer_' '(' answer_addr balance new_tokens sender_pubkey sender_owner payload ')' " := 
 ( onTip3Transfer_right 
 answer_addr balance new_tokens sender_pubkey sender_owner payload ) 
 (in custom URValue at level 0 , answer_addr custom URValue at level 0 
 , balance custom URValue at level 0 
 , new_tokens custom URValue at level 0 
 , sender_pubkey custom URValue at level 0 
 , sender_owner custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition burn_left { R a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( XAddress ) a1 ) ( sender_pubkey : URValue ( XUInteger256 ) a2 ) ( sender_owner : URValue ( XAddress ) a3 ) ( out_pubkey : URValue ( XUInteger256 ) a4 ) ( out_internal_owner : URValue ( XAddress ) a5 ) ( tokens : URValue ( XUInteger128 ) a6 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) burn 
 answer_addr sender_pubkey sender_owner out_pubkey out_internal_owner tokens ) . 
 
 Notation " 'burn_' '(' answer_addr sender_pubkey sender_owner out_pubkey out_internal_owner tokens ')' " := 
 ( burn_left 
 answer_addr sender_pubkey sender_owner out_pubkey out_internal_owner tokens ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , sender_pubkey custom URValue at level 0 
 , sender_owner custom URValue at level 0 
 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 
 , tokens custom URValue at level 0 ) : ursus_scope . 
 Definition requestTotalGranted_right  : URValue XUInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) requestTotalGranted 
 ) . 
 
 Notation " 'requestTotalGranted_' '(' ')' " := 
 ( requestTotalGranted_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getDetails_right  : URValue wrapper_details_infoLRecord false := 
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
 Definition getRootKey_right  : URValue XUInteger256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootKey 
 ) . 
 
 Notation " 'getRootKey_' '(' ')' " := 
 ( getRootKey_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getTotalGranted_right  : URValue XUInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTotalGranted 
 ) . 
 
 Notation " 'getTotalGranted_' '(' ')' " := 
 ( getTotalGranted_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition hasInternalWalletCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasInternalWalletCode 
 ) . 
 
 Notation " 'hasInternalWalletCode_' '(' ')' " := 
 ( hasInternalWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getInternalWalletCode_right  : URValue XCell false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getInternalWalletCode 
 ) . 
 
 Notation " 'getInternalWalletCode_' '(' ')' " := 
 ( getInternalWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getOwnerAddress_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwnerAddress 
 ) . 
 
 Notation " 'getOwnerAddress_' '(' ')' " := 
 ( getOwnerAddress_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getExternalWallet_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getExternalWallet 
 ) . 
 
 Notation " 'getExternalWallet_' '(' ')' " := 
 ( getExternalWallet_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getWalletAddress_right { a1 a2 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( owner : URValue ( XAddress ) a2 ) : URValue XAddress ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) getWalletAddress 
 pubkey owner ) . 
 
 Notation " 'getWalletAddress_' '(' pubkey owner ')' " := 
 ( getWalletAddress_right 
 pubkey owner ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , owner custom URValue at level 0 ) : ursus_scope . 
 Definition _on_bounced_right { a1 a2 }  ( cell : URValue ( (LRecord ) a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue XUInteger true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _on_bounced 
 cell msg_body ) . 
 
 Notation " '_on_bounced_' '(' cell msg_body ')' " := 
 ( _on_bounced_right 
 cell msg_body ) 
 (in custom URValue at level 0 , cell custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 
 Definition getInternalWalletCodeHash_right  : URValue XUInteger256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getInternalWalletCodeHash 
 ) . 
 
 Notation " 'getInternalWalletCodeHash_' '(' ')' " := 
 ( getInternalWalletCodeHash_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition _fallback_right { a1 a2 }  ( msg : URValue ( XCell ) a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue XUInteger ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 msg msg_body ) . 
 
 Notation " '_fallback_' '(' msg msg_body ')' " := 
 ( _fallback_right 
 msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 
 Definition optional_owner_right { a1 }  ( owner : URValue ( XAddress ) a1 ) : URValue XMaybe XAddress a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) optional_owner 
 owner ) . 
 
 Notation " 'optional_owner_' '(' owner ')' " := 
 ( optional_owner_right 
 owner ) 
 (in custom URValue at level 0 , owner custom URValue at level 0 ) : ursus_scope . 
 Definition expected_internal_address_right { a1 a2 }  ( sender_public_key : URValue ( XUInteger256 ) a1 ) ( sender_owner_addr : URValue ( XAddress ) a2 ) : URValue XAddress ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) expected_internal_address 
 sender_public_key sender_owner_addr ) . 
 
 Notation " 'expected_internal_address_' '(' sender_public_key sender_owner_addr ')' " := 
 ( expected_internal_address_right 
 sender_public_key sender_owner_addr ) 
 (in custom URValue at level 0 , sender_public_key custom URValue at level 0 
 , sender_owner_addr custom URValue at level 0 ) : ursus_scope . 
 Definition calc_internal_wallet_init_right { a1 a2 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( owner_addr : URValue ( XAddress ) a2 ) : URValue ( StateInitLRecord * XAddress ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_internal_wallet_init 
 pubkey owner_addr ) . 
 
 Notation " 'calc_internal_wallet_init_' '(' pubkey owner_addr ')' " := 
 ( calc_internal_wallet_init_right 
 pubkey owner_addr ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , owner_addr custom URValue at level 0 ) : ursus_scope . 
 Definition is_internal_owner_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) is_internal_owner 
 ) . 
 
 Notation " 'is_internal_owner_' '(' ')' " := 
 ( is_internal_owner_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition check_internal_owner_left { R }  : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_internal_owner 
 ) . 
 
 Notation " 'check_internal_owner_' '(' ')' " := 
 ( check_internal_owner_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition check_external_owner_left { R }  : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_external_owner 
 ) . 
 
 Notation " 'check_external_owner_' '(' ')' " := 
 ( check_external_owner_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition check_owner_left { R }  : UExpression R := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_owner 
 ) . 
 
 Notation " 'check_owner_' '(' ')' " := 
 ( check_owner_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 Definition prepare_wrapper_state_init_and_addr_right { a1 a2 }  ( wrapper_code : URValue ( XCell ) a1 ) ( wrapper_data : URValue ( DWrapperLRecord ) a2 ) : URValue ( StateInitLRecord * XUInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_wrapper_state_init_and_addr 
 wrapper_code wrapper_data ) . 
 
 Notation " 'prepare_wrapper_state_init_and_addr_' '(' wrapper_code wrapper_data ')' " := 
 ( prepare_wrapper_state_init_and_addr_right 
 wrapper_code wrapper_data ) 
 (in custom URValue at level 0 , wrapper_code custom URValue at level 0 
 , wrapper_data custom URValue at level 0 ) : ursus_scope . 



End Calls. 

End FuncNotations.
