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

Require Import CommonNotations.
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

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Import UrsusNotations.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Notation " 'allowance_info.spender' " := ( allowance_info_ι_spender ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.spender' " := ( allowance_info_ι_spender ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'allowance_info.remainingTokens' " := ( allowance_info_ι_remainingTokens ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_record.lend_balance' " := ( lend_record_ι_lend_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_record.lend_balance' " := ( lend_record_ι_lend_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_record.lend_finish_time' " := ( lend_record_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_record.lend_finish_time' " := ( lend_record_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_addr' " := ( lend_array_record_ι_lend_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_addr' " := ( lend_array_record_ι_lend_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_balance' " := ( lend_array_record_ι_lend_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_balance' " := ( lend_array_record_ι_lend_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_finish_time' " := ( lend_array_record_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_finish_time' " := ( lend_array_record_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.name' " := ( details_info_ι_name ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.name' " := ( details_info_ι_name ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.symbol' " := ( details_info_ι_symbol ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.symbol' " := ( details_info_ι_symbol ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.decimals' " := ( details_info_ι_decimals ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.decimals' " := ( details_info_ι_decimals ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.balance' " := ( details_info_ι_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.balance' " := ( details_info_ι_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.root_public_key' " := ( details_info_ι_root_public_key ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.root_public_key' " := ( details_info_ι_root_public_key ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.wallet_public_key' " := ( details_info_ι_wallet_public_key ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.wallet_public_key' " := ( details_info_ι_wallet_public_key ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.root_address' " := ( details_info_ι_root_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.root_address' " := ( details_info_ι_root_address ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.owner_address' " := ( details_info_ι_owner_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.owner_address' " := ( details_info_ι_owner_address ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.lend_ownership' " := ( details_info_ι_lend_ownership ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.lend_ownership' " := ( details_info_ι_lend_ownership ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.lend_balance' " := ( details_info_ι_lend_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.lend_balance' " := ( details_info_ι_lend_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.code' " := ( details_info_ι_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.code' " := ( details_info_ι_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.allowance' " := ( details_info_ι_allowance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.allowance' " := ( details_info_ι_allowance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'details_info.workchain_id' " := ( details_info_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'details_info.workchain_id' " := ( details_info_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope. 
 
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
 
 Definition root_address__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_root_address_ ) : ULValue XAddress ) . 
 Definition root_address__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_root_address_ ) : URValue XAddress false ) . 
 Notation " '_root_address_' " := ( root_address__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_root_address_' " := ( root_address__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition owner_address__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_owner_address_ ) : ULValue ( XMaybe XAddress ) ) . 
 Definition owner_address__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_owner_address_ ) : URValue ( XMaybe XAddress ) false ) . 
 Notation " '_owner_address_' " := ( owner_address__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_owner_address_' " := ( owner_address__right ) (in custom URValue at level 0) : ursus_scope. 
 

 Definition lend_ownership__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_lend_ownership_ ) : ULValue (XHMap addr_std_fixedLRecord lend_recordLRecord) ) . 
 Definition lend_ownership__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_lend_ownership_ ) : URValue (XHMap addr_std_fixedLRecord lend_recordLRecord) false ) . 
 Notation " '_lend_ownership_' " := ( lend_ownership__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_lend_ownership_' " := ( lend_ownership__right ) (in custom URValue at level 0) : ursus_scope. 

 Definition code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_code_ ) : ULValue XCell ) . 
 Definition code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_code_ ) : URValue XCell false ) . 
 Notation " '_code_' " := ( code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_code_' " := ( code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition allowance__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_allowance_ ) : ULValue ( XMaybe allowance_infoLRecord ) ) . 
 Definition allowance__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_allowance_ ) : URValue ( XMaybe allowance_infoLRecord ) false ) . 
 Notation " '_allowance_' " := ( allowance__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_allowance_' " := ( allowance__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_workchain_id_ ) : ULValue XUInteger8 ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DTONTokenWallet_ι_workchain_id_ ) : URValue XUInteger8 false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 

 Notation " 'DTONTokenWalletExternal.name_' " := ( DTONTokenWalletExternal_ι_name_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.name_' " := ( DTONTokenWalletExternal_ι_name_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.symbol_' " := ( DTONTokenWalletExternal_ι_symbol_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.symbol_' " := ( DTONTokenWalletExternal_ι_symbol_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.decimals_' " := ( DTONTokenWalletExternal_ι_decimals_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.decimals_' " := ( DTONTokenWalletExternal_ι_decimals_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.balance_' " := ( DTONTokenWalletExternal_ι_balance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.balance_' " := ( DTONTokenWalletExternal_ι_balance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.root_public_key_' " := ( DTONTokenWalletExternal_ι_root_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.root_public_key_' " := ( DTONTokenWalletExternal_ι_root_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.wallet_public_key_' " := ( DTONTokenWalletExternal_ι_wallet_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.wallet_public_key_' " := ( DTONTokenWalletExternal_ι_wallet_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.root_address_' " := ( DTONTokenWalletExternal_ι_root_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.root_address_' " := ( DTONTokenWalletExternal_ι_root_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.owner_address_' " := ( DTONTokenWalletExternal_ι_owner_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.owner_address_' " := ( DTONTokenWalletExternal_ι_owner_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.code_' " := ( DTONTokenWalletExternal_ι_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.code_' " := ( DTONTokenWalletExternal_ι_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.allowance_' " := ( DTONTokenWalletExternal_ι_allowance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.allowance_' " := ( DTONTokenWalletExternal_ι_allowance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.workchain_id_' " := ( DTONTokenWalletExternal_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletExternal.workchain_id_' " := ( DTONTokenWalletExternal_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.name_' " := ( DTONTokenWalletInternal_ι_name_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.name_' " := ( DTONTokenWalletInternal_ι_name_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.symbol_' " := ( DTONTokenWalletInternal_ι_symbol_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.symbol_' " := ( DTONTokenWalletInternal_ι_symbol_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.decimals_' " := ( DTONTokenWalletInternal_ι_decimals_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.decimals_' " := ( DTONTokenWalletInternal_ι_decimals_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.balance_' " := ( DTONTokenWalletInternal_ι_balance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.balance_' " := ( DTONTokenWalletInternal_ι_balance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.root_public_key_' " := ( DTONTokenWalletInternal_ι_root_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.root_public_key_' " := ( DTONTokenWalletInternal_ι_root_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.wallet_public_key_' " := ( DTONTokenWalletInternal_ι_wallet_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.wallet_public_key_' " := ( DTONTokenWalletInternal_ι_wallet_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.root_address_' " := ( DTONTokenWalletInternal_ι_root_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.root_address_' " := ( DTONTokenWalletInternal_ι_root_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.owner_address_' " := ( DTONTokenWalletInternal_ι_owner_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.owner_address_' " := ( DTONTokenWalletInternal_ι_owner_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.lend_ownership_' " := ( DTONTokenWalletInternal_ι_lend_ownership_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.lend_ownership_' " := ( DTONTokenWalletInternal_ι_lend_ownership_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.code_' " := ( DTONTokenWalletInternal_ι_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.code_' " := ( DTONTokenWalletInternal_ι_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.workchain_id_' " := ( DTONTokenWalletInternal_ι_workchain_id_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTONTokenWalletInternal.workchain_id_' " := ( DTONTokenWalletInternal_ι_workchain_id_ ) (in custom URValue at level 0) : ursus_scope. 
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
 Notation " 'lend_array_record.lend_addr' " := ( lend_array_record_ι_lend_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_addr' " := ( lend_array_record_ι_lend_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_balance' " := ( lend_array_record_ι_lend_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_balance' " := ( lend_array_record_ι_lend_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_finish_time' " := ( lend_array_record_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_finish_time' " := ( lend_array_record_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 


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

 
Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

(**************************************************************************************************)

 Definition transfer_left { R a1 a2 a3 a4 a5 }  
( answer_addr : URValue ( XAddress ) a1 ) ( too : URValue ( XAddress ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) ( grams : URValue ( XUInteger128 ) a4 ) ( return_ownership : URValue ( XBool ) a5 ) : UExpression R ( orb ( orb ( orb ( orb a5 a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) transfer 
 answer_addr too tokens grams return_ownership ) . 
 
 Notation " 'transfer_' '(' answer_addr ',' too ',' tokens ',' grams ',' return_ownership ')' " := 
 ( transfer_left 
 answer_addr too tokens grams return_ownership ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , return_ownership custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferWithNotify_left { R a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( XAddress ) a1 ) ( too : URValue ( XAddress ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) ( grams : URValue ( XUInteger128 ) a4 ) ( return_ownership : URValue ( XBool ) a5 ) ( payload : URValue ( XCell ) a6 ) : UExpression R ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) := 
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
 
 Definition transferToRecipient_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( XAddress ) a1 ) ( recipient_public_key : URValue ( XUInteger256 ) a2 ) ( recipient_internal_owner : URValue ( XAddress ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) ( deploy : URValue ( XBool ) a6 ) ( return_ownership : URValue ( XBool ) a7 ) : UExpression R ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
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
 
 Definition transferToRecipientWithNotify_left { R a1 a2 a3 a4 a5 a6 a7 a8 }  ( answer_addr : URValue ( XAddress ) a1 ) ( recipient_public_key : URValue ( XUInteger256 ) a2 ) ( recipient_internal_owner : URValue ( XAddress ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) ( deploy : URValue ( XBool ) a6 ) ( return_ownership : URValue ( XBool ) a7 ) ( payload : URValue ( XCell ) a8 ) : UExpression R ( orb ( orb ( orb ( orb ( orb ( orb ( orb a8 a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
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
 Definition accept_right { a1 a2 a3 }  ( tokens : URValue ( XUInteger128 ) a1 ) ( answer_addr : URValue ( XAddress ) a2 ) ( keep_grams : URValue ( XUInteger128 ) a3 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) accept 
 tokens answer_addr keep_grams ) . 
 
 Notation " 'accept_' '(' tokens answer_addr keep_grams ')' " := 
 ( accept_right 
 tokens answer_addr keep_grams ) 
 (in custom URValue at level 0 , tokens custom URValue at level 0 
 , answer_addr custom URValue at level 0 
 , keep_grams custom URValue at level 0 ) : ursus_scope . 
 
 Definition internalTransfer_left { R a1 a2 a3 a4 a5 a6 }  ( tokens : URValue ( XUInteger128 ) a1 ) ( answer_addr : URValue ( XAddress ) a2 ) ( sender_pubkey : URValue ( XUInteger256 ) a3 ) ( sender_owner : URValue ( XAddress ) a4 ) ( notify_receiver : URValue ( XBool ) a5 ) ( payload : URValue ( XCell ) a6 ) : UExpression R true := 
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
 
 Definition destroy_left { R a1 }  ( dest : URValue ( XAddress ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) destroy 
 dest ) . 
 
 Notation " 'destroy_' '(' dest ')' " := 
 ( destroy_left 
 dest ) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 ) : ursus_scope . 
 
 Definition burn_left { R a1 a2 }  ( out_pubkey : URValue ( XUInteger256 ) a1 ) ( out_internal_owner : URValue ( XAddress ) a2 ) : UExpression R ( orb a2 a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) burn 
 out_pubkey out_internal_owner ) . 
 
 Notation " 'burn_' '(' out_pubkey out_internal_owner ')' " := 
 ( burn_left 
 out_pubkey out_internal_owner ) 
 (in custom ULValue at level 0 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 ) : ursus_scope . 
 
 Definition lendOwnership_left { R a1 a2 a3 a4 a5 a6 a7 }  ( answer_addr : URValue ( XAddress ) a1 ) ( grams : URValue ( XUInteger128 ) a2 ) ( std_dest : URValue ( XUInteger256 ) a3 ) ( lend_balance : URValue ( XUInteger128 ) a4 ) ( lend_finish_time : URValue ( XUInteger32 ) a5 ) ( deploy_init_cl : URValue ( XCell ) a6 ) ( payload : URValue ( XCell ) a7 ) : UExpression R true := 
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
 
 Definition returnOwnership_left { R a1 }  ( tokens : URValue ( XUInteger128 ) a1 ) : UExpression R a1 := 
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
 Definition getRootAddress_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootAddress 
 ) . 
 
 Notation " 'getRootAddress_' '(' ')' " := 
 ( getRootAddress_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getOwnerAddress_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwnerAddress 
 ) . 
 
 Notation " 'getOwnerAddress_' '(' ')' " := 
 ( getOwnerAddress_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getCode_right  : URValue XCell false := 
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
 
 Definition approve_left { R a1 a2 a3 }  ( spender : URValue ( XAddress ) a1 ) ( remainingTokens : URValue ( XUInteger128 ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) approve 
 spender remainingTokens tokens ) . 
 
 Notation " 'approve_' '(' spender remainingTokens tokens ')' " := 
 ( approve_left 
 spender remainingTokens tokens ) 
 (in custom ULValue at level 0 , spender custom URValue at level 0 
 , remainingTokens custom URValue at level 0 
 , tokens custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferFrom_left { R a1 a2 a3 a4 a5 }  ( answer_addr : URValue ( XAddress ) a1 ) ( from : URValue ( XAddress ) a2 ) ( too : URValue ( XAddress ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) : UExpression R ( orb ( orb ( orb ( orb a5 a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) transferFrom 
 answer_addr from too tokens grams ) . 
 
 Notation " 'transferFrom_' '(' answer_addr ',' from ',' too ',' tokens ',' grams ')' " := 
 ( transferFrom_left 
 answer_addr from too tokens grams ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , from custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 
 Definition transferFromWithNotify_left { R a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( XAddress ) a1 ) ( from : URValue ( XAddress ) a2 ) ( too : URValue ( XAddress ) a3 ) ( tokens : URValue ( XUInteger128 ) a4 ) ( grams : URValue ( XUInteger128 ) a5 ) ( payload : URValue ( XCell ) a6 ) : UExpression R ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) transferFromWithNotify 
 answer_addr from too tokens grams payload ) . 
 
 Notation " 'transferFromWithNotify_' '(' answer_addr ',' from ',' too ',' tokens ',' grams ',' payload ')' " := 
 ( transferFromWithNotify_left 
 answer_addr from too tokens grams payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , from custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 
 
 Definition internalTransferFrom_left { R a1 a2 a3 a4 a5 }  ( answer_addr : URValue ( XAddress ) a1 ) ( too : URValue ( XAddress ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) ( notify_receiver : URValue ( XBool ) a4 ) ( payload : URValue ( XCell ) a5 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) internalTransferFrom 
 answer_addr too tokens notify_receiver payload ) . 
 
 Notation " 'internalTransferFrom_' '(' answer_addr ',' too ',' tokens ',' notify_receiver ',' payload ')' " := 
 ( internalTransferFrom_left 
 answer_addr too tokens notify_receiver payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 
 , too custom URValue at level 0 
 , tokens custom URValue at level 0 
 , notify_receiver custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 

 Definition disapprove_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) disapprove 
 ) . 
 
 Notation " 'disapprove_' '(' ')' " := 
 ( disapprove_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 Definition _on_bounced_right { a1 a2 }  ( msg : URValue ( XCell ) a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue XUInteger true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _on_bounced 
 msg msg_body ) . 
 
 Notation " '_on_bounced_' '(' msg msg_body ')' " := 
 ( _on_bounced_right 
 msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope .

(*  Definition prepare_wallet_data_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XUInteger8 ) a3 ) ( root_public_key : URValue ( XUInteger256 ) a4 ) ( wallet_public_key : URValue ( XUInteger256 ) a5 ) ( root_address : URValue ( XAddress ) a6 ) ( owner_address : URValue ( XMaybe XAddress ) a7 ) ( code : URValue ( XCell ) a8 ) ( workchain_id : URValue ( XUInteger8 ) a9 ) : URValue DTONTokenWalletLRecord ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
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
 *) 

(* Definition prepare_wallet_state_init_and_addr_right { a1 }  ( wallet_data : URValue ( DTONTokenWalletLRecord ) a1 ) : URValue ( StateInitLRecord # XUInteger256 ) a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) prepare_wallet_state_init_and_addr 
 wallet_data ) . 
 
 Notation " 'prepare_wallet_state_init_and_addr_' '(' wallet_data ')' " := 
 ( prepare_wallet_state_init_and_addr_right 
 wallet_data ) 
 (in custom URValue at level 0 , wallet_data custom URValue at level 0 ) : ursus_scope . 
 Definition prepare_external_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XUInteger8 ) a3 ) ( root_public_key : URValue ( XUInteger256 ) a4 ) ( wallet_public_key : URValue ( XUInteger256 ) a5 ) ( root_address : URValue ( XAddress ) a6 ) ( owner_address : URValue ( XMaybe XAddress ) a7 ) ( code : URValue ( XCell ) a8 ) ( workchain_id : URValue ( XUInteger8 ) a9 ) : URValue ( StateInitLRecord # XUInteger256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_external_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 *) 
(*  Notation " 'prepare_external_wallet_state_init_and_addr_' '(' name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ')' " := 
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
 Definition prepare_internal_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XUInteger8 ) a3 ) ( root_public_key : URValue ( XUInteger256 ) a4 ) ( wallet_public_key : URValue ( XUInteger256 ) a5 ) ( root_address : URValue ( XAddress ) a6 ) ( owner_address : URValue ( XMaybe XAddress ) a7 ) ( code : URValue ( XCell ) a8 ) ( workchain_id : URValue ( XUInteger8 ) a9 ) : URValue ( StateInitLRecord # XUInteger256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_internal_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 *) 
(*  Notation " 'prepare_internal_wallet_state_init_and_addr_' '(' name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ')' " := 
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
 *)
(*  Definition prepare_root_state_init_and_addr_right { a1 a2 }  ( root_code : URValue ( XCell ) a1 ) ( root_data : URValue ( DRootTokenContractLRecord ) a2 ) : URValue ( StateInitLRecord # XUInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_root_state_init_and_addr 
 root_code root_data ) . 
 
 Notation " 'prepare_root_state_init_and_addr_' '(' root_code root_data ')' " := 
 ( prepare_root_state_init_and_addr_right 
 root_code root_data ) 
 (in custom URValue at level 0 , root_code custom URValue at level 0 
 , root_data custom URValue at level 0 ) : ursus_scope . 
 *)

End Calls. 

End FuncNotations.
