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

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Fail Check OutgoingMessage_default.

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
 
 Definition wallet_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_wallet_code_ ) : ULValue (XMaybe XCell) ) . 
 Definition wallet_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_wallet_code_ ) : URValue (XMaybe XCell) false ) . 
 Notation " '_wallet_code_' " := ( wallet_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_wallet_code_' " := ( wallet_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition owner_address__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_owner_address_ ) : ULValue ( XMaybe XAddress ) ) . 
 Definition owner_address__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_owner_address_ ) : URValue ( XMaybe XAddress ) false ) . 
 Notation " '_owner_address_' " := ( owner_address__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_owner_address_' " := ( owner_address__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition start_balance__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_start_balance_ ) : ULValue XUInteger ) . 
 Definition start_balance__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DRootTokenContract_ι_start_balance_ ) : URValue XUInteger false ) . 
 Notation " '_start_balance_' " := ( start_balance__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_start_balance_' " := ( start_balance__right ) (in custom URValue at level 0) : ursus_scope. 

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
 Notation " 'DRootTokenContract.name_' " := ( DRootTokenContract_ι_name_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.name_' " := ( DRootTokenContract_ι_name_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.symbol_' " := ( DRootTokenContract_ι_symbol_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.symbol_' " := ( DRootTokenContract_ι_symbol_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.decimals_' " := ( DRootTokenContract_ι_decimals_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.decimals_' " := ( DRootTokenContract_ι_decimals_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.root_public_key_' " := ( DRootTokenContract_ι_root_public_key_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.root_public_key_' " := ( DRootTokenContract_ι_root_public_key_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.total_supply_' " := ( DRootTokenContract_ι_total_supply_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.total_supply_' " := ( DRootTokenContract_ι_total_supply_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.total_granted_' " := ( DRootTokenContract_ι_total_granted_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.total_granted_' " := ( DRootTokenContract_ι_total_granted_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.wallet_code_' " := ( DRootTokenContract_ι_wallet_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.wallet_code_' " := ( DRootTokenContract_ι_wallet_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.owner_address_' " := ( DRootTokenContract_ι_owner_address_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.owner_address_' " := ( DRootTokenContract_ι_owner_address_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.start_balance_' " := ( DRootTokenContract_ι_start_balance_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DRootTokenContract.start_balance_' " := ( DRootTokenContract_ι_start_balance_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_addr' " := ( lend_array_record_ι_lend_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_addr' " := ( lend_array_record_ι_lend_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_balance' " := ( lend_array_record_ι_lend_balance ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_balance' " := ( lend_array_record_ι_lend_balance ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_finish_time' " := ( lend_array_record_ι_lend_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'lend_array_record.lend_finish_time' " := ( lend_array_record_ι_lend_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 


 
Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

(**************************************************************************************************)

 Definition constructor_left { R a1 a2 a3 a4 a5 a6 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( XUInteger8 ) a3 ) ( root_public_key : URValue ( XUInteger256 ) a4 ) ( root_owner : URValue ( XAddress ) a5 ) ( total_supply : URValue ( XUInteger128 ) a6 ) : UExpression R true := 
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
 Definition setWalletCode_right { a1 }  ( wallet_code : URValue ( XCell ) a1 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setWalletCode 
 wallet_code ) . 
 
 Notation " 'setWalletCode_' '(' wallet_code ')' " := 
 ( setWalletCode_right 
 wallet_code ) 
 (in custom URValue at level 0 , wallet_code custom URValue at level 0 ) : ursus_scope . 
 Definition deployWallet_right { a1 a2 a3 a4 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( internal_owner : URValue ( XAddress ) a2 ) ( tokens : URValue ( XUInteger128 ) a3 ) ( grams : URValue ( XUInteger128 ) a4 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) deployWallet 
 pubkey internal_owner tokens grams ) . 
 
 Notation " 'deployWallet_' '(' pubkey internal_owner tokens grams ')' " := 
 ( deployWallet_right 
 pubkey internal_owner tokens grams ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 Definition deployEmptyWallet_right { a1 a2 a3 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( internal_owner : URValue ( XAddress ) a2 ) ( grams : URValue ( XUInteger128 ) a3 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) deployEmptyWallet 
 pubkey internal_owner grams ) . 
 
 Notation " 'deployEmptyWallet_' '(' pubkey internal_owner grams ')' " := 
 ( deployEmptyWallet_right 
 pubkey internal_owner grams ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 
 Definition grant_left { R a1 a2 a3 }  ( dest : URValue ( XAddress ) a1 ) ( tokens : URValue ( XUInteger128 ) a2 ) ( grams : URValue ( XUInteger128 ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) grant 
 dest tokens grams ) . 
 
 Notation " 'grant_' '(' dest tokens grams ')' " := 
 ( grant_left 
 dest tokens grams ) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 
 , tokens custom URValue at level 0 
 , grams custom URValue at level 0 ) : ursus_scope . 
 Definition mint_right { a1 }  ( tokens : URValue ( XUInteger128 ) a1 ) : URValue XBool a1 := 
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
 Definition hasWalletCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasWalletCode 
 ) . 
 
 Notation " 'hasWalletCode_' '(' ')' " := 
 ( hasWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getWalletCode_right  : URValue XCell false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getWalletCode 
 ) . 
 
 Notation " 'getWalletCode_' '(' ')' " := 
 ( getWalletCode_right 
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
 Definition _on_bounced_right { a1 a2 }  ( cell : URValue XCell a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue XUInteger true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _on_bounced 
 cell msg_body ) . 
 
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

 Definition _fallback_right { a1 a2 }  ( x : URValue XCell a1 ) ( y : URValue XSlice a2 ) : URValue XUInteger (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 x y ) . 
 
 Notation " '_fallback_' '(' x ',' y ')' " := 
 ( _fallback_right 
 x y ) 
 (in custom URValue at level 0 , 
x custom URValue at level 0 ,
y custom URValue at level 0 ) : ursus_scope . 

 Definition optional_owner_right { a1 }  ( owner : URValue ( XAddress ) a1 ) : URValue (XMaybe XAddress) a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) optional_owner 
 owner ) . 
 
 Notation " 'optional_owner_' '(' owner ')' " := 
 ( optional_owner_right 
 owner ) 
 (in custom URValue at level 0 , owner custom URValue at level 0 ) : ursus_scope . 

 Definition workchain_id_right  : URValue XUInteger8 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) workchain_id 
 ) . 
 
 Notation " 'workchain_id_' '(' ')' " := 
 ( workchain_id_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition calc_wallet_init_right { a1 a2 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( owner_addr : URValue ( XAddress ) a2 ) : URValue ( StateInitLRecord # XAddress ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_wallet_init 
 pubkey owner_addr ) . 
 
 Notation " 'calc_wallet_init_' '(' pubkey owner_addr ')' " := 
 ( calc_wallet_init_right 
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
 
 Definition check_external_owner_left { R a1 }  ( allow_pubkey_owner_in_internal_node : URValue ( XBool ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) check_external_owner 
 allow_pubkey_owner_in_internal_node ) . 
 
 Notation " 'check_external_owner_' '(' allow_pubkey_owner_in_internal_node ')' " := 
 ( check_external_owner_left 
 allow_pubkey_owner_in_internal_node ) 
 (in custom ULValue at level 0 , allow_pubkey_owner_in_internal_node custom URValue at level 0 ) : ursus_scope . 
 
 Definition check_owner_left { R a1 }  ( false : URValue XBool a1 ) : UExpression R a1 := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) check_owner 
 false ) . 
 
 Notation " 'check_owner_' '(' false ')' " := 
 ( check_owner_left 
 false ) 
 (in custom ULValue at level 0 , false custom URValue at level 0 ) : ursus_scope . 
 Definition prepare_root_state_init_and_addr_right { a1 a2 }  ( root_code : URValue ( XCell ) a1 ) ( root_data : URValue ( DRootTokenContractLRecord ) a2 ) : URValue ( StateInitLRecord # XUInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_root_state_init_and_addr 
 root_code root_data ) . 
 
 Notation " 'prepare_root_state_init_and_addr_' '(' root_code root_data ')' " := 
 ( prepare_root_state_init_and_addr_right 
 root_code root_data ) 
 (in custom URValue at level 0 , root_code custom URValue at level 0 
 , root_data custom URValue at level 0 ) : ursus_scope . 


End Calls. 

End FuncNotations.
