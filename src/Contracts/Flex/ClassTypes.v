Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdNotations.
Require Import UrsusStdLib.stdFuncNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.
Require Import FinProof.ProgrammingWith.  
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Import CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 1 *) Inductive lend_recordFields := | lend_record_ι_lend_balance | lend_record_ι_lend_finish_time .
(* 1 *) Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address .
(* 1 *) Inductive allowance_infoFields := | allowance_info_ι_spender | allowance_info_ι_remainingTokens .
(* 1 *) Inductive DWrapperFields := | DWrapper_ι_name_ | DWrapper_ι_symbol_ | DWrapper_ι_decimals_ | DWrapper_ι_workchain_id_ | DWrapper_ι_root_public_key_ | DWrapper_ι_total_granted_ | DWrapper_ι_internal_wallet_code_ | DWrapper_ι_owner_address_ | DWrapper_ι_start_balance_ | DWrapper_ι_external_wallet_ .
(* 1 *) Inductive DXchgPairFields := | DXchgPair_ι_flex_addr_ | DXchgPair_ι_tip3_major_root_ | DXchgPair_ι_tip3_minor_root_ | DXchgPair_ι_min_amount_ | DXchgPair_ι_notify_addr_ .
(* 1 *) Inductive DTONTokenWalletExternalFields := | DTONTokenWalletExternal_ι_name_ | DTONTokenWalletExternal_ι_symbol_ | DTONTokenWalletExternal_ι_decimals_ | DTONTokenWalletExternal_ι_balance_ | DTONTokenWalletExternal_ι_root_public_key_ | DTONTokenWalletExternal_ι_wallet_public_key_ | DTONTokenWalletExternal_ι_root_address_ | DTONTokenWalletExternal_ι_owner_address_ | DTONTokenWalletExternal_ι_code_ | DTONTokenWalletExternal_ι_allowance_ | DTONTokenWalletExternal_ι_workchain_id_ .
(* 1 *) Inductive DTONTokenWalletInternalFields := | DTONTokenWalletInternal_ι_name_ | DTONTokenWalletInternal_ι_symbol_ | DTONTokenWalletInternal_ι_decimals_ | DTONTokenWalletInternal_ι_balance_ | DTONTokenWalletInternal_ι_root_public_key_ | DTONTokenWalletInternal_ι_wallet_public_key_ | DTONTokenWalletInternal_ι_root_address_ | DTONTokenWalletInternal_ι_owner_address_ | DTONTokenWalletInternal_ι_lend_ownership_ | DTONTokenWalletInternal_ι_code_ | DTONTokenWalletInternal_ι_workchain_id_ .
(* 1 *) Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 1 *) Inductive DTradingPairFields := | DTradingPair_ι_flex_addr_ | DTradingPair_ι_tip3_root_ | DTradingPair_ι_deploy_value_ | DTradingPair_ι_min_amount_ | DTradingPair_ι_notify_addr_.
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 1 *) Inductive ListingConfigFields := | ListingConfig_ι_register_wrapper_cost | ListingConfig_ι_reject_wrapper_cost | ListingConfig_ι_wrapper_deploy_value | ListingConfig_ι_wrapper_keep_balance | ListingConfig_ι_ext_wallet_balance | ListingConfig_ι_set_internal_wallet_value | ListingConfig_ι_register_pair_cost | ListingConfig_ι_reject_pair_cost | ListingConfig_ι_pair_deploy_value | ListingConfig_ι_pair_keep_balance | ListingConfig_ι_register_return_value .
(* 1 *) Inductive WrapperListingRequestFields := | WrapperListingRequest_ι_client_addr | WrapperListingRequest_ι_client_funds | WrapperListingRequest_ι_tip3cfg .
(* 1 *) Inductive WrapperListingRequestWithPubkeyFields := | WrapperListingRequestWithPubkey_ι_wrapper_pubkey | WrapperListingRequestWithPubkey_ι_request .
(* 1 *) Inductive TradingPairListingRequestFields := | TradingPairListingRequest_ι_client_addr | TradingPairListingRequest_ι_client_funds | TradingPairListingRequest_ι_tip3_root | TradingPairListingRequest_ι_min_amount | TradingPairListingRequest_ι_notify_addr .
(* 1 *) Inductive TradingPairListingRequestWithPubkeyFields := | TradingPairListingRequestWithPubkey_ι_wrapper_pubkey | TradingPairListingRequestWithPubkey_ι_request .
(* 1 *) Inductive XchgPairListingRequestFields := | XchgPairListingRequest_ι_client_addr | XchgPairListingRequest_ι_client_funds | XchgPairListingRequest_ι_tip3_major_root | XchgPairListingRequest_ι_tip3_minor_root | XchgPairListingRequest_ι_min_amount | XchgPairListingRequest_ι_notify_addr .
(* 1 *) Inductive XchgPairListingRequestWithPubkeyFields := | XchgPairListingRequestWithPubkey_ι_request_pubkey | XchgPairListingRequestWithPubkey_ι_request .
(* 1 *) Inductive FlexOwnershipInfoFields := | FlexOwnershipInfo_ι_deployer_pubkey | FlexOwnershipInfo_ι_ownership_description | FlexOwnershipInfo_ι_owner_contract .
(* 1 *) Inductive FlexDetailsFields := | FlexDetails_ι_initialized | FlexDetails_ι_tons_cfg | FlexDetails_ι_listing_cfg | FlexDetails_ι_trading_pair_code | FlexDetails_ι_xchg_pair_code | FlexDetails_ι_deals_limit | FlexDetails_ι_ownership | FlexDetails_ι_wrapper_listing_requests | FlexDetails_ι_trading_pair_listing_requests | FlexDetails_ι_xchg_pair_listing_requests .
(* 2 *) Definition addr_std_fixedL : list Type := 
 [ ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ] .
Elpi GeneratePruvendoRecord addr_std_fixedL addr_std_fixedFields . 
 Opaque addr_std_fixedLRecord . 

(* 2 *) Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 Opaque TickTockLRecord .

(* 2 *) Definition lend_recordL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord lend_recordL lend_recordFields . 
 Opaque lend_recordLRecord . 

(* 2 *) Definition allowance_infoL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord allowance_infoL allowance_infoFields . 
 Opaque allowance_infoLRecord . 

(* 2 *) Definition DWrapperL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( Grams ) : Type ; 
 ( ( XMaybe XAddress (* ITONTokenWalletPtrLRecord *) ) ) : Type ] .
Elpi GeneratePruvendoRecord DWrapperL DWrapperFields . 
 Opaque DWrapperLRecord . 

(* 2 *) Definition DXchgPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord DXchgPairL DXchgPairFields . 
 Opaque DXchgPairLRecord .

(* 2 *) Definition DTONTokenWalletExternalL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( XCell ) : Type ; 
 ( ( XMaybe allowance_infoLRecord ) ) : Type ; 
 ( XInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletExternalL DTONTokenWalletExternalFields . 
 Opaque DTONTokenWalletExternalLRecord . 

(* 2 *) Definition DTONTokenWalletInternalL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( XHMap addr_std_fixedLRecord lend_recordLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( XInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord DTONTokenWalletInternalL DTONTokenWalletInternalFields . 
 Opaque DTONTokenWalletInternalLRecord . 

(* 2 *) Definition Tip3ConfigL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord Tip3ConfigL Tip3ConfigFields . 
 Opaque Tip3ConfigLRecord . 

(* 2 *) Definition StateInitL : list Type := 
 [ ( ( XMaybe XInteger ) ) : Type ;
 ( ( XMaybe TickTockLRecord ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
 Opaque StateInitLRecord . 

(* 2 *) Definition DTradingPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ;
 ( XInteger128 ) : Type ;
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord DTradingPairL DTradingPairFields . 
 Opaque DTradingPairLRecord . 

(* 2 *) Definition TonsConfigL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord TonsConfigL TonsConfigFields . 
 Opaque TonsConfigLRecord . 

(* 2 *) Definition ListingConfigL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord ListingConfigL ListingConfigFields . 
 Opaque ListingConfigLRecord . 

(* 2 *) Definition WrapperListingRequestL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ] .
Elpi GeneratePruvendoRecord WrapperListingRequestL WrapperListingRequestFields . 
 Opaque WrapperListingRequestLRecord . 

(* 2 *) Definition WrapperListingRequestWithPubkeyL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( WrapperListingRequestLRecord ) : Type ] .
Elpi GeneratePruvendoRecord WrapperListingRequestWithPubkeyL WrapperListingRequestWithPubkeyFields . 
 Opaque WrapperListingRequestWithPubkeyLRecord . 

(* 2 *) Definition TradingPairListingRequestL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord TradingPairListingRequestL TradingPairListingRequestFields . 
 Opaque TradingPairListingRequestLRecord . 

(* 2 *) Definition TradingPairListingRequestWithPubkeyL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( TradingPairListingRequestLRecord ) : Type ] .
Elpi GeneratePruvendoRecord TradingPairListingRequestWithPubkeyL TradingPairListingRequestWithPubkeyFields . 
 Opaque TradingPairListingRequestWithPubkeyLRecord . 

(* 2 *) Definition XchgPairListingRequestL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord XchgPairListingRequestL XchgPairListingRequestFields . 
 Opaque XchgPairListingRequestLRecord . 

(* 2 *) Definition XchgPairListingRequestWithPubkeyL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( XchgPairListingRequestLRecord ) : Type ] .
Elpi GeneratePruvendoRecord XchgPairListingRequestWithPubkeyL XchgPairListingRequestWithPubkeyFields . 
 Opaque XchgPairListingRequestWithPubkeyLRecord . 

(* 2 *) Definition FlexOwnershipInfoL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( XString ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ] .
Elpi GeneratePruvendoRecord FlexOwnershipInfoL FlexOwnershipInfoFields . 
 Opaque FlexOwnershipInfoLRecord . 

(* 2 *) Definition FlexDetailsL : list Type := 
 [ ( XBool ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( ListingConfigLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( XCell ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( FlexOwnershipInfoLRecord ) : Type ; 
 ( ( XHMap XInteger WrapperListingRequestWithPubkeyLRecord ) ) : Type ; 
 ( ( XHMap XInteger TradingPairListingRequestWithPubkeyLRecord ) ) : Type ; 
 ( ( XHMap XInteger XchgPairListingRequestWithPubkeyLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord FlexDetailsL FlexDetailsFields . 
 Opaque FlexDetailsLRecord . 


Check XBool.
 

End ClassTypes .
 