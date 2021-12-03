Require Import FinProof.ProgrammingWith. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonTypes.

(* 1 *) Inductive ListingConfigFields := | ListingConfig_ι_register_wrapper_cost | ListingConfig_ι_reject_wrapper_cost | ListingConfig_ι_wrapper_deploy_value | ListingConfig_ι_wrapper_keep_balance | ListingConfig_ι_ext_wallet_balance | ListingConfig_ι_set_internal_wallet_value | ListingConfig_ι_register_pair_cost | ListingConfig_ι_reject_pair_cost | ListingConfig_ι_pair_deploy_value | ListingConfig_ι_pair_keep_balance | ListingConfig_ι_register_return_value .
(* 2 *) Inductive WrapperListingRequestFields := | WrapperListingRequest_ι_client_addr | WrapperListingRequest_ι_client_funds | WrapperListingRequest_ι_tip3cfg .
(* 3 *) Inductive WrapperListingRequestWithPubkeyFields := | WrapperListingRequestWithPubkey_ι_wrapper_pubkey | WrapperListingRequestWithPubkey_ι_request .
(* 4 *) Inductive TradingPairListingRequestFields := | TradingPairListingRequest_ι_client_addr | TradingPairListingRequest_ι_client_funds | TradingPairListingRequest_ι_tip3_root | TradingPairListingRequest_ι_min_amount | TradingPairListingRequest_ι_notify_addr .
(* 5 *) Inductive TradingPairListingRequestWithPubkeyFields := | TradingPairListingRequestWithPubkey_ι_wrapper_pubkey | TradingPairListingRequestWithPubkey_ι_request .
(* 6 *) Inductive XchgPairListingRequestFields := | XchgPairListingRequest_ι_client_addr | XchgPairListingRequest_ι_client_funds | XchgPairListingRequest_ι_tip3_major_root | XchgPairListingRequest_ι_tip3_minor_root | XchgPairListingRequest_ι_min_amount | XchgPairListingRequest_ι_notify_addr .
(* 7 *) Inductive XchgPairListingRequestWithPubkeyFields := | XchgPairListingRequestWithPubkey_ι_request_pubkey | XchgPairListingRequestWithPubkey_ι_request .
(* 8 *) Inductive FlexOwnershipInfoFields := | FlexOwnershipInfo_ι_deployer_pubkey | FlexOwnershipInfo_ι_ownership_description | FlexOwnershipInfo_ι_owner_contract .
(* 9 *) Inductive FlexDetailsFields := | FlexDetails_ι_initialized | FlexDetails_ι_tons_cfg | FlexDetails_ι_listing_cfg | FlexDetails_ι_trading_pair_code | FlexDetails_ι_xchg_pair_code | FlexDetails_ι_deals_limit | FlexDetails_ι_ownership | FlexDetails_ι_wrapper_listing_requests | FlexDetails_ι_trading_pair_listing_requests | FlexDetails_ι_xchg_pair_listing_requests .
(* 10 *) Inductive DFlexFields := 
| DFlex_ι_deployer_pubkey_ 
| DFlex_ι_workchain_id_ 
| DFlex_ι_ownership_description_ 
| DFlex_ι_owner_address_ 
| DFlex_ι_tons_cfg_ 
| DFlex_ι_listing_cfg_ 
| DFlex_ι_pair_code_ 
| DFlex_ι_xchg_pair_code_ 
| DFlex_ι_price_code_ 
| DFlex_ι_xchg_price_code_ 
| DFlex_ι_ext_wallet_code_ 
| DFlex_ι_flex_wallet_code_ 
| DFlex_ι_wrapper_code_ 
| DFlex_ι_deals_limit_ 
| DFlex_ι_wrapper_listing_requests_
| DFlex_ι_trading_pair_listing_requests_
| DFlex_ι_xchg_pair_listing_requests_ .


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) Definition ListingConfigL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord ListingConfigL ListingConfigFields . 

Opaque Tip3ConfigLRecord.
(* 2 *) Definition WrapperListingRequestL : list Type := 
 [ ( address ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ] .
Elpi GeneratePruvendoRecord WrapperListingRequestL WrapperListingRequestFields . 
 
Opaque WrapperListingRequestLRecord.
(* 3 *) Definition WrapperListingRequestWithPubkeyL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( WrapperListingRequestLRecord ) : Type ] .
Elpi GeneratePruvendoRecord WrapperListingRequestWithPubkeyL WrapperListingRequestWithPubkeyFields . 

Opaque addr_stdLRecord address.
(* 4 *) Definition TradingPairListingRequestL : list Type := 
 [ ( address ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( address ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( address ) : Type ] .
Elpi GeneratePruvendoRecord TradingPairListingRequestL TradingPairListingRequestFields .  

Opaque TradingPairListingRequestLRecord.
(* 5 *) Definition TradingPairListingRequestWithPubkeyL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( TradingPairListingRequestLRecord ) : Type ] .
Elpi GeneratePruvendoRecord TradingPairListingRequestWithPubkeyL TradingPairListingRequestWithPubkeyFields . 
 
(* 6 *) Definition XchgPairListingRequestL : list Type := 
 [ ( address ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( address ) : Type ; 
 ( address ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( address ) : Type ] .
Elpi GeneratePruvendoRecord XchgPairListingRequestL XchgPairListingRequestFields . 

Opaque  XchgPairListingRequestLRecord.
(* 7 *) Definition XchgPairListingRequestWithPubkeyL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( XchgPairListingRequestLRecord ) : Type ] .
Elpi GeneratePruvendoRecord XchgPairListingRequestWithPubkeyL XchgPairListingRequestWithPubkeyFields . 

(* 8 *) Definition FlexOwnershipInfoL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( XString ) : Type ; 
 ( ( XMaybe address ) ) : Type ] .
Elpi GeneratePruvendoRecord FlexOwnershipInfoL FlexOwnershipInfoFields . 

(* 9 *) Definition FlexDetailsL : list Type := 
 [ ( XBool ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( ListingConfigLRecord ) : Type ; 
 cell_ : Type ; 
 cell_ : Type ; 
 ( XUInteger8 ) : Type ; 
 ( FlexOwnershipInfoLRecord ) : Type ; 
 ( ( XHMap XUInteger WrapperListingRequestWithPubkeyLRecord ) ) : Type ; 
 ( ( XHMap XUInteger TradingPairListingRequestWithPubkeyLRecord ) ) : Type ; 
 ( ( XHMap XUInteger XchgPairListingRequestWithPubkeyLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord FlexDetailsL FlexDetailsFields . 
 
(* 10 *) Definition DFlexL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( XInteger (* XUInteger8 *) ) : Type ; (* _workchain_id_ *)
 ( XString ) : Type ; 
 ( ( XMaybe address ) ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( ListingConfigLRecord ) : Type ; 
 ( ( XMaybe cell_ ) ) : Type ; 
 ( ( XMaybe cell_ ) ) : Type ; 
 ( ( XMaybe cell_ ) ) : Type ; 
 ( ( XMaybe cell_ ) ) : Type ; 
 ( ( XMaybe cell_ ) ) : Type ; 
 ( ( XMaybe cell_ ) ) : Type ; 
 ( ( XMaybe cell_ ) ) : Type ; 
  ( XUInteger8 ) : Type ;
 ( (XHMap XUInteger256  WrapperListingRequestLRecord)) : Type ; 
 ( (XHMap XUInteger256  TradingPairListingRequestLRecord)) : Type ; 
 ( (XHMap XUInteger256  XchgPairListingRequestLRecord)) : Type ] .
Elpi GeneratePruvendoRecord DFlexL DFlexFields . 
 
End ClassTypes .
 