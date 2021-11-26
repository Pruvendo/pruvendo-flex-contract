Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdFunc.
Require Import UrsusStdLib.Cpp.stdNotations.
Require Import UrsusStdLib.Cpp.stdFuncNotations.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import FinProof.ProgrammingWith.  
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.

(* 1 *) 
(* 1 *) Inductive ListingConfigFields := | ListingConfig_ι_register_wrapper_cost | ListingConfig_ι_reject_wrapper_cost | ListingConfig_ι_wrapper_deploy_value | ListingConfig_ι_wrapper_keep_balance | ListingConfig_ι_ext_wallet_balance | ListingConfig_ι_set_internal_wallet_value | ListingConfig_ι_register_pair_cost | ListingConfig_ι_reject_pair_cost | ListingConfig_ι_pair_deploy_value | ListingConfig_ι_pair_keep_balance | ListingConfig_ι_register_return_value .
(* 1 *) Inductive WrapperListingRequestFields := | WrapperListingRequest_ι_client_addr | WrapperListingRequest_ι_client_funds | WrapperListingRequest_ι_tip3cfg .
(* 1 *) Inductive WrapperListingRequestWithPubkeyFields := | WrapperListingRequestWithPubkey_ι_wrapper_pubkey | WrapperListingRequestWithPubkey_ι_request .
(* 1 *) Inductive TradingPairListingRequestFields := | TradingPairListingRequest_ι_client_addr | TradingPairListingRequest_ι_client_funds | TradingPairListingRequest_ι_tip3_root | TradingPairListingRequest_ι_min_amount | TradingPairListingRequest_ι_notify_addr .
(* 1 *) Inductive TradingPairListingRequestWithPubkeyFields := | TradingPairListingRequestWithPubkey_ι_wrapper_pubkey | TradingPairListingRequestWithPubkey_ι_request .
(* 1 *) Inductive XchgPairListingRequestFields := | XchgPairListingRequest_ι_client_addr | XchgPairListingRequest_ι_client_funds | XchgPairListingRequest_ι_tip3_major_root | XchgPairListingRequest_ι_tip3_minor_root | XchgPairListingRequest_ι_min_amount | XchgPairListingRequest_ι_notify_addr .
(* 1 *) Inductive XchgPairListingRequestWithPubkeyFields := | XchgPairListingRequestWithPubkey_ι_request_pubkey | XchgPairListingRequestWithPubkey_ι_request .
(* 1 *) Inductive FlexOwnershipInfoFields := | FlexOwnershipInfo_ι_deployer_pubkey | FlexOwnershipInfo_ι_ownership_description | FlexOwnershipInfo_ι_owner_contract .
(* 1 *) Inductive FlexDetailsFields := | FlexDetails_ι_initialized | FlexDetails_ι_tons_cfg | FlexDetails_ι_listing_cfg | FlexDetails_ι_trading_pair_code | FlexDetails_ι_xchg_pair_code | FlexDetails_ι_deals_limit | FlexDetails_ι_ownership | FlexDetails_ι_wrapper_listing_requests | FlexDetails_ι_trading_pair_listing_requests | FlexDetails_ι_xchg_pair_listing_requests .
(* 1 *) Inductive DFlexFields := 
| deployer_pubkey_ 
| workchain_id_ 
| ownership_description_ 
| owner_address_ 
| tons_cfg_ 
| listing_cfg_ 
| pair_code_ 
| xchg_pair_code_ 
| price_code_ 
| xchg_price_code_ 
| ext_wallet_code_ 
| flex_wallet_code_ 
| wrapper_code_ 
| deals_limit_ 
| wrapper_listing_requests_
| trading_pair_listing_requests_
| xchg_pair_listing_requests_ .


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.



(* 2 *) Definition ListingConfigL : list Type := 
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
 Opaque ListingConfigLRecord . 

(* 2 *) Definition WrapperListingRequestL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( Tip3ConfigLRecord ) : Type ] .
 Opaque Tip3ConfigLRecord.
Elpi GeneratePruvendoRecord WrapperListingRequestL WrapperListingRequestFields . 
 Opaque WrapperListingRequestLRecord . 

(* 2 *) Definition WrapperListingRequestWithPubkeyL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( WrapperListingRequestLRecord ) : Type ] .
Elpi GeneratePruvendoRecord WrapperListingRequestWithPubkeyL WrapperListingRequestWithPubkeyFields . 
 Opaque WrapperListingRequestWithPubkeyLRecord . 

(* 2 *) Definition TradingPairListingRequestL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord TradingPairListingRequestL TradingPairListingRequestFields . 
 Opaque TradingPairListingRequestLRecord . 

(* 2 *) Definition TradingPairListingRequestWithPubkeyL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( TradingPairListingRequestLRecord ) : Type ] .
Elpi GeneratePruvendoRecord TradingPairListingRequestWithPubkeyL TradingPairListingRequestWithPubkeyFields . 
 Opaque TradingPairListingRequestWithPubkeyLRecord . 

(* 2 *) Definition XchgPairListingRequestL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord XchgPairListingRequestL XchgPairListingRequestFields . 
 Opaque XchgPairListingRequestLRecord . 

(* 2 *) Definition XchgPairListingRequestWithPubkeyL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( XchgPairListingRequestLRecord ) : Type ] .
Elpi GeneratePruvendoRecord XchgPairListingRequestWithPubkeyL XchgPairListingRequestWithPubkeyFields . 
 Opaque XchgPairListingRequestWithPubkeyLRecord . 

(* 2 *) Definition FlexOwnershipInfoL : list Type := 
 [ ( XUInteger256 ) : Type ; 
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
 ( XUInteger8 ) : Type ; 
 ( FlexOwnershipInfoLRecord ) : Type ; 
 ( ( XHMap XUInteger WrapperListingRequestWithPubkeyLRecord ) ) : Type ; 
 ( ( XHMap XUInteger TradingPairListingRequestWithPubkeyLRecord ) ) : Type ; 
 ( ( XHMap XUInteger XchgPairListingRequestWithPubkeyLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord FlexDetailsL FlexDetailsFields . 
 Opaque FlexDetailsLRecord . 

(* 2 *) Definition DFlexL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XString ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( ListingConfigLRecord ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
  ( XUInteger8 ) : Type ;
 ( (XHMap XUInteger256 (XUInteger256 * WrapperListingRequestLRecord)) ) : Type ; 
 ( (XHMap XUInteger256 (XUInteger256 * TradingPairListingRequestLRecord)) ) : Type ; 
 ( (XHMap XUInteger256 (XUInteger256 * XchgPairListingRequestLRecord)) ) : Type ] .

Elpi GeneratePruvendoRecord DFlexL DFlexFields . 
 Opaque DFlexLRecord .

End ClassTypes .
 