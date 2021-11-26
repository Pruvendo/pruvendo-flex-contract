Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := Contracts.Flex.ClassTypes.ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition ListingConfig_ι_register_wrapper_cost_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_register_wrapper_cost} || : _.
    
Definition ListingConfig_ι_register_wrapper_cost_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_register_wrapper_cost} }} : _.
    
Notation " a '↑' 'ListingConfig.register_wrapper_cost' " := ( ListingConfig_ι_register_wrapper_cost_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.register_wrapper_cost' " := ( ListingConfig_ι_register_wrapper_cost_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_reject_wrapper_cost_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_reject_wrapper_cost} || : _.
    
Definition ListingConfig_ι_reject_wrapper_cost_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_reject_wrapper_cost} }} : _.
    
Notation " a '↑' 'ListingConfig.reject_wrapper_cost' " := ( ListingConfig_ι_reject_wrapper_cost_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.reject_wrapper_cost' " := ( ListingConfig_ι_reject_wrapper_cost_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_wrapper_deploy_value_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_wrapper_deploy_value} || : _.
    
Definition ListingConfig_ι_wrapper_deploy_value_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_wrapper_deploy_value} }} : _.
    
Notation " a '↑' 'ListingConfig.wrapper_deploy_value' " := ( ListingConfig_ι_wrapper_deploy_value_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.wrapper_deploy_value' " := ( ListingConfig_ι_wrapper_deploy_value_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_wrapper_keep_balance_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_wrapper_keep_balance} || : _.
    
Definition ListingConfig_ι_wrapper_keep_balance_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_wrapper_keep_balance} }} : _.
    
Notation " a '↑' 'ListingConfig.wrapper_keep_balance' " := ( ListingConfig_ι_wrapper_keep_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.wrapper_keep_balance' " := ( ListingConfig_ι_wrapper_keep_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_ext_wallet_balance_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_ext_wallet_balance} || : _.
    
Definition ListingConfig_ι_ext_wallet_balance_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_ext_wallet_balance} }} : _.
    
Notation " a '↑' 'ListingConfig.ext_wallet_balance' " := ( ListingConfig_ι_ext_wallet_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.ext_wallet_balance' " := ( ListingConfig_ι_ext_wallet_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_set_internal_wallet_value_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_set_internal_wallet_value} || : _.
    
Definition ListingConfig_ι_set_internal_wallet_value_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_set_internal_wallet_value} }} : _.
    
Notation " a '↑' 'ListingConfig.set_internal_wallet_value' " := ( ListingConfig_ι_set_internal_wallet_value_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.set_internal_wallet_value' " := ( ListingConfig_ι_set_internal_wallet_value_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_register_pair_cost_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_register_pair_cost} || : _.
    
Definition ListingConfig_ι_register_pair_cost_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_register_pair_cost} }} : _.
    
Notation " a '↑' 'ListingConfig.register_pair_cost' " := ( ListingConfig_ι_register_pair_cost_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.register_pair_cost' " := ( ListingConfig_ι_register_pair_cost_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_reject_pair_cost_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_reject_pair_cost} || : _.
    
Definition ListingConfig_ι_reject_pair_cost_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_reject_pair_cost} }} : _.
    
Notation " a '↑' 'ListingConfig.reject_pair_cost' " := ( ListingConfig_ι_reject_pair_cost_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.reject_pair_cost' " := ( ListingConfig_ι_reject_pair_cost_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_pair_deploy_value_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_pair_deploy_value} || : _.
    
Definition ListingConfig_ι_pair_deploy_value_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_pair_deploy_value} }} : _.
    
Notation " a '↑' 'ListingConfig.pair_deploy_value' " := ( ListingConfig_ι_pair_deploy_value_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.pair_deploy_value' " := ( ListingConfig_ι_pair_deploy_value_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_pair_keep_balance_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_pair_keep_balance} || : _.
    
Definition ListingConfig_ι_pair_keep_balance_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_pair_keep_balance} }} : _.
    
Notation " a '↑' 'ListingConfig_ι_pair_keep_balance' " := ( ListingConfig_ι_pair_keep_balance_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig_ι_pair_keep_balance' " := ( ListingConfig_ι_pair_keep_balance_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_register_return_value_right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_register_return_value} || : _.
    
Definition ListingConfig_ι_register_return_value_left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_register_return_value} }} : _.
    
Notation " a '↑' 'ListingConfig_ι_register_return_value' " := ( ListingConfig_ι_register_return_value_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig_ι_register_return_value' " := ( ListingConfig_ι_register_return_value_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequest_ι_client_addr_right {b} (x: URValue WrapperListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {WrapperListingRequest_ι_client_addr} || : _.
    
Definition WrapperListingRequest_ι_client_addr_left (x: ULValue WrapperListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {WrapperListingRequest_ι_client_addr} }} : _.
    
Notation " a '↑' 'WrapperListingRequest.client_addr' " := ( WrapperListingRequest_ι_client_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequest.client_addr' " := ( WrapperListingRequest_ι_client_addr_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequest_ι_client_funds_right {b} (x: URValue WrapperListingRequestLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {WrapperListingRequest_ι_client_funds} || : _.
    
Definition WrapperListingRequest_ι_client_funds_left (x: ULValue WrapperListingRequestLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {WrapperListingRequest_ι_client_funds} }} : _.
    
Notation " a '↑' 'WrapperListingRequest.client_funds' " := ( WrapperListingRequest_ι_client_funds_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequest.client_funds' " := ( WrapperListingRequest_ι_client_funds_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequest_ι_tip3cfg_right {b} (x: URValue WrapperListingRequestLRecord b): URValue Tip3ConfigLRecord b :=
    || {x} ^^ {WrapperListingRequest_ι_tip3cfg} || : _.
    
Definition WrapperListingRequest_ι_tip3cfg_left (x: ULValue WrapperListingRequestLRecord): ULValue Tip3ConfigLRecord :=
    {{ {x} ^^ {WrapperListingRequest_ι_tip3cfg} }} : _.
    
Notation " a '↑' 'WrapperListingRequest.tip3cfg' " := ( WrapperListingRequest_ι_tip3cfg_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequest.tip3cfg' " := ( WrapperListingRequest_ι_tip3cfg_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequestWithPubkey_ι_wrapper_pubkey_right {b} (x: URValue WrapperListingRequestWithPubkeyLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {WrapperListingRequestWithPubkey_ι_wrapper_pubkey} || : _.
    
Definition WrapperListingRequestWithPubkey_ι_wrapper_pubkey_left (x: ULValue WrapperListingRequestWithPubkeyLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {WrapperListingRequestWithPubkey_ι_wrapper_pubkey} }} : _.
    
Notation " a '↑' 'WrapperListingRequestWithPubkey.wrapper_pubkey' " := ( WrapperListingRequestWithPubkey_ι_wrapper_pubkey_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequestWithPubkey.wrapper_pubkey' " := ( WrapperListingRequestWithPubkey_ι_wrapper_pubkey_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequestWithPubkey_ι_request_right {b} (x: URValue WrapperListingRequestWithPubkeyLRecord b): URValue WrapperListingRequestLRecord b :=
    || {x} ^^ {WrapperListingRequestWithPubkey_ι_request} || : _.
    
Definition WrapperListingRequestWithPubkey_ι_request_left (x: ULValue WrapperListingRequestWithPubkeyLRecord): ULValue WrapperListingRequestLRecord :=
    {{ {x} ^^ {WrapperListingRequestWithPubkey_ι_request} }} : _.
    
Notation " a '↑' 'WrapperListingRequestWithPubkey.request' " := ( WrapperListingRequestWithPubkey_ι_request_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequestWithPubkey.request' " := ( WrapperListingRequestWithPubkey_ι_request_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_client_addr_right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {TradingPairListingRequest_ι_client_addr} || : _.
    
Definition TradingPairListingRequest_ι_client_addr_left (x: ULValue TradingPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {TradingPairListingRequest_ι_client_addr} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.client_addr' " := ( TradingPairListingRequest_ι_client_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.client_addr' " := ( TradingPairListingRequest_ι_client_addr_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_client_funds_right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TradingPairListingRequest_ι_client_funds} || : _.
    
Definition TradingPairListingRequest_ι_client_funds_left (x: ULValue TradingPairListingRequestLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TradingPairListingRequest_ι_client_funds} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.client_funds' " := ( TradingPairListingRequest_ι_client_funds_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.client_funds' " := ( TradingPairListingRequest_ι_client_funds_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_tip3_root_right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {TradingPairListingRequest_ι_tip3_root} || : _.
    
Definition TradingPairListingRequest_ι_tip3_root_left (x: ULValue TradingPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {TradingPairListingRequest_ι_tip3_root} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.tip3_root' " := ( TradingPairListingRequest_ι_tip3_root_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.tip3_root' " := ( TradingPairListingRequest_ι_tip3_root_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_min_amount_right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TradingPairListingRequest_ι_min_amount} || : _.
    
Definition TradingPairListingRequest_ι_min_amount_left (x: ULValue TradingPairListingRequestLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TradingPairListingRequest_ι_min_amount} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.min_amount' " := ( TradingPairListingRequest_ι_min_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.min_amount' " := ( TradingPairListingRequest_ι_min_amount_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_notify_addr_right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {TradingPairListingRequest_ι_notify_addr} || : _.
    
Definition TradingPairListingRequest_ι_notify_addr_left (x: ULValue TradingPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {TradingPairListingRequest_ι_notify_addr} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.notify_addr' " := ( TradingPairListingRequest_ι_notify_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.notify_addr' " := ( TradingPairListingRequest_ι_notify_addr_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequestWithPubkey_ι_wrapper_pubkey_right {b} (x: URValue TradingPairListingRequestWithPubkeyLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {TradingPairListingRequestWithPubkey_ι_wrapper_pubkey} || : _.
    
Definition TradingPairListingRequestWithPubkey_ι_wrapper_pubkey_left (x: ULValue TradingPairListingRequestWithPubkeyLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {TradingPairListingRequestWithPubkey_ι_wrapper_pubkey} }} : _.
    
Notation " a '↑' 'TradingPairListingRequestWithPubkey.wrapper_pubkey' " := ( TradingPairListingRequestWithPubkey_ι_wrapper_pubkey_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequestWithPubkey.wrapper_pubkey' " := ( TradingPairListingRequestWithPubkey_ι_wrapper_pubkey_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequestWithPubkey_ι_request_right {b} (x: URValue TradingPairListingRequestWithPubkeyLRecord b): URValue TradingPairListingRequestLRecord b :=
    || {x} ^^ {DXchgPair_ι_flex_addr_} || : _.
    
Definition TradingPairListingRequestWithPubkey_ι_request_left (x: ULValue TradingPairListingRequestWithPubkeyLRecord): ULValue TradingPairListingRequestLRecord :=
    {{ {x} ^^ {DXchgPair_ι_flex_addr_} }} : _.
    
Notation " a '↑' 'TradingPairListingRequestWithPubkey.request' " := ( TradingPairListingRequestWithPubkey_ι_request_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequestWithPubkey.request' " := ( TradingPairListingRequestWithPubkey_ι_request_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition XchgPairListingRequest_ι_client_addr_right {b} (x: URValue XchgPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {XchgPairListingRequest_ι_client_addr} || : _.
    
Definition XchgPairListingRequest_ι_client_addr_left (x: ULValue XchgPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {XchgPairListingRequest_ι_client_addr} }} : _.
    
Notation " a '↑' 'XchgPairListingRequest.client_addr' " := ( XchgPairListingRequest_ι_client_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'XchgPairListingRequest.client_addr' " := ( XchgPairListingRequest_ι_client_addr_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition XchgPairListingRequest_ι_client_funds_right {b} (x: URValue XchgPairListingRequestLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {XchgPairListingRequest_ι_client_funds} || : _.
    
Definition XchgPairListingRequest_ι_client_funds_left (x: ULValue XchgPairListingRequestLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {XchgPairListingRequest_ι_client_funds} }} : _.
    
Notation " a '↑' 'XchgPairListingRequest.client_funds' " := ( XchgPairListingRequest_ι_client_funds_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'XchgPairListingRequest.client_funds' " := ( XchgPairListingRequest_ι_client_funds_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition XchgPairListingRequest_ι_tip3_major_root_right {b} (x: URValue XchgPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {XchgPairListingRequest_ι_tip3_major_root} || : _.
    
Definition XchgPairListingRequest_ι_tip3_major_root_left (x: ULValue XchgPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {XchgPairListingRequest_ι_tip3_major_root} }} : _.
    
Notation " a '↑' 'XchgPairListingRequest.tip3_major_root' " := ( XchgPairListingRequest_ι_tip3_major_root_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'XchgPairListingRequest.tip3_major_root' " := ( XchgPairListingRequest_ι_tip3_major_root_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition XchgPairListingRequest_ι_tip3_minor_root_right {b} (x: URValue XchgPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {XchgPairListingRequest_ι_tip3_minor_root} || : _.
    
Definition XchgPairListingRequest_ι_tip3_minor_root_left (x: ULValue XchgPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {XchgPairListingRequest_ι_tip3_minor_root} }} : _.
    
Notation " a '↑' 'XchgPairListingRequest.tip3_minor_root' " := ( XchgPairListingRequest_ι_tip3_minor_root_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'XchgPairListingRequest.tip3_minor_root' " := ( XchgPairListingRequest_ι_tip3_minor_root_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition XchgPairListingRequest_ι_min_amount_right {b} (x: URValue XchgPairListingRequestLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {XchgPairListingRequest_ι_min_amount} || : _.
    
Definition XchgPairListingRequest_ι_min_amount_left (x: ULValue XchgPairListingRequestLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {XchgPairListingRequest_ι_min_amount} }} : _.
    
Notation " a '↑' 'XchgPairListingRequest.min_amount' " := ( XchgPairListingRequest_ι_min_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'XchgPairListingRequest.min_amount' " := ( XchgPairListingRequest_ι_min_amount_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition XchgPairListingRequest_ι_notify_addr_right {b} (x: URValue XchgPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {XchgPairListingRequest_ι_notify_addr} || : _.
    
Definition XchgPairListingRequest_ι_notify_addr_left (x: ULValue XchgPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {XchgPairListingRequest_ι_notify_addr} }} : _.
    
Notation " a '↑' 'XchgPairListingRequest.notify_addr' " := ( XchgPairListingRequest_ι_notify_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'XchgPairListingRequest.notify_addr' " := ( XchgPairListingRequest_ι_notify_addr_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition XchgPairListingRequestWithPubkey_ι_request_pubkey_right {b} (x: URValue XchgPairListingRequestWithPubkeyLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {XchgPairListingRequestWithPubkey_ι_request_pubkey} || : _.
    
Definition XchgPairListingRequestWithPubkey_ι_request_pubkey_left (x: ULValue XchgPairListingRequestWithPubkeyLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {XchgPairListingRequestWithPubkey_ι_request_pubkey} }} : _.
    
Notation " a '↑' 'XchgPairListingRequestWithPubkey.request_pubkey' " := ( XchgPairListingRequestWithPubkey_ι_request_pubkey_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'XchgPairListingRequestWithPubkey.request_pubkey' " := ( XchgPairListingRequestWithPubkey_ι_request_pubkey_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition XchgPairListingRequestWithPubkey_ι_request_right {b} (x: URValue XchgPairListingRequestWithPubkeyLRecord b): URValue XchgPairListingRequestLRecord b :=
    || {x} ^^ {XchgPairListingRequestWithPubkey_ι_request} || : _.
    
Definition XchgPairListingRequestWithPubkey_ι_request_left (x: ULValue XchgPairListingRequestWithPubkeyLRecord): ULValue XchgPairListingRequestLRecord :=
    {{ {x} ^^ {XchgPairListingRequestWithPubkey_ι_request} }} : _.
    
Notation " a '↑' 'XchgPairListingRequestWithPubkey.request' " := ( XchgPairListingRequestWithPubkey_ι_request_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'XchgPairListingRequestWithPubkey.request' " := ( XchgPairListingRequestWithPubkey_ι_request_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexOwnershipInfo_ι_deployer_pubkey_right {b} (x: URValue FlexOwnershipInfoLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {FlexOwnershipInfo_ι_deployer_pubkey} || : _.
    
Definition FlexOwnershipInfo_ι_deployer_pubkey_left (x: ULValue FlexOwnershipInfoLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {FlexOwnershipInfo_ι_deployer_pubkey} }} : _.
    
Notation " a '↑' 'FlexOwnershipInfo.deployer_pubkey' " := ( FlexOwnershipInfo_ι_deployer_pubkey_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexOwnershipInfo.deployer_pubkey' " := ( FlexOwnershipInfo_ι_deployer_pubkey_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexOwnershipInfo_ι_ownership_description_right {b} (x: URValue FlexOwnershipInfoLRecord b): URValue XString b :=
    || {x} ^^ {FlexOwnershipInfo_ι_ownership_description} || : _.
    
Definition FlexOwnershipInfo_ι_ownership_description_left (x: ULValue FlexOwnershipInfoLRecord): ULValue XString :=
    {{ {x} ^^ {FlexOwnershipInfo_ι_ownership_description} }} : _.
    
Notation " a '↑' 'FlexOwnershipInfo.ownership_description' " := ( FlexOwnershipInfo_ι_ownership_description_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'xxFlexOwnershipInfo.ownership_descriptionx' " := ( FlexOwnershipInfo_ι_ownership_description_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexOwnershipInfo_ι_owner_contract_right {b} (x: URValue FlexOwnershipInfoLRecord b): URValue ( XMaybe XAddress ) b :=
    || {x} ^^ {FlexOwnershipInfo_ι_owner_contract} || : _.
    
Definition FlexOwnershipInfo_ι_owner_contract_left (x: ULValue FlexOwnershipInfoLRecord): ULValue ( XMaybe XAddress ) :=
    {{ {x} ^^ {FlexOwnershipInfo_ι_owner_contract} }} : _.
    
Notation " a '↑' 'FlexOwnershipInfo.owner_contract' " := ( FlexOwnershipInfo_ι_owner_contract_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexOwnershipInfo.owner_contract' " := ( FlexOwnershipInfo_ι_owner_contract_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_initialized_right {b} (x: URValue FlexDetailsLRecord b): URValue XBool b :=
    || {x} ^^ {FlexDetails_ι_initialized} || : _.
    
Definition FlexDetails_ι_initialized_left (x: ULValue FlexDetailsLRecord): ULValue XBool :=
    {{ {x} ^^ {FlexDetails_ι_initialized} }} : _.
    
Notation " a '↑' 'FlexDetails.initialized' " := ( FlexDetails_ι_initialized_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDetails.initialized' " := ( FlexDetails_ι_initialized_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_tons_cfg_right {b} (x: URValue FlexDetailsLRecord b): URValue TonsConfigLRecord b :=
    || {x} ^^ {FlexDetails_ι_tons_cfg} || : _.
    
Definition FlexDetails_ι_tons_cfg_left (x: ULValue FlexDetailsLRecord): ULValue TonsConfigLRecord :=
    {{ {x} ^^ {FlexDetails_ι_tons_cfg} }} : _.
    
Notation " a '↑' 'FlexDetails.tons_cfg' " := ( FlexDetails_ι_tons_cfg_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDetails.tons_cfg' " := ( FlexDetails_ι_tons_cfg_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_listing_cfg_right {b} (x: URValue FlexDetailsLRecord b): URValue ListingConfigLRecord b :=
    || {x} ^^ {FlexDetails_ι_listing_cfg} || : _.
    
Definition FlexDetails_ι_listing_cfg_left (x: ULValue FlexDetailsLRecord): ULValue ListingConfigLRecord :=
    {{ {x} ^^ {FlexDetails_ι_listing_cfg} }} : _.
    
Notation " a '↑' 'FlexDetails_ι_listing_cfg' " := ( FlexDetails_ι_listing_cfg_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDetails_ι_listing_cfg' " := ( FlexDetails_ι_listing_cfg_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_trading_pair_code_right {b} (x: URValue FlexDetailsLRecord b): URValue XCell b :=
    || {x} ^^ {FlexDetails_ι_trading_pair_code} || : _.
    
Definition FlexDetails_ι_trading_pair_code_left (x: ULValue FlexDetailsLRecord): ULValue XCell :=
    {{ {x} ^^ {FlexDetails_ι_trading_pair_code} }} : _.
    
Notation " a '↑' 'FlexDetails.trading_pair_code' " := ( FlexDetails_ι_trading_pair_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDetails.trading_pair_code' " := ( FlexDetails_ι_trading_pair_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_xchg_pair_code_right {b} (x: URValue FlexDetailsLRecord b): URValue XCell b :=
    || {x} ^^ {FlexDetails_ι_xchg_pair_code} || : _.
    
Definition FlexDetails_ι_xchg_pair_code_left (x: ULValue FlexDetailsLRecord): ULValue XCell :=
    {{ {x} ^^ {FlexDetails_ι_xchg_pair_code} }} : _.
    
Notation " a '↑' 'FlexDetails.xchg_pair_code' " := ( FlexDetails_ι_xchg_pair_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDetails.xchg_pair_code' " := ( FlexDetails_ι_xchg_pair_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_deals_limit_right {b} (x: URValue FlexDetailsLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {FlexDetails_ι_deals_limit} || : _.
    
Definition FlexDetails_ι_deals_limit_left (x: ULValue FlexDetailsLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {FlexDetails_ι_deals_limit} }} : _.
    
Notation " a '↑' 'FlexDetails.deals_limit' " := ( FlexDetails_ι_deals_limit_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDetails.deals_limit' " := ( FlexDetails_ι_deals_limit_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_ownership_right {b} (x: URValue FlexDetailsLRecord b): URValue FlexOwnershipInfoLRecord b :=
    || {x} ^^ {FlexDetails_ι_ownership} || : _.
    
Definition FlexDetails_ι_ownership_left (x: ULValue FlexDetailsLRecord): ULValue FlexOwnershipInfoLRecord :=
    {{ {x} ^^ {FlexDetails_ι_ownership} }} : _.
    
Notation " a '↑' 'FlexDetails.ownership' " := ( FlexDetails_ι_ownership_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'xxFlexDetails.ownershipx' " := ( FlexDetails_ι_ownership_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_wrapper_listing_requests_right {b} (x: URValue FlexDetailsLRecord b): URValue ( XHMap XUInteger WrapperListingRequestWithPubkeyLRecord ) b :=
    || {x} ^^ {FlexDetails_ι_wrapper_listing_requests} || : _.
    
Definition FlexDetails_ι_wrapper_listing_requests_left (x: ULValue FlexDetailsLRecord): ULValue ( XHMap XUInteger WrapperListingRequestWithPubkeyLRecord ) :=
    {{ {x} ^^ {FlexDetails_ι_wrapper_listing_requests} }} : _.
    
Notation " a '↑' 'FlexDetails.wrapper_listing_requests' " := ( FlexDetails_ι_wrapper_listing_requests_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDetails.wrapper_listing_requests' " := ( FlexDetails_ι_wrapper_listing_requests_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_trading_pair_listing_requests_right {b} (x: URValue FlexDetailsLRecord b): URValue ( XHMap XUInteger TradingPairListingRequestWithPubkeyLRecord ) b :=
    || {x} ^^ {FlexDetails_ι_trading_pair_listing_requests} || : _.
    
Definition FlexDetails_ι_trading_pair_listing_requests_left (x: ULValue FlexDetailsLRecord): ULValue ( XHMap XUInteger TradingPairListingRequestWithPubkeyLRecord ) :=
    {{ {x} ^^ {FlexDetails_ι_trading_pair_listing_requests} }} : _.
    
Notation " a '↑' 'FlexDetails.trading_pair_listing_requests' " := ( FlexDetails_ι_trading_pair_listing_requests_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDetails.trading_pair_listing_requests' " := ( FlexDetails_ι_trading_pair_listing_requests_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDetails_ι_xchg_pair_listing_requests_right {b} (x: URValue FlexDetailsLRecord b): URValue ( XHMap XUInteger XchgPairListingRequestWithPubkeyLRecord ) b :=
    || {x} ^^ {FlexDetails_ι_xchg_pair_listing_requests} || : _.
    
Definition FlexDetails_ι_xchg_pair_listing_requests_left (x: ULValue FlexDetailsLRecord): ULValue ( XHMap XUInteger XchgPairListingRequestWithPubkeyLRecord ) :=
    {{ {x} ^^ {FlexDetails_ι_xchg_pair_listing_requests} }} : _.
    
Notation " a '↑' 'FlexDetails.xchg_pair_listing_requests' " := ( FlexDetails_ι_xchg_pair_listing_requests_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDetails.xchg_pair_listing_requests' " := ( FlexDetails_ι_xchg_pair_listing_requests_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_deployer_pubkey__right {b} (x: URValue DFlexLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DFlex_ι_deployer_pubkey_} || : _.
    
Definition DFlex_ι_deployer_pubkey__left (x: ULValue DFlexLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DFlex_ι_deployer_pubkey_} }} : _.
    
Notation " a '↑' 'DFlex.deployer_pubkey_' " := ( DFlex_ι_deployer_pubkey__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.deployer_pubkey_' " := ( DFlex_ι_deployer_pubkey__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_workchain_id__right {b} (x: URValue DFlexLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DFlex_ι_workchain_id_} || : _.
    
Definition DFlex_ι_workchain_id__left (x: ULValue DFlexLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DFlex_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DFlex.workchain_id_' " := ( DFlex_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.workchain_id_' " := ( DFlex_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_ownership_description__right {b} (x: URValue DFlexLRecord b): URValue XString b :=
    || {x} ^^ {DFlex_ι_ownership_description_} || : _.
    
Definition DFlex_ι_ownership_description__left (x: ULValue DFlexLRecord): ULValue XString :=
    {{ {x} ^^ {DFlex_ι_ownership_description_} }} : _.
    
Notation " a '↑' 'DFlex.ownership_description_' " := ( DFlex_ι_ownership_description__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex_.ownership_description_' " := ( DFlex_ι_ownership_description__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_owner_address__right {b} (x: URValue DFlexLRecord b): URValue ( XMaybe XAddress ) b :=
    || {x} ^^ {DFlex_ι_owner_address_} || : _.
    
Definition DFlex_ι_owner_address__left (x: ULValue DFlexLRecord): ULValue ( XMaybe XAddress ) :=
    {{ {x} ^^ {DFlex_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DFlex.owner_address_' " := ( DFlex_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.owner_address_' " := ( DFlex_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_tons_cfg__right {b} (x: URValue DFlexLRecord b): URValue TonsConfigLRecord b :=
    || {x} ^^ {DFlex_ι_tons_cfg_} || : _.
    
Definition DFlex_ι_tons_cfg__left (x: ULValue DFlexLRecord): ULValue TonsConfigLRecord :=
    {{ {x} ^^ {DFlex_ι_tons_cfg_} }} : _.
    
Notation " a '↑' 'DFlex.tons_cfg_' " := ( DFlex_ι_tons_cfg__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.tons_cfg_' " := ( DFlex_ι_tons_cfg__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_listing_cfg__right {b} (x: URValue DFlexLRecord b): URValue ListingConfigLRecord b :=
    || {x} ^^ {DFlex_ι_listing_cfg_} || : _.
    
Definition DFlex_ι_listing_cfg__left (x: ULValue DFlexLRecord): ULValue ListingConfigLRecord :=
    {{ {x} ^^ {DFlex_ι_listing_cfg_} }} : _.
    
Notation " a '↑' 'DFlex.listing_cfg_' " := ( DFlex_ι_listing_cfg__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.listing_cfg_' " := ( DFlex_ι_listing_cfg__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_pair_code__right {b} (x: URValue DFlexLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlex_ι_pair_code_} || : _.
    
Definition DFlex_ι_pair_code__left (x: ULValue DFlexLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlex_ι_pair_code_} }} : _.
    
Notation " a '↑' 'DFlex.pair_code_' " := ( DFlex_ι_pair_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.pair_code_' " := ( DFlex_ι_pair_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_xchg_pair_code__right {b} (x: URValue DFlexLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlex_ι_xchg_pair_code_} || : _.
    
Definition DFlex_ι_xchg_pair_code__left (x: ULValue DFlexLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlex_ι_xchg_pair_code_} }} : _.
    
Notation " a '↑' 'DFlex.xchg_pair_code_' " := ( DFlex_ι_xchg_pair_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.xchg_pair_code_' " := ( DFlex_ι_xchg_pair_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_price_code__right {b} (x: URValue DFlexLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlex_ι_price_code_} || : _.
    
Definition DFlex_ι_price_code__left (x: ULValue DFlexLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlex_ι_price_code_} }} : _.
    
Notation " a '↑' 'DFlex.price_code_' " := ( DFlex_ι_price_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.price_code_' " := ( DFlex_ι_price_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_xchg_price_code__right {b} (x: URValue DFlexLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlex_ι_xchg_price_code_} || : _.
    
Definition DFlex_ι_xchg_price_code__left (x: ULValue DFlexLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlex_ι_xchg_price_code_} }} : _.
    
Notation " a '↑' 'DFlex.xchg_price_code_' " := ( DFlex_ι_xchg_price_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.xchg_price_code_' " := ( DFlex_ι_xchg_price_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_ext_wallet_code__right {b} (x: URValue DFlexLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlex_ι_ext_wallet_code_} || : _.
    
Definition DFlex_ι_ext_wallet_code__left (x: ULValue DFlexLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlex_ι_ext_wallet_code_} }} : _.
    
Notation " a '↑' 'DFlex.ext_wallet_code_' " := ( DFlex_ι_ext_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.ext_wallet_code_' " := ( DFlex_ι_ext_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_flex_wallet_code__right {b} (x: URValue DFlexLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlex_ι_flex_wallet_code_} || : _.
    
Definition DFlex_ι_flex_wallet_code__left (x: ULValue DFlexLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlex_ι_flex_wallet_code_} }} : _.
    
Notation " a '↑' 'DFlex.flex_wallet_code_' " := ( DFlex_ι_flex_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.flex_wallet_code_' " := ( DFlex_ι_flex_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_wrapper_code__right {b} (x: URValue DFlexLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlex_ι_wrapper_code_} || : _.
    
Definition DFlex_ι_wrapper_code__left (x: ULValue DFlexLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlex_ι_wrapper_code_} }} : _.
    
Notation " a '↑' 'DFlex.wrapper_code_' " := ( DFlex_ι_wrapper_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.wrapper_code_' " := ( DFlex_ι_wrapper_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_deals_limit__right {b} (x: URValue DFlexLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DFlex_ι_deals_limit_} || : _.
    
Definition DFlex_ι_deals_limit__left (x: ULValue DFlexLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DFlex_ι_deals_limit_} }} : _.
    
Notation " a '↑' 'DFlex.deals_limit_' " := ( DFlex_ι_deals_limit__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.deals_limit_' " := ( DFlex_ι_deals_limit__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_wrapper_listing_requests__right {b} (x: URValue DFlexLRecord b): URValue (XHMap XUInteger256 (XUInteger256 * WrapperListingRequestLRecord)) b :=
    || {x} ^^ {DFlex_ι_wrapper_listing_requests_} || : _.
    
Definition DFlex_ι_wrapper_listing_requests__left (x: ULValue DFlexLRecord): ULValue (XHMap XUInteger256 (XUInteger256 * WrapperListingRequestLRecord)) :=
    {{ {x} ^^ {DFlex_ι_wrapper_listing_requests_} }} : _.
    
Notation " a '↑' 'DFlex.wrapper_listing_requests_' " := ( DFlex_ι_wrapper_listing_requests__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.wrapper_listing_requests_' " := ( DFlex_ι_wrapper_listing_requests__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_trading_pair_listing_requests__right {b} (x: URValue DFlexLRecord b): URValue (XHMap XUInteger256 (XUInteger256 * TradingPairListingRequestLRecord)) b :=
    || {x} ^^ {DFlex_ι_trading_pair_listing_requests_} || : _.
    
Definition DFlex_ι_trading_pair_listing_requests__left (x: ULValue DFlexLRecord): ULValue (XHMap XUInteger256 (XUInteger256 * TradingPairListingRequestLRecord)) :=
    {{ {x} ^^ {DFlex_ι_trading_pair_listing_requests_} }} : _.
    
Notation " a '↑' 'DFlex.trading_pair_listing_requests_' " := ( DFlex_ι_trading_pair_listing_requests__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.trading_pair_listing_requests_' " := ( DFlex_ι_trading_pair_listing_requests__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlex_ι_xchg_pair_listing_requests__right {b} (x: URValue DFlexLRecord b): URValue (XHMap XUInteger256 (XUInteger256 * XchgPairListingRequestLRecord)) b :=
    || {x} ^^ {DFlex_ι_xchg_pair_listing_requests_} || : _.
    
Definition DFlex_ι_xchg_pair_listing_requests__left (x: ULValue DFlexLRecord): ULValue (XHMap XUInteger256 (XUInteger256 * XchgPairListingRequestLRecord)) :=
    {{ {x} ^^ {DFlex_ι_xchg_pair_listing_requests_} }} : _.
    
Notation " a '↑' 'DFlex.xchg_pair_listing_requests_' " := ( DFlex_ι_xchg_pair_listing_requests__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlex.xchg_pair_listing_requests_' " := ( DFlex_ι_xchg_pair_listing_requests__left a ) (in custom ULValue at level 0) : ursus_scope.

End ClassTypesNotations.


