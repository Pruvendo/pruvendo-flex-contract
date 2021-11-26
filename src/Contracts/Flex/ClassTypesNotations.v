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

Definition ListingConfig_ι_register_wrapper_cost _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_register_wrapper_cost} || : _.
    
Definition ListingConfig_ι_register_wrapper_cost _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_register_wrapper_cost} }} : _.
    
Notation " a '↑' 'ListingConfig.register_wrapper_cost' " := ( ListingConfig_ι_register_wrapper_cost _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.register_wrapper_cost' " := ( ListingConfig_ι_register_wrapper_cost _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_reject_wrapper_cost _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_reject_wrapper_cost} || : _.
    
Definition ListingConfig_ι_reject_wrapper_cost _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_reject_wrapper_cost} }} : _.
    
Notation " a '↑' 'ListingConfig.reject_wrapper_cost' " := ( ListingConfig_ι_reject_wrapper_cost _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.reject_wrapper_cost' " := ( ListingConfig_ι_reject_wrapper_cost _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_wrapper_deploy_value _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_wrapper_deploy_value} || : _.
    
Definition ListingConfig_ι_wrapper_deploy_value _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_wrapper_deploy_value} }} : _.
    
Notation " a '↑' 'ListingConfig.wrapper_deploy_value' " := ( ListingConfig_ι_wrapper_deploy_value _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.wrapper_deploy_value' " := ( ListingConfig_ι_wrapper_deploy_value _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_wrapper_keep_balance _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_wrapper_keep_balance} || : _.
    
Definition ListingConfig_ι_wrapper_keep_balance _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_wrapper_keep_balance} }} : _.
    
Notation " a '↑' 'ListingConfig.wrapper_keep_balance' " := ( ListingConfig_ι_wrapper_keep_balance _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.wrapper_keep_balance' " := ( ListingConfig_ι_wrapper_keep_balance _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_ext_wallet_balance _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_ext_wallet_balance} || : _.
    
Definition ListingConfig_ι_ext_wallet_balance _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_ext_wallet_balance} }} : _.
    
Notation " a '↑' 'ListingConfig.ext_wallet_balance' " := ( ListingConfig_ι_ext_wallet_balance _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.ext_wallet_balance' " := ( ListingConfig_ι_ext_wallet_balance _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_set_internal_wallet_value _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_set_internal_wallet_value} || : _.
    
Definition ListingConfig_ι_set_internal_wallet_value _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_set_internal_wallet_value} }} : _.
    
Notation " a '↑' 'ListingConfig.set_internal_wallet_value' " := ( ListingConfig_ι_set_internal_wallet_value _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.set_internal_wallet_value' " := ( ListingConfig_ι_set_internal_wallet_value _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_register_pair_cost _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_register_pair_cost} || : _.
    
Definition ListingConfig_ι_register_pair_cost _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_register_pair_cost} }} : _.
    
Notation " a '↑' 'ListingConfig.register_pair_cost' " := ( ListingConfig_ι_register_pair_cost _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.register_pair_cost' " := ( ListingConfig_ι_register_pair_cost _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_reject_pair_cost _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_reject_pair_cost} || : _.
    
Definition ListingConfig_ι_reject_pair_cost _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_reject_pair_cost} }} : _.
    
Notation " a '↑' 'ListingConfig.reject_pair_cost' " := ( ListingConfig_ι_reject_pair_cost _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.reject_pair_cost' " := ( ListingConfig_ι_reject_pair_cost _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_pair_deploy_value _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_pair_deploy_value} || : _.
    
Definition ListingConfig_ι_pair_deploy_value _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_pair_deploy_value} }} : _.
    
Notation " a '↑' 'ListingConfig.pair_deploy_value' " := ( ListingConfig_ι_pair_deploy_value _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig.pair_deploy_value' " := ( ListingConfig_ι_pair_deploy_value _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_pair_keep_balance _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_pair_keep_balance} || : _.
    
Definition ListingConfig_ι_pair_keep_balance _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_pair_keep_balance} }} : _.
    
Notation " a '↑' 'ListingConfig_ι_pair_keep_balance' " := ( ListingConfig_ι_pair_keep_balance _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig_ι_pair_keep_balance' " := ( ListingConfig_ι_pair_keep_balance _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition ListingConfig_ι_register_return_value _right {b} (x: URValue ListingConfigLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {ListingConfig_ι_register_return_value} || : _.
    
Definition ListingConfig_ι_register_return_value _left (x: ULValue ListingConfigLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {ListingConfig_ι_register_return_value} }} : _.
    
Notation " a '↑' 'ListingConfig_ι_register_return_value' " := ( ListingConfig_ι_register_return_value _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'ListingConfig_ι_register_return_value' " := ( ListingConfig_ι_register_return_value _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequest_ι_client_addr _right {b} (x: URValue WrapperListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {WrapperListingRequest_ι_client_addr} || : _.
    
Definition WrapperListingRequest_ι_client_addr _left (x: ULValue WrapperListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {WrapperListingRequest_ι_client_addr} }} : _.
    
Notation " a '↑' 'WrapperListingRequest.client_addr' " := ( WrapperListingRequest_ι_client_addr _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequest.client_addr' " := ( WrapperListingRequest_ι_client_addr _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequest_ι_client_funds _right {b} (x: URValue WrapperListingRequestLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {WrapperListingRequest_ι_client_funds} || : _.
    
Definition WrapperListingRequest_ι_client_funds _left (x: ULValue WrapperListingRequestLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {WrapperListingRequest_ι_client_funds} }} : _.
    
Notation " a '↑' 'WrapperListingRequest.client_funds' " := ( WrapperListingRequest_ι_client_funds _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequest.client_funds' " := ( WrapperListingRequest_ι_client_funds _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequest_ι_tip3cfg _right {b} (x: URValue WrapperListingRequestLRecord b): URValue Tip3ConfigLRecord b :=
    || {x} ^^ {WrapperListingRequest_ι_tip3cfg} || : _.
    
Definition WrapperListingRequest_ι_tip3cfg _left (x: ULValue WrapperListingRequestLRecord): ULValue Tip3ConfigLRecord :=
    {{ {x} ^^ {WrapperListingRequest_ι_tip3cfg} }} : _.
    
Notation " a '↑' 'WrapperListingRequest.tip3cfg' " := ( WrapperListingRequest_ι_tip3cfg _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequest.tip3cfg' " := ( WrapperListingRequest_ι_tip3cfg _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequestWithPubkey_ι_wrapper_pubkey _right {b} (x: URValue WrapperListingRequestWithPubkeyLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {WrapperListingRequestWithPubkey_ι_wrapper_pubkey} || : _.
    
Definition WrapperListingRequestWithPubkey_ι_wrapper_pubkey _left (x: ULValue WrapperListingRequestWithPubkeyLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {WrapperListingRequestWithPubkey_ι_wrapper_pubkey} }} : _.
    
Notation " a '↑' 'WrapperListingRequestWithPubkey.wrapper_pubkey' " := ( WrapperListingRequestWithPubkey_ι_wrapper_pubkey _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequestWithPubkey.wrapper_pubkey' " := ( WrapperListingRequestWithPubkey_ι_wrapper_pubkey _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperListingRequestWithPubkey_ι_request _right {b} (x: URValue WrapperListingRequestWithPubkeyLRecord b): URValue WrapperListingRequestLRecord b :=
    || {x} ^^ {WrapperListingRequestWithPubkey_ι_request} || : _.
    
Definition WrapperListingRequestWithPubkey_ι_request _left (x: ULValue WrapperListingRequestWithPubkeyLRecord): ULValue WrapperListingRequestLRecord :=
    {{ {x} ^^ {WrapperListingRequestWithPubkey_ι_request} }} : _.
    
Notation " a '↑' 'WrapperListingRequestWithPubkey.request' " := ( WrapperListingRequestWithPubkey_ι_request _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperListingRequestWithPubkey.request' " := ( WrapperListingRequestWithPubkey_ι_request _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_client_addr _right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {TradingPairListingRequest_ι_client_addr} || : _.
    
Definition TradingPairListingRequest_ι_client_addr _left (x: ULValue TradingPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {TradingPairListingRequest_ι_client_addr} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.client_addr' " := ( TradingPairListingRequest_ι_client_addr _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.client_addr' " := ( TradingPairListingRequest_ι_client_addr _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_client_funds _right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TradingPairListingRequest_ι_client_funds} || : _.
    
Definition TradingPairListingRequest_ι_client_funds _left (x: ULValue TradingPairListingRequestLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TradingPairListingRequest_ι_client_funds} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.client_funds' " := ( TradingPairListingRequest_ι_client_funds _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.client_funds' " := ( TradingPairListingRequest_ι_client_funds _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_tip3_root _right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {TradingPairListingRequest_ι_tip3_root} || : _.
    
Definition TradingPairListingRequest_ι_tip3_root _left (x: ULValue TradingPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {TradingPairListingRequest_ι_tip3_root} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.tip3_root' " := ( TradingPairListingRequest_ι_tip3_root _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.tip3_root' " := ( TradingPairListingRequest_ι_tip3_root _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_min_amount _right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {TradingPairListingRequest_ι_min_amount} || : _.
    
Definition TradingPairListingRequest_ι_min_amount _left (x: ULValue TradingPairListingRequestLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {TradingPairListingRequest_ι_min_amount} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.min_amount' " := ( TradingPairListingRequest_ι_min_amount _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.min_amount' " := ( TradingPairListingRequest_ι_min_amount _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequest_ι_notify_addr _right {b} (x: URValue TradingPairListingRequestLRecord b): URValue XAddress b :=
    || {x} ^^ {TradingPairListingRequest_ι_notify_addr} || : _.
    
Definition TradingPairListingRequest_ι_notify_addr _left (x: ULValue TradingPairListingRequestLRecord): ULValue XAddress :=
    {{ {x} ^^ {TradingPairListingRequest_ι_notify_addr} }} : _.
    
Notation " a '↑' 'TradingPairListingRequest.notify_addr' " := ( TradingPairListingRequest_ι_notify_addr _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequest.notify_addr' " := ( TradingPairListingRequest_ι_notify_addr _left a ) (in custom ULValue at level 0) : ursus_scope.

Definition TradingPairListingRequestWithPubkey_ι_wrapper_pubkey _right {b} (x: URValue TradingPairListingRequestWithPubkeyLRecord b): URValue ttt b :=
    || {x} ^^ {TradingPairListingRequestWithPubkey_ι_wrapper_pubkey} || : _.
    
Definition TradingPairListingRequestWithPubkey_ι_wrapper_pubkey _left (x: ULValue TradingPairListingRequestWithPubkeyLRecord): ULValue ttt :=
    {{ {x} ^^ {TradingPairListingRequestWithPubkey_ι_wrapper_pubkey} }} : _.
    
Notation " a '↑' 'TradingPairListingRequestWithPubkey.wrapper_pubkey' " := ( TradingPairListingRequestWithPubkey_ι_wrapper_pubkey _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'TradingPairListingRequestWithPubkey.wrapper_pubkey' " := ( TradingPairListingRequestWithPubkey_ι_wrapper_pubkey _left a ) (in custom ULValue at level 0) : ursus_scope.












Definition DXchgPair_ι_flex_addr_ _right {b} (x: URValue TradingPairListingRequestWithPubkeyLRecord b): URValue ttt b :=
    || {x} ^^ {DXchgPair_ι_flex_addr_} || : _.
    
Definition DXchgPair_ι_flex_addr_ _left (x: ULValue TradingPairListingRequestWithPubkeyLRecord): ULValue ttt :=
    {{ {x} ^^ {DXchgPair_ι_flex_addr_} }} : _.
    
Notation " a '↑' 'xxx' " := ( DXchgPair_ι_flex_addr_ _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'xxx' " := ( DXchgPair_ι_flex_addr_ _left a ) (in custom ULValue at level 0) : ursus_scope.


End ClassTypesNotations.


