Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.

Require Import Wrapper.ClassTypes.
(* Require Import Wrapper.Ledger. *)
Require Import Wrapper.Interface.

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).

Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.
Module Export InterfaceModule := PublicInterface xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition WrapperRet_ι_err_code_right {b} (x: URValue WrapperRetLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {WrapperRet_ι_err_code} || : _ .
    
Definition WrapperRet_ι_err_code_left (x: ULValue WrapperRetLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {WrapperRet_ι_err_code} }} : _.
    
Notation " a '↑' 'WrapperRet.err_code' " := ( WrapperRet_ι_err_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperRet.err_code' " := ( WrapperRet_ι_err_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition WrapperRet_ι_flex_wallet_right {b} (x: URValue WrapperRetLRecord b): URValue address b :=
    || {x} ^^ {WrapperRet_ι_flex_wallet} || : _ .
    
Definition WrapperRet_ι_flex_wallet_left (x: ULValue WrapperRetLRecord): ULValue address :=
    {{ {x} ^^ {WrapperRet_ι_flex_wallet} }} : _.
    
Notation " a '↑' 'WrapperRet.flex_wallet' " := ( WrapperRet_ι_flex_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'WrapperRet.flex_wallet' " := ( WrapperRet_ι_flex_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDeployWalletArgs_ι_pubkey_right {b} (x: URValue FlexDeployWalletArgsLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {FlexDeployWalletArgs_ι_pubkey} || : _ .
    
Definition FlexDeployWalletArgs_ι_pubkey_left (x: ULValue FlexDeployWalletArgsLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {FlexDeployWalletArgs_ι_pubkey} }} : _.
    
Notation " a '↑' 'FlexDeployWalletArgs.pubkey' " := ( FlexDeployWalletArgs_ι_pubkey_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDeployWalletArgs.pubkey' " := ( FlexDeployWalletArgs_ι_pubkey_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDeployWalletArgs_ι_internal_owner_right {b} (x: URValue FlexDeployWalletArgsLRecord b): URValue address b :=
    || {x} ^^ {FlexDeployWalletArgs_ι_internal_owner} || : _ .
    
Definition FlexDeployWalletArgs_ι_internal_owner_left (x: ULValue FlexDeployWalletArgsLRecord): ULValue address :=
    {{ {x} ^^ {FlexDeployWalletArgs_ι_internal_owner} }} : _.
    
Notation " a '↑' 'FlexDeployWalletArgs.internal_owner' " := ( FlexDeployWalletArgs_ι_internal_owner_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDeployWalletArgs.internal_owner' " := ( FlexDeployWalletArgs_ι_internal_owner_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition FlexDeployWalletArgs_ι_grams_right {b} (x: URValue FlexDeployWalletArgsLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {FlexDeployWalletArgs_ι_grams} || : _ .
    
Definition FlexDeployWalletArgs_ι_grams_left (x: ULValue FlexDeployWalletArgsLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {FlexDeployWalletArgs_ι_grams} }} : _.
    
Notation " a '↑' 'FlexDeployWalletArgs.grams' " := ( FlexDeployWalletArgs_ι_grams_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'FlexDeployWalletArgs.grams' " := ( FlexDeployWalletArgs_ι_grams_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_name_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XString b :=
    || {x} ^^ {wrapper_details_info_ι_name} || : _ .
    
Definition wrapper_details_info_ι_name_left (x: ULValue wrapper_details_infoLRecord): ULValue XString :=
    {{ {x} ^^ {wrapper_details_info_ι_name} }} : _.
    
Notation " a '↑' 'wrapper_details_info.name' " := ( wrapper_details_info_ι_name_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.name' " := ( wrapper_details_info_ι_name_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_symbol_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XString b :=
    || {x} ^^ {wrapper_details_info_ι_symbol} || : _ .
    
Definition wrapper_details_info_ι_symbol_left (x: ULValue wrapper_details_infoLRecord): ULValue XString :=
    {{ {x} ^^ {wrapper_details_info_ι_symbol} }} : _.
    
Notation " a '↑' 'wrapper_details_info.symbol' " := ( wrapper_details_info_ι_symbol_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.symbol' " := ( wrapper_details_info_ι_symbol_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_decimals_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {wrapper_details_info_ι_decimals} || : _ .
    
Definition wrapper_details_info_ι_decimals_left (x: ULValue wrapper_details_infoLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {wrapper_details_info_ι_decimals} }} : _.
    
Notation " a '↑' 'wrapper_details_info.decimals' " := ( wrapper_details_info_ι_decimals_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.decimals' " := ( wrapper_details_info_ι_decimals_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_root_public_key_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {wrapper_details_info_ι_root_public_key} || : _ .
    
Definition wrapper_details_info_ι_root_public_key_left (x: ULValue wrapper_details_infoLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {wrapper_details_info_ι_root_public_key} }} : _.
    
Notation " a '↑' 'wrapper_details_info.root_public_key' " := ( wrapper_details_info_ι_root_public_key_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.root_public_key' " := ( wrapper_details_info_ι_root_public_key_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_total_granted_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {wrapper_details_info_ι_total_granted} || : _ .
    
Definition wrapper_details_info_ι_total_granted_left (x: ULValue wrapper_details_infoLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {wrapper_details_info_ι_total_granted} }} : _.
    
Notation " a '↑' 'wrapper_details_info.total_granted' " := ( wrapper_details_info_ι_total_granted_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.total_granted' " := ( wrapper_details_info_ι_total_granted_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_wallet_code_right {b} (x: URValue wrapper_details_infoLRecord b): URValue XCell b :=
    || {x} ^^ {wrapper_details_info_ι_wallet_code} || : _ .
    
Definition wrapper_details_info_ι_wallet_code_left (x: ULValue wrapper_details_infoLRecord): ULValue XCell :=
    {{ {x} ^^ {wrapper_details_info_ι_wallet_code} }} : _.
    
Notation " a '↑' 'wrapper_details_info.wallet_code' " := ( wrapper_details_info_ι_wallet_code_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.wallet_code' " := ( wrapper_details_info_ι_wallet_code_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_owner_address_right {b} (x: URValue wrapper_details_infoLRecord b): URValue address b :=
    || {x} ^^ {wrapper_details_info_ι_owner_address} || : _ .
    
Definition wrapper_details_info_ι_owner_address_left (x: ULValue wrapper_details_infoLRecord): ULValue address :=
    {{ {x} ^^ {wrapper_details_info_ι_owner_address} }} : _.
    
Notation " a '↑' 'wrapper_details_info.owner_address' " := ( wrapper_details_info_ι_owner_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.owner_address' " := ( wrapper_details_info_ι_owner_address_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition wrapper_details_info_ι_external_wallet_right {b} (x: URValue wrapper_details_infoLRecord b): URValue address b :=
    || {x} ^^ {wrapper_details_info_ι_external_wallet} || : _ .
    
Definition wrapper_details_info_ι_external_wallet_left (x: ULValue wrapper_details_infoLRecord): ULValue address :=
    {{ {x} ^^ {wrapper_details_info_ι_external_wallet} }} : _.
    
Notation " a '↑' 'wrapper_details_info.external_wallet' " := ( wrapper_details_info_ι_external_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'wrapper_details_info.external_wallet' " := ( wrapper_details_info_ι_external_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_name__right {b} (x: URValue DWrapperLRecord b): URValue XString b :=
    || {x} ^^ {DWrapper_ι_name_} || : _ .
    
Definition DWrapper_ι_name__left (x: ULValue DWrapperLRecord): ULValue XString :=
    {{ {x} ^^ {DWrapper_ι_name_} }} : _.
    
Notation " a '↑' 'DWrapper.name_' " := ( DWrapper_ι_name__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.name_' " := ( DWrapper_ι_name__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_symbol__right {b} (x: URValue DWrapperLRecord b): URValue XString b :=
    || {x} ^^ {DWrapper_ι_symbol_} || : _ .
    
Definition DWrapper_ι_symbol__left (x: ULValue DWrapperLRecord): ULValue XString :=
    {{ {x} ^^ {DWrapper_ι_symbol_} }} : _.
    
Notation " a '↑' 'DWrapper.symbol_' " := ( DWrapper_ι_symbol__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.symbol_' " := ( DWrapper_ι_symbol__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_decimals__right {b} (x: URValue DWrapperLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DWrapper_ι_decimals_} || : _ .
    
Definition DWrapper_ι_decimals__left (x: ULValue DWrapperLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DWrapper_ι_decimals_} }} : _.
    
Notation " a '↑' 'DWrapper.decimals_' " := ( DWrapper_ι_decimals__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.decimals_' " := ( DWrapper_ι_decimals__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_workchain_id__right {b} (x: URValue DWrapperLRecord b): URValue XInteger (* XUInteger8 *) b :=
    || {x} ^^ {DWrapper_ι_workchain_id_} || : _ .
    
Definition DWrapper_ι_workchain_id__left (x: ULValue DWrapperLRecord): ULValue XInteger (* XUInteger8 *) :=
    {{ {x} ^^ {DWrapper_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DWrapper.workchain_id_' " := ( DWrapper_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.workchain_id_' " := ( DWrapper_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_root_public_key__right {b} (x: URValue DWrapperLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DWrapper_ι_root_public_key_} || : _ .
    
Definition DWrapper_ι_root_public_key__left (x: ULValue DWrapperLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DWrapper_ι_root_public_key_} }} : _.
    
Notation " a '↑' 'DWrapper.root_public_key_' " := ( DWrapper_ι_root_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.root_public_key_' " := ( DWrapper_ι_root_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_total_granted__right {b} (x: URValue DWrapperLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DWrapper_ι_total_granted_} || : _ .
    
Definition DWrapper_ι_total_granted__left (x: ULValue DWrapperLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DWrapper_ι_total_granted_} }} : _.
    
Notation " a '↑' 'DWrapper.total_granted_' " := ( DWrapper_ι_total_granted__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.total_granted_' " := ( DWrapper_ι_total_granted__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_owner_address__right {b} (x: URValue DWrapperLRecord b): URValue ( XMaybe address ) b :=
    || {x} ^^ {DWrapper_ι_owner_address_} || : _ .
    
Definition DWrapper_ι_owner_address__left (x: ULValue DWrapperLRecord): ULValue ( XMaybe address ) :=
    {{ {x} ^^ {DWrapper_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DWrapper.owner_address_' " := ( DWrapper_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.owner_address_' " := ( DWrapper_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_internal_wallet_code__right {b} (x: URValue DWrapperLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DWrapper_ι_internal_wallet_code_} || : _ .
    
Definition DWrapper_ι_internal_wallet_code__left (x: ULValue DWrapperLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DWrapper_ι_internal_wallet_code_} }} : _.
    
Notation " a '↑' 'DWrapper.internal_wallet_code_' " := ( DWrapper_ι_internal_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.internal_wallet_code_' " := ( DWrapper_ι_internal_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_start_balance__right {b} (x: URValue DWrapperLRecord b): URValue Grams b :=
    || {x} ^^ {DWrapper_ι_start_balance_} || : _ .
    
Definition DWrapper_ι_start_balance__left (x: ULValue DWrapperLRecord): ULValue Grams :=
    {{ {x} ^^ {DWrapper_ι_start_balance_} }} : _.
    
Notation " a '↑' 'DWrapper.start_balance_' " := ( DWrapper_ι_start_balance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.start_balance_' " := ( DWrapper_ι_start_balance__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DWrapper_ι_external_wallet__right {b} (x: URValue DWrapperLRecord b): URValue (XMaybe address) b :=
    || {x} ^^ {DWrapper_ι_external_wallet_} || : _ .
    
Definition DWrapper_ι_external_wallet__left (x: ULValue DWrapperLRecord): ULValue (XMaybe address) :=
    {{ {x} ^^ {DWrapper_ι_external_wallet_} }} : _.
    
Notation " a '↑' 'DWrapper.external_wallet_' " := ( DWrapper_ι_external_wallet__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DWrapper.external_wallet_' " := ( DWrapper_ι_external_wallet__left a ) (in custom ULValue at level 0) : ursus_scope.

(***************************************************************************************************)

(* Inductive IWrapperP :=
    | Iinit : address -> IWrapperP
    | IsetInternalWalletCode : XCell -> IWrapperP
    | IdeployEmptyWallet : XUInteger256 -> address -> XUInteger128 -> IWrapperP
    | IonTip3Transfer : address -> XUInteger128 -> XUInteger128 -> XUInteger256 -> 
                                                address -> XCell -> IWrapperP
    | Iburn : address -> XUInteger256 -> address -> XUInteger256 -> 
                                                address -> XUInteger128 -> IWrapperP
    | IhasInternalWalletCode : IWrapperP

    | _Icreate : InitialState -> IWrapperP. *)

Definition Iinit_right { a1 }  ( x : URValue address a1 ) : URValue IWrapper a1.
 pose proof (urvalue_bind x (fun x' => #(Iinit x' : IWrapper)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.init' ( x ) " := (Iinit_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .
 
Definition IsetInternalWalletCode_right { a1 }  ( x : URValue XCell a1 ) : URValue IWrapper a1.
 pose proof (urvalue_bind x (fun x' => #(IsetInternalWalletCode x' : IWrapper)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.setInternalWalletCode' ( x ) " := (IsetInternalWalletCode_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .

Definition IdeployEmptyWallet_right { a1 a2 a3}  (x : URValue XUInteger256 a1 ) 
                                                 (y : URValue address a2) 
                                                 (z : URValue XUInteger128 a3) : URValue IWrapper ( (orb  a1 (orb a2 a3)) ).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  #(IdeployEmptyWallet x' y' z' : IWrapper)))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.deployEmptyWallet' ( x , y , z ) " := (IdeployEmptyWallet_right x y z) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0) : ursus_scope .

(* | IonTip3Transfer : address -> XUInteger128 -> XUInteger128 -> XUInteger256 -> address -> XCell -> IWrapperP *)
Definition IonTip3Transfer_right { a1 a2 a3 a4 a5 a6 }  (x : URValue address a1 ) 
                                                 (y : URValue XUInteger128 a2) 
                                                 (z : URValue XUInteger128 a3)
                                                 (t : URValue XUInteger256 a4)
                                                 (u : URValue address a5)
                                                 (v : URValue XCell a6) : URValue IWrapper (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 a6))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  #(IonTip3Transfer x' y' z' t' u' v' : IWrapper))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.onTip3Transfer' ( x , y , z , t , u , v ) " := (IonTip3Transfer_right x y z t u v) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, v custom URValue at level 0 ) : ursus_scope .

(* | Iburn : address -> XUInteger256 -> address -> XUInteger256 -> 
                                                address -> XUInteger128 -> IWrapperP *)
Definition Iburn_right { a1 a2 a3 a4 a5 a6 }  (x : URValue address a1 ) 
                                                 (y : URValue XUInteger256 a2) 
                                                 (z : URValue address a3)
                                                 (t : URValue XUInteger256 a4)
                                                 (u : URValue address a5)
                                                 (v : URValue XUInteger128 a6) : URValue IWrapper (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 a6))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  #(Iburn x' y' z' t' u' v' : IWrapper))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.burn' ( x , y , z , t , u , v ) " := (Iburn_right x y z t u v) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, v custom URValue at level 0 ) : ursus_scope .


Definition IhasInternalWalletCode_right : URValue IWrapper false.
 refine (# IhasInternalWalletCode ) .
Defined.

Notation " '.hasInternalWalletCode' '()' " := (IhasInternalWalletCode_right) (in custom URValue at level 0 ) : ursus_scope .
 
Definition _Icreate_right { a1 }  ( x : URValue StateInitLRecord a1 ) : URValue IWrapper a1.
 pose proof (urvalue_bind x (fun x' => #(_Icreate x' : IWrapper)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'Wrapper.deploy' ( x ) " := (_Icreate_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .
 

End ClassTypesNotations.