Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.

Require Import FlexClient.ClassTypes.
Require Import FlexClient.Interface.

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).

Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.
Module Export InterfaceModule := PublicInterface xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition DFlexClient_ι_owner__right {b} (x: URValue DFlexClientLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DFlexClient_ι_owner_} || : _.
    
Definition DFlexClient_ι_owner__left (x: ULValue DFlexClientLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DFlexClient_ι_owner_} }} : _.
    
Notation " a '↑' 'DFlexClient.owner_' " := ( DFlexClient_ι_owner__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.owner_' " := ( DFlexClient_ι_owner__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_trading_pair_code__right {b} (x: URValue DFlexClientLRecord b): URValue XCell b :=
    || {x} ^^ {DFlexClient_ι_trading_pair_code_} || : _.
    
Definition DFlexClient_ι_trading_pair_code__left (x: ULValue DFlexClientLRecord): ULValue XCell :=
    {{ {x} ^^ {DFlexClient_ι_trading_pair_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.trading_pair_code_' " := ( DFlexClient_ι_trading_pair_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.trading_pair_code_' " := ( DFlexClient_ι_trading_pair_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_xchg_pair_code__right {b} (x: URValue DFlexClientLRecord b): URValue XCell b :=
    || {x} ^^ {DFlexClient_ι_xchg_pair_code_} || : _.
    
Definition DFlexClient_ι_xchg_pair_code__left (x: ULValue DFlexClientLRecord): ULValue XCell :=
    {{ {x} ^^ {DFlexClient_ι_xchg_pair_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.xchg_pair_code_' " := ( DFlexClient_ι_xchg_pair_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.xchg_pair_code_' " := ( DFlexClient_ι_xchg_pair_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_workchain_id__right {b} (x: URValue DFlexClientLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DFlexClient_ι_workchain_id_} || : _.
    
Definition DFlexClient_ι_workchain_id__left (x: ULValue DFlexClientLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DFlexClient_ι_workchain_id_} }} : _.
    
Notation " a '↑' 'DFlexClient.workchain_id_' " := ( DFlexClient_ι_workchain_id__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.workchain_id_' " := ( DFlexClient_ι_workchain_id__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_tons_cfg__right {b} (x: URValue DFlexClientLRecord b): URValue TonsConfigLRecord b :=
    || {x} ^^ {DFlexClient_ι_tons_cfg_} || : _.
    
Definition DFlexClient_ι_tons_cfg__left (x: ULValue DFlexClientLRecord): ULValue TonsConfigLRecord :=
    {{ {x} ^^ {DFlexClient_ι_tons_cfg_} }} : _.
    
Notation " a '↑' 'DFlexClient.tons_cfg_' " := ( DFlexClient_ι_tons_cfg__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.tons_cfg_' " := ( DFlexClient_ι_tons_cfg__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_flex__right {b} (x: URValue DFlexClientLRecord b): URValue XAddress b :=
    || {x} ^^ {DFlexClient_ι_flex_} || : _.
    
Definition DFlexClient_ι_flex__left (x: ULValue DFlexClientLRecord): ULValue XAddress :=
    {{ {x} ^^ {DFlexClient_ι_flex_} }} : _.
    
Notation " a '↑' 'DFlexClient.flex_' " := ( DFlexClient_ι_flex__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.flex_' " := ( DFlexClient_ι_flex__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_ext_wallet_code__right {b} (x: URValue DFlexClientLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlexClient_ι_ext_wallet_code_} || : _.
    
Definition DFlexClient_ι_ext_wallet_code__left (x: ULValue DFlexClientLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlexClient_ι_ext_wallet_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.ext_wallet_code_' " := ( DFlexClient_ι_ext_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.ext_wallet_code_' " := ( DFlexClient_ι_ext_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_flex_wallet_code__right {b} (x: URValue DFlexClientLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlexClient_ι_flex_wallet_code_} || : _.
    
Definition DFlexClient_ι_flex_wallet_code__left (x: ULValue DFlexClientLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlexClient_ι_flex_wallet_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.flex_wallet_code_' " := ( DFlexClient_ι_flex_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.flex_wallet_code_' " := ( DFlexClient_ι_flex_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DFlexClient_ι_flex_wrapper_code__right {b} (x: URValue DFlexClientLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DFlexClient_ι_flex_wrapper_code_} || : _.
    
Definition DFlexClient_ι_flex_wrapper_code__left (x: ULValue DFlexClientLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DFlexClient_ι_flex_wrapper_code_} }} : _.
    
Notation " a '↑' 'DFlexClient.flex_wrapper_code_' " := ( DFlexClient_ι_flex_wrapper_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DFlexClient.flex_wrapper_code_' " := ( DFlexClient_ι_flex_wrapper_code__left a ) (in custom ULValue at level 0) : ursus_scope.

(*interface*)
(* Inductive IFlexClientP :=
| Iconstructor : XUInteger256 -> XCell -> XCell -> IFlexClientP
| IsetFlexCfg   : TonsConfigLRecord -> XAddress -> IFlexClientP
| IsetExtWalletCode : XCell -> IFlexClientP
| IsetFlexWalletCode : XCell -> IFlexClientP
| IsetFlexWrapperCode : XCell -> IFlexClientP
| _Icreate : InitialState -> IFlexClientP.
 *)

Definition Iconstructor_right { a1 a2 a3 } (x : URValue XUInteger256 a1 ) 
                                       (y : URValue XCell a2) 
                                       (z : URValue XCell a3)
                                        : URValue IFlexClient (orb a1 (orb a2 a3)).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  #(Iconstructor x' y' z'  : IFlexClient)))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.contructor' ( x , y , z  ) " := (Iconstructor_right x y z) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0) : ursus_scope .

Definition IsetFlexCfg_right { a1 a2 } (x : URValue TonsConfigLRecord a1 ) 
                                       (y : URValue XAddress a2) 
                                        : URValue IFlexClient (orb a1 a2).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' => #(IsetFlexCfg x' y'  : IFlexClient))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.setFlexCfg' ( x , y  ) " := (IsetFlexCfg_right x y) 
(in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0 ) : ursus_scope .


Definition _Icreate_right { a1 }  ( x : URValue InitialStateLRecord a1 ) : URValue IFlexClient a1.
 pose proof (urvalue_bind x (fun x' => #(_Icreate x' : IFlexClient)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'FlexClient.create' ( x ) " := (_Icreate_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .

Definition IsetFlexWrapperCode_right { a1 }  ( x : URValue XCell a1 ) : URValue IFlexClient a1.
 pose proof (urvalue_bind x (fun x' => #(IsetFlexWrapperCode x' : IFlexClient)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.setFlexWrapperCode' ( x ) " := (IsetFlexWrapperCode_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .

Definition IsetFlexWalletCode_right { a1 }  ( x : URValue XCell a1 ) : URValue IFlexClient a1.
 pose proof (urvalue_bind x (fun x' => #(IsetFlexWalletCode x' : IFlexClient)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.setFlexWalletCode' ( x ) " := (IsetFlexWalletCode_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .

Definition IsetExtWalletCode_right { a1 }  ( x : URValue XCell a1 ) : URValue IFlexClient a1.
 pose proof (urvalue_bind x (fun x' => #(IsetExtWalletCode x' : IFlexClient)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.setExtWalletCode' ( x ) " := (IsetExtWalletCode_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .


End ClassTypesNotations.


