Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonAxioms.

Require Import RootTokenContract.ClassTypes.
Require Import RootTokenContract.Interface.
(* Require Import RootTokenContract.Ledger. *)

Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).

Module Export CommonAxiomsModule := CommonAxioms xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.
Module Export InterfaceModule := PublicInterface xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition DRootTokenContract_ι_name__right {b} (x: URValue DRootTokenContractLRecord b): URValue XString b :=
    || {x} ^^ {DRootTokenContract_ι_name_} || : _.
    
Definition DRootTokenContract_ι_name__left (x: ULValue DRootTokenContractLRecord): ULValue XString :=
    {{ {x} ^^ {DRootTokenContract_ι_name_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.name_' " := ( DRootTokenContract_ι_name__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.name_' " := ( DRootTokenContract_ι_name__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_symbol__right {b} (x: URValue DRootTokenContractLRecord b): URValue XString b :=
    || {x} ^^ {DRootTokenContract_ι_symbol_} || : _.
    
Definition DRootTokenContract_ι_symbol__left (x: ULValue DRootTokenContractLRecord): ULValue XString :=
    {{ {x} ^^ {DRootTokenContract_ι_symbol_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.symbol_' " := ( DRootTokenContract_ι_symbol__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.symbol_' " := ( DRootTokenContract_ι_symbol__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_decimals__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {DRootTokenContract_ι_decimals_} || : _.
    
Definition DRootTokenContract_ι_decimals__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {DRootTokenContract_ι_decimals_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.decimals_' " := ( DRootTokenContract_ι_decimals__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.decimals_' " := ( DRootTokenContract_ι_decimals__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_root_public_key__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {DRootTokenContract_ι_root_public_key_} || : _.
    
Definition DRootTokenContract_ι_root_public_key__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {DRootTokenContract_ι_root_public_key_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.root_public_key_' " := ( DRootTokenContract_ι_root_public_key__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.root_public_key_' " := ( DRootTokenContract_ι_root_public_key__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_total_supply__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DRootTokenContract_ι_total_supply_} || : _.
    
Definition DRootTokenContract_ι_total_supply__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DRootTokenContract_ι_total_supply_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.total_supply_' " := ( DRootTokenContract_ι_total_supply__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.total_supply_' " := ( DRootTokenContract_ι_total_supply__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_total_granted__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger128 b :=
    || {x} ^^ {DRootTokenContract_ι_total_granted_} || : _.
    
Definition DRootTokenContract_ι_total_granted__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger128 :=
    {{ {x} ^^ {DRootTokenContract_ι_total_granted_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.total_granted_' " := ( DRootTokenContract_ι_total_granted__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.total_granted_' " := ( DRootTokenContract_ι_total_granted__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_wallet_code__right {b} (x: URValue DRootTokenContractLRecord b): URValue ( XMaybe XCell ) b :=
    || {x} ^^ {DRootTokenContract_ι_wallet_code_} || : _.
    
Definition DRootTokenContract_ι_wallet_code__left (x: ULValue DRootTokenContractLRecord): ULValue ( XMaybe XCell ) :=
    {{ {x} ^^ {DRootTokenContract_ι_wallet_code_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.wallet_code_' " := ( DRootTokenContract_ι_wallet_code__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.wallet_code_' " := ( DRootTokenContract_ι_wallet_code__left a ) (in custom ULValue at level 0) : ursus_scope.

Definition DRootTokenContract_ι_owner_address__right {b} (x: URValue DRootTokenContractLRecord b): URValue ( XMaybe address ) b :=
    || {x} ^^ {DRootTokenContract_ι_owner_address_} || : _.
    
Definition DRootTokenContract_ι_owner_address__left (x: ULValue DRootTokenContractLRecord): ULValue ( XMaybe address ) :=
    {{ {x} ^^ {DRootTokenContract_ι_owner_address_} }} : _.
    
Notation " a '↑' 'DRootTokenContract_ι_owner_address_' " := ( DRootTokenContract_ι_owner_address__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract_ι_owner_address_' " := ( DRootTokenContract_ι_owner_address__left a ) (in custom ULValue at level 0) : ursus_scope.


Definition DRootTokenContract_ι_start_balance__right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger b :=
    || {x} ^^ {DRootTokenContract_ι_start_balance_} || : _.
    
Definition DRootTokenContract_ι_start_balance__left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger :=
    {{ {x} ^^ {DRootTokenContract_ι_start_balance_} }} : _.
    
Notation " a '↑' 'DRootTokenContract.start_balance_' " := ( DRootTokenContract_ι_start_balance__right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'DRootTokenContract.start_balance_' " := ( DRootTokenContract_ι_start_balance__left a ) (in custom ULValue at level 0) : ursus_scope.


Definition _Icreate_right { a1 }  ( x : URValue StateInitLRecord a1 ) : URValue IRootTokenContract a1.
 pose proof (urvalue_bind x (fun x' => #(_Icreate x' : IRootTokenContract)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " 'RootTokenWallet.deploy' ( x ) " := (_Icreate_right x) (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope .
 

(* Inductive IRootTokenContractP :=
6 | Iconstructor : XString -> XString -> XUInteger8 -> XUInteger256 -> address -> XUInteger128 -> IRootTokenContractP
4 | IdeployWallet : XUInteger256 -> address -> XUInteger128 -> XUInteger128 -> IRootTokenContractP
3 | IdeployEmptyWallet : XUInteger256 -> address -> XUInteger128 -> IRootTokenContractP
3 | Igrant : address -> XUInteger128 -> XUInteger128 -> IRootTokenContractP
1 | Imint : XUInteger128 -> IRootTokenContractP
0 | IrequestTotalGranted : IRootTokenContractP *)

Definition Iconstructor_right { a1 a2 a3 a4 a5 a6 }  (x : URValue XString a1 ) 
                                                 (y : URValue XString a2) 
                                                 (z : URValue XUInteger8 a3)
                                                 (t : URValue XUInteger256 a4)
                                                 (u : URValue address a5)
                                                 (v : URValue XUInteger128 a6) : URValue IRootTokenContract (orb a1 (orb a2 (orb a3 (orb a4 (orb a5 a6))))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  
                            urvalue_bind u (fun u' =>  
                                urvalue_bind v (fun v' =>  #(Iconstructor x' y' z' t' u' v' : IRootTokenContract))))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.constructor' ( x , y , z , t , u , v ) " := (Iconstructor_right x y z t u v) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 , u custom URValue at level 0, v custom URValue at level 0 ) : ursus_scope .

(* | IdeployWallet : XUInteger256 -> address -> XUInteger128 -> XUInteger128 -> IRootTokenContractP *)
Definition IdeployWallet_right { a1 a2 a3 a4 }  (x : URValue XUInteger256 a1 ) 
                                                 (y : URValue address a2) 
                                                 (z : URValue XUInteger128 a3)
                                                 (t : URValue XUInteger128 a4)
                                                  : URValue IRootTokenContract (orb a1 (orb a2 (orb a3 a4))).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  
                        urvalue_bind t (fun t' =>  #(IdeployWallet x' y' z' t'  : IRootTokenContract))))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.deployWallet' ( x , y , z , t ) " := (IdeployWallet_right x y z t) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0, 
 t custom URValue at level 0 ) : ursus_scope .

(* IdeployEmptyWallet : XUInteger256 -> address -> XUInteger128 -> IRootTokenContractP *)
Definition IdeployEmptyWallet_right { a1 a2 a3 } (x : URValue XUInteger256 a1 ) 
                                                 (y : URValue address a2) 
                                                 (z : URValue XUInteger128 a3)
                                                 : URValue IRootTokenContract (orb a1 (orb a2 a3)).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  #(IdeployEmptyWallet x' y' z'  : IRootTokenContract)))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.deployEmptyWallet' ( x , y , z  ) " := (IdeployEmptyWallet_right x y z) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0) : ursus_scope .

(* Igrant : address -> XUInteger128 -> XUInteger128 -> IRootTokenContractP *)
Definition Igrant_right { a1 a2 a3 } (x : URValue address a1 ) 
                                     (y : URValue XUInteger128 a2) 
                                     (z : URValue XUInteger128 a3)
                                    : URValue IRootTokenContract (orb a1 (orb a2 a3)).
 pose proof (urvalue_bind x (fun x' => 
                urvalue_bind y (fun y' =>
                    urvalue_bind z (fun z' =>  #(Igrant x' y' z'  : IRootTokenContract)))): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.grant' ( x , y , z ) " := (Igrant_right x y z) 
(in custom URValue at level 0 , x custom URValue at level 0,
 y custom URValue at level 0 , z custom URValue at level 0) : ursus_scope . 

(* Imint : XUInteger128 -> IRootTokenContractP *)
Definition Imint_right { a1 } (x : URValue XUInteger128 a1 ) : URValue IRootTokenContract a1.
 pose proof (urvalue_bind x (fun x' => #(Imint x'  : IRootTokenContract)): URValue _ _).
 rewrite right_or_false in X.
 refine X.
Defined.

Notation " '.mint' ( x ) " := (Imint_right x ) 
(in custom URValue at level 0 , x custom URValue at level 0) : ursus_scope . 


(* | IrequestTotalGranted : IRootTokenContractP *)
Definition  IrequestTotalGranted_right : URValue IRootTokenContract false.
 refine (#IrequestTotalGranted).
Defined.

Notation " '.requestTotalGranted' '()' " := (IrequestTotalGranted_right ) 
(in custom URValue at level 0 ) : ursus_scope . 


End ClassTypesNotations.


