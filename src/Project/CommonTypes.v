Require Import UMLang.BasicModuleTypes.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address .
Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address | Tip3Config_ι_workchain_id_.
Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .

Module Types (xt: XTypesSig) (sm: StateMonadSig).
Export xt. 

Module Export BasicTypesModule := BasicTypes xt sm.
Local Open Scope glist_scope.

Definition IFlexNotifyPtr := XAddress. 
Definition ITONTokenWalletPtr := XAddress. 
Definition IPricePtr := XAddress. 
Definition TokensType := XUInteger256. 
Definition WalletGramsType := XUInteger128. 
Definition Grams := XUInteger16 . 
(*******TODO***************************)
Definition auto := XUInteger . 
(**************************************)                            
Definition addr_std_compact := XAddress . 
Definition varuint32 := XUInteger32 .
Definition address_t := XAddress.
Definition IWrapperPtr := XAddress .


(* 2 *) Definition TonsConfigL : list Type := 
[ ( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord TonsConfigL TonsConfigFields . 

 Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 
 Definition addr_std_fixedL : list Type := 
 [ ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ] .
Elpi GeneratePruvendoRecord addr_std_fixedL addr_std_fixedFields . 
 
Definition Tip3ConfigL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ; 
 ( XAddress ) : Type ;
 ( XUInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord Tip3ConfigL Tip3ConfigFields . 

Definition StateInitL : list Type := 
 [ ( XMaybe XUInteger ) : Type ; 
 ( XMaybe TickTockLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
  
End Types.
