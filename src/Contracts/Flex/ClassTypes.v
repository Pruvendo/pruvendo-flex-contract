Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdNotations.
Require Import UrsusStdLib.stdFuncNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.
Require Import FinProof.ProgrammingWith.  
Require Import UMLang.ClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) Inductive anycast_infoFields := | anycast_info_ι_rewrite_pfx | anycast_info_ι_1 .
(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 1 *) Inductive addr_stdFields := | addr_std_ι_kind | addr_std_ι_Anycast | addr_std_ι_workchain_id | addr_std_ι_address .
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 1 *) Inductive FlexOwnershipInfoFields := | FlexOwnershipInfo_ι_deployer_pubkey | FlexOwnershipInfo_ι_ownership_description | FlexOwnershipInfo_ι_owner_contract .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 1 *) Inductive DTradingPairFields := | DTradingPair_ι_flex_addr_ | DTradingPair_ι_tip3_root_ | DTradingPair_ι_deploy_value_ .
(* 1 *) Inductive DXchgPairFields := | DXchgPair_ι_flex_addr_ | DXchgPair_ι_tip3_major_root_ | DXchgPair_ι_tip3_minor_root_ | DXchgPair_ι_deploy_value_ .
 
(* 2 *) Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 Opaque TickTockLRecord . 

(* 2 *) Definition anycast_infoL : list Type := 
 [ ( XInteger32 ) : Type ;
( XInteger32 ) : Type ] .
Elpi GeneratePruvendoRecord anycast_infoL anycast_infoFields . 
 Opaque anycast_infoLRecord . 

(* 2 *) Definition addr_stdL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XMaybe anycast_infoLRecord ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ] .
Elpi GeneratePruvendoRecord addr_stdL addr_stdFields . 
 Opaque addr_stdLRecord . 

(* 2 *) Definition TonsConfigL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord TonsConfigL TonsConfigFields . 
 Opaque TonsConfigLRecord . 

(* 2 *) Definition FlexOwnershipInfoL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( XString ) : Type ; 
 ( XMaybe XAddress ) : Type ] .
Elpi GeneratePruvendoRecord FlexOwnershipInfoL FlexOwnershipInfoFields . 
 Opaque FlexOwnershipInfoLRecord . 


(* 2 *) Definition StateInitL : list Type := 
 [ ( XMaybe XInteger ) : Type ; 
 ( XMaybe TickTockLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
 Opaque StateInitLRecord . 

(* 2 *) Definition DTradingPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord DTradingPairL DTradingPairFields . 
 Opaque DTradingPairLRecord . 

(* 2 *) Definition DXchgPairL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord DXchgPairL DXchgPairFields . 
 Opaque DXchgPairLRecord . 


Check XBool.
 

End ClassTypes .
 