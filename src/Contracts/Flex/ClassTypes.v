
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
Module Import CommonTypes := Types xt sm.

Local Open Scope xlist_scope.


(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock | TickTock_ι_1 .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 1 *) Inductive TradingPairFields := | TradingPair_ι_flex_addr_ | TradingPair_ι_tip3_root_ | TradingPair_ι_deploy_value_ .
(* 1 *) Inductive XchgPairFields := | XchgPair_ι_flex_addr_ | XchgPair_ι_tip3_major_root_ | XchgPair_ι_tip3_minor_root_ | XchgPair_ι_deploy_value_ .
 
Check XBool.

(* 2 *) Definition TickTockStateL : list Type := 
 [ XBool : Type ; 
   XBool : Type ;
   XBool : Type ]%xlist .
GeneratePruvendoRecord TickTockStateL TickTockFields . 

(* 2 *) Definition StateInitStateL : list Type := 
 [ ( XMaybe XInteger ) : Type ; 
 ( XMaybe TickTockStateLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ] .
GeneratePruvendoRecord StateInitStateL StateInitFields . 
 
(* 2 *) Definition TonsConfigStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord TonsConfigStateL TonsConfigFields . 

(* 2 *) Definition TradingPairStateL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord TradingPairStateL TradingPairFields . 

(* 2 *) Definition XchgPairStateL : list Type := 
 [ ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord XchgPairStateL XchgPairFields . 
 
End ClassTypes .
 