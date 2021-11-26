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

(* MOVE TO PRICE *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
(* 1 *) Inductive DFlexClientFields := | DFlexClient_ι_owner_ | DFlexClient_ι_trading_pair_code_ | DFlexClient_ι_xchg_pair_code_ | DFlexClient_ι_workchain_id_ | DFlexClient_ι_tons_cfg_ | DFlexClient_ι_flex_ | DFlexClient_ι_ext_wallet_code_ | DFlexClient_ι_flex_wallet_code_ | DFlexClient_ι_flex_wrapper_code_ .


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Locate XBool.
 
(* 2 *) Definition DFlexClientL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( XCell ) : Type ; 
 ( XCell ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( XAddress ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ] .
Elpi GeneratePruvendoRecord DFlexClientL DFlexClientFields . 
 Opaque DFlexClientLRecord . 



(* 2 *) Definition SellArgsL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord SellArgsL SellArgsFields . 
 Opaque SellArgsLRecord . 


End ClassTypes .
 