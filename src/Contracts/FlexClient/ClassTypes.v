Require Import FinProof.ProgrammingWith. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.

Inductive DFlexClientFields := | DFlexClient_ι_owner_ | DFlexClient_ι_trading_pair_code_ | DFlexClient_ι_xchg_pair_code_ | DFlexClient_ι_workchain_id_ | DFlexClient_ι_tons_cfg_ | DFlexClient_ι_flex_ | DFlexClient_ι_ext_wallet_code_ | DFlexClient_ι_flex_wallet_code_ | DFlexClient_ι_flex_wrapper_code_ .

Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Definition DFlexClientL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( XCell ) : Type ; 
 ( XCell ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( TonsConfigLRecord ) : Type ; 
 ( address ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ] .
Elpi GeneratePruvendoRecord DFlexClientL DFlexClientFields . 

End ClassTypes .
 