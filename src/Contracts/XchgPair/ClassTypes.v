Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdNotations.
Require Import UrsusStdLib.stdFuncNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.
Require Import FinProof.ProgrammingWith.  
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Import CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.


(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 2 *) Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 Opaque TickTockLRecord . 

(* 2 *) Definition StateInitL : list Type := 
 [ ( ( XMaybe XInteger ) ) : Type ; 
 ( ( XMaybe TickTockLRecord ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
 Opaque StateInitLRecord . 

End ClassTypes .
