Require Import FinProof.ProgrammingWith. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.

Inductive DRootTokenContractFields := | DRootTokenContract_ι_name_ | DRootTokenContract_ι_symbol_ | DRootTokenContract_ι_decimals_ | DRootTokenContract_ι_root_public_key_ | DRootTokenContract_ι_total_supply_ | DRootTokenContract_ι_total_granted_ | DRootTokenContract_ι_wallet_code_ | DRootTokenContract_ι_owner_address_ | DRootTokenContract_ι_start_balance_ .

Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

Definition DRootTokenContractL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( XUInteger (* Grams *) ) : Type ] .
Elpi GeneratePruvendoRecord DRootTokenContractL DRootTokenContractFields . 

End ClassTypes .
 