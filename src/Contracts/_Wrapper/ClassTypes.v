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


Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.

(* 1 *) Inductive WrapperRetFields := | WrapperRet_ι_err_code | WrapperRet_ι_flex_wallet .
(* 1 *) Inductive FlexDeployWalletArgsFields := | FlexDeployWalletArgs_ι_pubkey | FlexDeployWalletArgs_ι_internal_owner | FlexDeployWalletArgs_ι_grams .
(* 1 *) Inductive wrapper_details_infoFields := | wrapper_details_info_ι_name | wrapper_details_info_ι_symbol | wrapper_details_info_ι_decimals | wrapper_details_info_ι_root_public_key | wrapper_details_info_ι_total_granted | wrapper_details_info_ι_wallet_code | wrapper_details_info_ι_owner_address | wrapper_details_info_ι_external_wallet .
(* 1 *) Inductive ContractFields := | name_ | symbol_ | decimals_ | workchain_id_ | root_public_key_ | total_granted_ | internal_wallet_code_ | owner_address_ | start_balance_ | external_wallet_ .

(* 2 *) Definition WrapperRetL : list Type := 
 [ ( XInteger32 ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord WrapperRetL WrapperRetFields . 
 Opaque WrapperRetLRecord . 

(* 2 *) Definition FlexDeployWalletArgsL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord FlexDeployWalletArgsL FlexDeployWalletArgsFields . 
 Opaque FlexDeployWalletArgsLRecord . 

(* 2 *) Definition wrapper_details_infoL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( XAddress ) : Type ; 
 ( XAddress ) : Type ] .
Elpi GeneratePruvendoRecord wrapper_details_infoL wrapper_details_infoFields . 
 Opaque wrapper_details_infoLRecord . 

(* 2 *) Definition ContractL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XInteger256 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe XAddress ) ) : Type ; 
 ( GramsLRecord ) : Type ; 
 ( ( XMaybe ITONTokenWalletPtrLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord ContractL ContractFields . 
 Opaque ContractLRecord . 

End ClassTypes .
 