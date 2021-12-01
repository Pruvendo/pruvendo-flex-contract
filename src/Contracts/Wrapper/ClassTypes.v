Require Import FinProof.ProgrammingWith.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import Project.CommonTypes.

(* 1 *) Inductive WrapperRetFields := | WrapperRet_ι_err_code | WrapperRet_ι_flex_wallet .
(* 1 *) Inductive FlexDeployWalletArgsFields := | FlexDeployWalletArgs_ι_pubkey | FlexDeployWalletArgs_ι_internal_owner | FlexDeployWalletArgs_ι_grams .
(* 1 *) Inductive wrapper_details_infoFields := | wrapper_details_info_ι_name | wrapper_details_info_ι_symbol | wrapper_details_info_ι_decimals | wrapper_details_info_ι_root_public_key | wrapper_details_info_ι_total_granted | wrapper_details_info_ι_wallet_code | wrapper_details_info_ι_owner_address | wrapper_details_info_ι_external_wallet .
(* 1 *) Inductive DWrapperFields := | DWrapper_ι_name_ | DWrapper_ι_symbol_ | DWrapper_ι_decimals_ | DWrapper_ι_workchain_id_ | DWrapper_ι_root_public_key_ | DWrapper_ι_total_granted_ | DWrapper_ι_internal_wallet_code_ | DWrapper_ι_owner_address_ | DWrapper_ι_start_balance_ | DWrapper_ι_external_wallet_ .

Module ClassTypes (xt: XTypesSig) (sm: StateMonadSig) .
Module Export CommonTypes := Types xt sm.

Local Open Scope xlist_scope.
Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope glist_scope.
Opaque address .
(* 2 *) Definition WrapperRetL : list Type := 
 [ ( XUInteger32 ) : Type ; 
 ( address ) : Type ] .
Elpi GeneratePruvendoRecord WrapperRetL WrapperRetFields . 
 Opaque WrapperRetLRecord . 

(* 2 *) Definition FlexDeployWalletArgsL : list Type := 
 [ ( XUInteger256 ) : Type ; 
 ( address ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord FlexDeployWalletArgsL FlexDeployWalletArgsFields . 
 Opaque FlexDeployWalletArgsLRecord . 

(* 2 *) Definition wrapper_details_infoL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XCell ) : Type ; 
 ( address ) : Type ; 
 ( address ) : Type ] .
Elpi GeneratePruvendoRecord wrapper_details_infoL wrapper_details_infoFields . 
 Opaque wrapper_details_infoLRecord . 

(* 2 *) Definition DWrapperL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XInteger (* XUInteger8 *) ) : Type ; (* DWrapper_ι_workchain_id_ *)
 ( XUInteger256 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XMaybe XCell ) ) : Type ; 
 ( ( XMaybe address ) ) : Type ; 
 ( XUInteger16 (* Grams *) ) : Type ; 
 ( ( XMaybe address (* ITONTokenWalletPtrLRecord *) ) ) : Type ] .
Elpi GeneratePruvendoRecord DWrapperL DWrapperFields . 
 Opaque DWrapperLRecord . 

End ClassTypes .
 