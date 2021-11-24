Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import CommonNotations.
Require Import Contracts.Wrapper.ClassTypes.
Require Import Contracts.Wrapper.Ledger.
Require Import Contracts.Wrapper.ClassTypesNotations.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 
(* Module Export stdTypesNotationsModule := stdTypesNotations xt sm LedgerModuleForFuncSig. *)
Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter getStateInit : ( () ) -> UExpression StateInitLRecord false . 
 Parameter init : ( ( XAddress ) ) -> UExpression XBool true . 
 Parameter setInternalWalletCode : ( ( XCell ) ) -> UExpression XBool true . 
 Parameter deployEmptyWallet : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> UExpression XAddress false . 
 Parameter onTip3Transfer : ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XCell ) ) -> UExpression WrapperRetLRecord true . 
 Parameter burn : ( ( XAddress ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> UExpression PhantomType true . 
 Parameter requestTotalGranted : UExpression XInteger128 false . 
 Parameter getDetails : UExpression wrapper_details_infoLRecord false . 
 Parameter getName : UExpression XString false . 
 Parameter getSymbol : UExpression XString false . 
 Parameter getDecimals : UExpression XInteger8 false . 
 Parameter getRootKey : UExpression XInteger256 false . 
 Parameter getTotalGranted : UExpression XInteger128 false . 
 Parameter hasInternalWalletCode : UExpression XBool false . 
 Parameter getInternalWalletCode : UExpression XCell false . 
 Parameter getOwnerAddress : UExpression XAddress false . 
 Parameter getExternalWallet : UExpression XAddress false . 
 Parameter getWalletAddress : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> UExpression XAddress false . 
 Parameter _on_bounced : ( XCell ) -> ( ( XSlice ) ) -> UExpression XInteger true . 
 Parameter getInternalWalletCodeHash : UExpression XInteger256 false . 
 Parameter _fallback : ( ( XCell ) ) -> ( ( XSlice ) ) -> UExpression XInteger false . 
 Parameter optional_owner : ( ( XAddress ) ) -> UExpression XMaybe XAddress false . 
 Parameter expected_internal_address : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> UExpression XAddress false . 
 Parameter calc_internal_wallet_init : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> UExpression ( StateInitLRecord * XAddress ) false . 
 Parameter is_internal_owner : UExpression XBool false . 
 Parameter check_internal_owner : UExpression PhantomType true . 
 Parameter check_external_owner : UExpression PhantomType true . 
 Parameter check_owner : UExpression PhantomType false . 
 Parameter prepare_wrapper_state_init_and_addr : ( ( XCell ) ) -> ( ( DWrapperLRecord ) ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 


End SpecSig.

End Spec.  