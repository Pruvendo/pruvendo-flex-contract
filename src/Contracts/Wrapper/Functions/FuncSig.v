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

Parameter getStateInit : (*???????????????*) PhantomType -> UExpression StateInitLRecord false . 
Parameter init : ( ( XAddress ) ) -> UExpression XBool true . 
Parameter setInternalWalletCode : ( ( XCell ) ) -> UExpression XBool true . 
Parameter deployEmptyWallet : ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XUInteger128 ) ) -> UExpression XAddress false . 
Parameter onTip3Transfer : ( ( XAddress ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XCell ) ) -> UExpression WrapperRetLRecord true . 
Parameter burn : ( ( XAddress ) ) -> ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XUInteger128 ) ) -> UExpression PhantomType true . 
Parameter requestTotalGranted : UExpression XUInteger128 false . 
Parameter getDetails : UExpression wrapper_details_infoLRecord false . 
Parameter getName : UExpression XString false . 
Parameter getSymbol : UExpression XString false . 
Parameter getDecimals : UExpression XUInteger8 false . 
Parameter getRootKey : UExpression XUInteger256 false . 
Parameter getTotalGranted : UExpression XUInteger128 false . 
Parameter hasInternalWalletCode : UExpression XBool false . 
Parameter getInternalWalletCode : UExpression XCell false . 
Parameter getOwnerAddress : UExpression XAddress false . 
Parameter getExternalWallet : UExpression XAddress false . 
Parameter getWalletAddress : ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> UExpression XAddress false . 
Parameter _on_bounced : ( XCell ) -> ( ( XSlice ) ) -> UExpression XUInteger true . 
Parameter getInternalWalletCodeHash : UExpression XUInteger256 false . 
Parameter _fallback : ( ( XCell ) ) -> ( ( XSlice ) ) -> UExpression XUInteger false . 
Parameter optional_owner : ( ( XAddress ) ) -> UExpression (XMaybe XAddress) false . 
Parameter expected_internal_address : ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> UExpression XAddress false . 
Parameter calc_internal_wallet_init : ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> UExpression ( StateInitLRecord * XAddress ) false . 
Parameter is_internal_owner : UExpression XBool false . 
Parameter check_internal_owner : UExpression PhantomType true . 
Parameter check_external_owner : UExpression PhantomType true . 
Parameter check_owner : UExpression PhantomType false . 
Parameter prepare_wrapper_state_init_and_addr : ( ( XCell ) ) -> ( ( DWrapperLRecord ) ) -> UExpression ( StateInitLRecord * XUInteger256 ) false . 


End SpecSig.

End Spec.  