Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import CommonNotations.
Require Import Contracts.RootTokenContract.ClassTypes.
Require Import Contracts.RootTokenContract.Ledger.
Require Import Contracts.RootTokenContract.ClassTypesNotations.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 
(* Module Export stdTypesNotationsModule := stdTypesNotations xt sm LedgerModuleForFuncSig. *)
Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter constructor : ( ( XString ) ) -> ( ( XString ) ) -> ( ( XUInteger8 ) ) -> ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XUInteger128 ) ) -> UExpression PhantomType true . 
 Parameter setWalletCode : ( ( XCell ) ) -> UExpression XBool true . 
 Parameter deployWallet : ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> UExpression XAddress true . 
 Parameter deployEmptyWallet : ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XUInteger128 ) ) -> UExpression XAddress true . 
 Parameter grant : ( ( XAddress ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> UExpression PhantomType true . 
 Parameter mint : ( ( XUInteger128 ) ) -> UExpression XBool false . 
 Parameter requestTotalGranted : UExpression XUInteger128 false . 
 Parameter getName : UExpression XString false . 
 Parameter getSymbol : UExpression XString false . 
 Parameter getDecimals : UExpression XUInteger8 false . 
 Parameter getRootKey : UExpression XUInteger256 false . 
 Parameter getTotalSupply : UExpression XUInteger128 false . 
 Parameter getTotalGranted : UExpression XUInteger128 false . 
 Parameter hasWalletCode : UExpression XBool false . 
 Parameter getWalletCode : UExpression XCell false . 
 Parameter getWalletAddress : ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> UExpression XAddress false . 
 Parameter _on_bounced : ( ( (LRecord ) ) -> ( ( XSlice ) ) -> UExpression XUInteger true . 
 Parameter getWalletCodeHash : UExpression XUInteger256 false . 
 Parameter _fallback : XCell -> XSlice -> UExpression XUInteger false . 
 Parameter optional_owner : ( ( XAddress ) ) -> UExpression XMaybe XAddress false . 
 Parameter workchain_id : UExpression XUInteger8 false . 
 Parameter calc_wallet_init : ( ( XUInteger256 ) ) -> ( ( XAddress ) ) -> UExpression ( StateInitLRecord * XAddress ) false . 
 Parameter is_internal_owner : UExpression XBool false . 
 Parameter check_internal_owner : UExpression PhantomType true . 
 Parameter check_external_owner : ( ( XBool ) ) -> UExpression PhantomType true . 
 Parameter check_owner : ( ( =LRecord ) ) -> UExpression PhantomType false . 
 Parameter prepare_root_state_init_and_addr : ( ( XCell ) ) -> ( ( DRootTokenContractLRecord ) ) -> UExpression ( StateInitLRecord * XUInteger256 ) false . 


End SpecSig.

End Spec.  