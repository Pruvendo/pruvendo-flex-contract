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

Parameter constructor : ( ( XString ) ) -> ( ( XString ) ) -> ( ( XInteger8 ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> UExpression PhantomType true . 
 Parameter setWalletCode : ( ( XCell ) ) -> UExpression XBool true . 
 Parameter deployWallet : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> UExpression XAddress true . 
 Parameter deployEmptyWallet : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> UExpression XAddress true . 
 Parameter grant : ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> UExpression PhantomType true . 
 Parameter mint : ( ( XInteger128 ) ) -> UExpression XBool false . 
 Parameter requestTotalGranted : UExpression XInteger128 false . 
 Parameter getName : UExpression XString false . 
 Parameter getSymbol : UExpression XString false . 
 Parameter getDecimals : UExpression XInteger8 false . 
 Parameter getRootKey : UExpression XInteger256 false . 
 Parameter getTotalSupply : UExpression XInteger128 false . 
 Parameter getTotalGranted : UExpression XInteger128 false . 
 Parameter hasWalletCode : UExpression XBool false . 
 Parameter getWalletCode : UExpression XCell false . 
 Parameter getWalletAddress : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> UExpression XAddress false . 
 Parameter _on_bounced : ( ( (LRecord ) ) -> ( ( XSlice ) ) -> UExpression XInteger true . 
 Parameter getWalletCodeHash : UExpression XInteger256 false . 
 Parameter _fallback : XCell -> XSlice -> UExpression XInteger false . 
 Parameter optional_owner : ( ( XAddress ) ) -> UExpression XMaybe XAddress false . 
 Parameter workchain_id : UExpression XInteger8 false . 
 Parameter calc_wallet_init : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> UExpression ( StateInitLRecord * XAddress ) false . 
 Parameter is_internal_owner : UExpression XBool false . 
 Parameter check_internal_owner : UExpression PhantomType true . 
 Parameter check_external_owner : ( ( XBool ) ) -> UExpression PhantomType true . 
 Parameter check_owner : ( ( =LRecord ) ) -> UExpression PhantomType false . 
 Parameter prepare_root_state_init_and_addr : ( ( XCell ) ) -> ( ( DRootTokenContractLRecord ) ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 


End SpecSig.

End Spec.  