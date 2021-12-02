Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonAxioms.

Require Import Wrapper.ClassTypes.
Require Import Wrapper.ClassTypesNotations.
Require Import Wrapper.Ledger.


Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter getStateInit : (*???????????????*) ULValue PhantomType -> UExpression StateInitLRecord false . 
Parameter init : address -> UExpression boolean true . 
Parameter setInternalWalletCode : cell -> UExpression boolean true . 
Parameter deployEmptyWallet : uint256 -> address -> uint128 -> UExpression address false . 
Parameter onTip3Transfer : address -> uint128 -> uint128 -> uint256 -> address -> cell -> UExpression WrapperRetLRecord true . 
Parameter burn : address -> uint256 -> address -> uint256 -> address -> uint128 -> UExpression PhantomType true . 
Parameter requestTotalGranted : UExpression uint128 false . 
Parameter getDetails : UExpression wrapper_details_infoLRecord false . 
Parameter getName : UExpression String false . 
Parameter getSymbol : UExpression String false . 
Parameter getDecimals : UExpression uint8 false . 
Parameter getRootKey : UExpression uint256 false . 
Parameter getTotalGranted : UExpression uint128 false . 
Parameter hasInternalWalletCode : UExpression boolean false . 
Parameter getInternalWalletCode : UExpression cell false . 
Parameter getOwnerAddress : UExpression address false . 
Parameter getExternalWallet : UExpression address false . 
Parameter getWalletAddress : uint256 -> address -> UExpression address false . 
Parameter _on_bounced : cell -> slice -> UExpression uint true . 
Parameter getInternalWalletCodeHash : UExpression uint256 false . 
Parameter _fallback : cell -> slice -> UExpression uint false . 
Parameter optional_owner : address -> UExpression (optional address) false . 
Parameter expected_internal_address : uint256 -> address -> UExpression address false . 
Parameter calc_internal_wallet_init : uint256 -> address -> UExpression ( StateInitLRecord # address ) false . 
Parameter is_internal_owner : UExpression boolean false . 
Parameter check_internal_owner : UExpression PhantomType true . 
Parameter check_external_owner : UExpression PhantomType true . 
Parameter check_owner : UExpression PhantomType false . 
Parameter prepare_wrapper_state_init_and_addr : cell ->  ContractLRecord -> UExpression ( StateInitLRecord # uint256 ) false . 


End SpecSig.

End Spec.  