Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonNotations.

Require Import Wrapper.ClassTypes.
Require Import Wrapper.ClassTypesNotations.
Require Import Wrapper.Ledger.


Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter getStateInit : (*???????????????*) PhantomType -> UExpression StateInitLRecord false . 
Parameter init : raw_address -> UExpression boolean true . 
Parameter setInternalWalletCode : TvmCell -> UExpression boolean true . 
Parameter deployEmptyWallet : uint256 -> raw_address -> uint128 -> UExpression raw_address false . 
Parameter onTip3Transfer : raw_address -> uint128 -> uint128 -> uint256 -> raw_address -> TvmCell -> UExpression WrapperRetLRecord true . 
Parameter burn : raw_address -> uint256 -> raw_address -> uint256 -> raw_address -> uint128 -> UExpression PhantomType true . 
Parameter requestTotalGranted : UExpression uint128 false . 
Parameter getDetails : UExpression wrapper_details_infoLRecord false . 
Parameter getName : UExpression String false . 
Parameter getSymbol : UExpression String false . 
Parameter getDecimals : UExpression uint8 false . 
Parameter getRootKey : UExpression uint256 false . 
Parameter getTotalGranted : UExpression uint128 false . 
Parameter hasInternalWalletCode : UExpression boolean false . 
Parameter getInternalWalletCode : UExpression TvmCell false . 
Parameter getOwnerAddress : UExpression raw_address false . 
Parameter getExternalWallet : UExpression raw_address false . 
Parameter getWalletAddress : uint256 -> raw_address -> UExpression raw_address false . 
Parameter _on_bounced : TvmCell -> TvmSlice -> UExpression uint true . 
Parameter getInternalWalletCodeHash : UExpression uint256 false . 
Parameter _fallback : TvmCell -> TvmSlice -> UExpression uint false . 
Parameter optional_owner : raw_address -> UExpression (optional raw_address) false . 
Parameter expected_internal_address : uint256 -> raw_address -> UExpression raw_address false . 
Parameter calc_internal_wallet_init : uint256 -> raw_address -> UExpression ( StateInitLRecord # raw_address ) false . 
Parameter is_internal_owner : UExpression boolean false . 
Parameter check_internal_owner : UExpression PhantomType true . 
Parameter check_external_owner : UExpression PhantomType true . 
Parameter check_owner : UExpression PhantomType false . 
Parameter prepare_wrapper_state_init_and_addr : TvmCell ->  ContractLRecord -> UExpression ( StateInitLRecord # uint256 ) false . 


End SpecSig.

End Spec.  