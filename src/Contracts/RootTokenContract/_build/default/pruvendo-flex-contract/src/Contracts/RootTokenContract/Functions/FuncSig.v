Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonNotations.

Require Import RootTokenContract.ClassTypes.
Require Import RootTokenContract.Ledger.
Require Import RootTokenContract.ClassTypesNotations.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 
Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter constructor : String -> String -> uint8 ->  uint256 -> raw_address -> uint128 -> UExpression PhantomType true . 
Parameter setWalletCode : TvmCell -> UExpression boolean true . 
Parameter deployWallet : uint256  -> raw_address -> uint128 -> uint128 -> UExpression raw_address true . 
Parameter deployEmptyWallet : uint256 -> raw_address -> uint128 -> UExpression raw_address true . 
Parameter grant : raw_address -> uint128 -> uint128 -> UExpression PhantomType true . 
Parameter mint : uint128 -> UExpression boolean false . 
Parameter requestTotalGranted : UExpression uint128 false . 
Parameter getName : UExpression String false . 
Parameter getSymbol : UExpression String false . 
Parameter getDecimals : UExpression uint8 false . 
Parameter getRootKey : UExpression uint256 false . 
Parameter getTotalSupply : UExpression uint128 false . 
Parameter getTotalGranted : UExpression uint128 false . 
Parameter hasWalletCode : UExpression boolean false . 
Parameter getWalletCode : UExpression TvmCell false . 
Parameter getWalletAddress :  uint256 -> raw_address -> UExpression raw_address false . 
Parameter _on_bounced : TvmCell -> TvmSlice -> UExpression uint true . 
Parameter getWalletCodeHash : UExpression uint256 false . 
Parameter _fallback : TvmCell -> TvmSlice -> UExpression uint false . 
Parameter optional_owner : raw_address -> UExpression (optional raw_address) false . 
Parameter workchain_id : UExpression uint8 false . 
Parameter calc_wallet_init : uint256 -> raw_address -> UExpression ( StateInitLRecord # raw_address ) false . 
Parameter is_internal_owner : UExpression boolean false . 
Parameter check_internal_owner : UExpression PhantomType true . 
Parameter check_external_owner : boolean -> UExpression PhantomType true . 
Parameter check_owner : boolean -> UExpression PhantomType false . 
Parameter prepare_root_state_init_and_addr : TvmCell -> ContractLRecord -> UExpression ( StateInitLRecord # uint256 ) false . 


End SpecSig.

End Spec.  