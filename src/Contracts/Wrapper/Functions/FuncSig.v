Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import CommonNotations.
Require Import Contracts.Price.ClassTypes.
Require Import Contracts.Price.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export CommonNotationsModule := CommonNotations xt sm LedgerModuleForFuncSig. 
(* Module Export stdTypesNotationsModule := stdTypesNotations xt sm LedgerModuleForFuncSig. *)
Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter make_deal : ( ( OrderInfoLRecord ) ) -> ( ( OrderInfoLRecord ) ) -> UExpression ( XBool # (XBool # uint128) ) false . 
 Parameter extract_active_order : ( XMaybe (uint # OrderInfoLRecord ) ) -> ( ( XQueue OrderInfoLRecord ) ) -> ( ( uint128 ) ) -> ( ( XBool ) ) -> UExpression ( ( XMaybe (uint # OrderInfoLRecord) ) # (( XQueue OrderInfoLRecord ) # uint128) ) false . 
 Parameter process_queue : ( ( uint ) ) -> ( ( uint ) ) -> UExpression PhantomType false . 
 Parameter onTip3LendOwnership : ( ( XAddress ) ) -> ( ( uint128 ) ) -> ( ( uint32 ) ) -> ( ( uint256 ) ) -> ( ( XAddress ) ) -> ( ( XCell ) ) -> UExpression OrderRetLRecord false . 
 Parameter buyTip3 : ( ( uint128 ) ) -> ( ( XAddress ) ) -> ( ( uint32 ) ) -> UExpression OrderRetLRecord true . 
 Parameter processQueue : UExpression PhantomType false . 
 Parameter cancelSell : UExpression PhantomType false . 
 Parameter cancelBuy : UExpression PhantomType false . 
 Parameter getDetails : UExpression DetailsInfoLRecord false . 
 Parameter getPrice : UExpression uint128 false . 
 Parameter getMinimumAmount : UExpression uint128 false . 
 Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
 Parameter getSells : UExpression ( XHMap uint OrderInfoLRecord ) false . 
 Parameter getBuys : UExpression ( XHMap uint OrderInfoLRecord ) false . 
 Parameter getSellAmount : UExpression uint128 false . 
 Parameter getBuyAmount : UExpression uint128 false . 
 Parameter _fallback : XCell -> XSlice -> UExpression uint false . 
 Parameter onTip3LendOwnershipMinValue : UExpression uint128 false . 
 Parameter buyTip3MinValue : ( ( uint128 ) ) -> UExpression uint128 false . 
 Parameter verify_tip3_addr : ( ( XAddress ) ) -> ( ( uint256 ) ) -> ( ( uint256 ) ) -> UExpression XBool false . 
 Parameter expected_wallet_address : ( ( uint256 ) ) -> ( ( uint256 ) ) -> UExpression uint256 false . 
 Parameter on_sell_fail : ( ( uint ) ) -> ( XAddress (*ITONTokenWalletPtr*) ) -> ( ( uint128 ) ) -> UExpression OrderRetLRecord false . 
 Parameter prepare_price_state_init_and_addr : ( ( ContractLRecord ) ) -> ( ( XCell ) ) -> UExpression ( StateInitLRecord # uint256 ) false . 
 Parameter is_active_time : ( ( uint32 ) ) -> UExpression XBool false . 
 Parameter calc_cost : ( ( uint128 ) ) -> ( ( uint128 ) ) -> UExpression (XMaybe uint128) false . 
 Parameter process_queue_impl : ( ( XAddress ) ) -> ( XAddress (*IFlexNotifyPtr*) ) -> ( ( uint128 ) ) -> ( ( uint8 ) ) -> ( ( TonsConfigLRecord ) ) -> ( ( uint ) ) -> ( ( uint ) ) -> ( ( uint128 ) ) -> ( ( XQueue OrderInfoLRecord ) ) -> ( ( uint128 ) ) -> ( ( XQueue OrderInfoLRecord ) ) -> UExpression process_retLRecord false . 
 Parameter cancel_order_impl : ( ( XQueue OrderInfoLRecord ) ) -> ( ( addr_std_fixedLRecord ) ) -> ( ( uint128 ) ) -> ( ( XBool ) ) -> ( uint (*Grams*) ) -> ( uint (*Grams*) ) -> ( uint (*Grams*) ) -> UExpression ((XQueue OrderInfoLRecord) # uint128) false . 


End SpecSig.

End Spec.  