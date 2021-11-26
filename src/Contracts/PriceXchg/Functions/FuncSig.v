Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import CommonNotations.
Require Import Contracts.PriceXchg.ClassTypes.
Require Import Contracts.PriceXchg.Ledger.
Require Import Contracts.PriceXchg.ClassTypesNotations.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 
(* Module Export stdTypesNotationsModule := stdTypesNotations xt sm LedgerModuleForFuncSig. *)
Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Parameter make_deal : ( (ULValue OrderInfoXchgLRecord ) ) -> ( (ULValue OrderInfoXchgLRecord ) ) -> UExpression ( XBool # (XBool # uint128) ) false . 
 Parameter extract_active_order : ( ULValue( XMaybe (uint # OrderInfoXchgLRecord ) )) -> 
                                  ( ULValue( ( XQueue OrderInfoXchgLRecord ) )) -> 
                                  ( ULValue ( uint128 ) ) -> 
                                            ( ( XBool ) ) -> 
UExpression ( (XMaybe ( uint # OrderInfoXchgLRecord )) # ( (XQueue OrderInfoXchgLRecord) # uint128 ) ) true . 


 Parameter process_queue : ( ( uint ) ) -> ( ( uint ) ) -> UExpression PhantomType true . 
 Parameter onTip3LendOwnership : ( ( XAddress ) ) -> ( ( uint128 ) ) -> ( ( uint32 ) ) -> ( ( uint256 ) ) -> ( ( XAddress ) ) -> ( ( XCell ) ) -> UExpression OrderRetLRecord false . 
 Parameter processQueue : UExpression PhantomType false . 
 Parameter cancelSell : UExpression PhantomType false . 
 Parameter cancelBuy : UExpression PhantomType false . 
 Parameter getDetails : UExpression DetailsInfoXchgLRecord false . 
 Parameter getPriceNum : UExpression uint128 false . 
 Parameter getPriceDenum : UExpression uint128 false . 
 Parameter getMinimumAmount : UExpression uint128 false . 
 Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
 Parameter getSells : UExpression ( XHMap uint OrderInfoXchgLRecord ) false . 
 Parameter getBuys : UExpression ( XHMap uint OrderInfoXchgLRecord ) false . 
 Parameter getSellAmount : UExpression uint128 false . 
 Parameter getBuyAmount : UExpression uint128 false . 
 Parameter _fallback : ( XCell ) -> ( XSlice ) -> UExpression uint false . 
 Parameter onTip3LendOwnershipMinValue : UExpression uint128 false . 
 Parameter verify_tip3_addr : ( ( Tip3ConfigLRecord ) ) -> ( ( XAddress ) ) -> ( ( uint256 ) ) -> ( ( uint256 ) ) -> UExpression XBool false . 
 Parameter expected_wallet_address : ( ( Tip3ConfigLRecord ) ) -> ( ( uint256 ) ) -> ( ( uint256 ) ) -> UExpression uint256 false . 
 Parameter on_ord_fail : ( ( uint ) ) -> ( ( XAddress (* ITONTokenWalletPtrLRecord *) ) ) -> ( ( uint128 ) ) -> UExpression OrderRetLRecord false . 
 Parameter prepare_price_xchg_state_init_and_addr : ( ( ContractLRecord ) ) -> ( ( XCell ) ) -> UExpression ( StateInitLRecord # uint256 ) false . 
 Parameter is_active_time : ( ( uint32 ) ) -> UExpression XBool false . 
 Parameter minor_cost : ( ( uint128 ) ) -> ( ( RationalPriceLRecord ) ) -> UExpression (XMaybe uint128) false . 
 Parameter process_queue_impl : ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XAddress (* IFlexNotifyPtrLRecord *) ) ) -> ( ( RationalPriceLRecord ) ) -> ( ( uint8 ) ) -> ( ( TonsConfigLRecord ) ) -> ( ( uint ) ) -> ( ( uint ) ) -> ( ( uint128 ) ) -> ( ( XQueue OrderInfoXchgLRecord ) ) -> ( ( uint128 ) ) -> ( ( XQueue OrderInfoXchgLRecord ) ) -> UExpression process_retLRecord false . 
 Parameter cancel_order_impl : ( ( XQueue OrderInfoXchgLRecord ) ) -> ( ( addr_std_fixedLRecord ) ) -> ( ( uint128 ) ) -> ( ( XBool ) ) -> ( ( uint (* Grams *) ) ) -> ( ( uint (* Grams *) ) ) -> ( ( uint (* Grams *) ) ) -> UExpression ((XQueue OrderInfoXchgLRecord) # uint128) false . 
 Parameter int_sender_and_value : UExpression ( XAddress # uint (* Grams *) ) false . 

End SpecSig.

End Spec.  