Require Import FinProof.Common. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.PriceXchg.ClassTypes.
Require Import Contracts.PriceXchg.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.

Local Open Scope ursus_scope.

Parameter make_deal : ( (ULValue OrderInfoXchgLRecord ) ) -> ( (ULValue OrderInfoXchgLRecord ) ) -> UExpression ( XBool # (XBool # XInteger128) ) false . 
 Parameter extract_active_order : ( ULValue( XMaybe (XInteger # OrderInfoXchgLRecord ) )) -> 
                                  ( ULValue( ( XQueue OrderInfoXchgLRecord ) )) -> 
                                  ( ULValue ( XInteger128 ) )) -> 
                                            ( ( XBool ) ) -> 
UExpression ( (XMaybe ( XInteger # OrderInfoXchgLRecord )) # ( (XQueue OrderInfoXchgLRecord) # XInteger128 ) ) false . 


 Parameter process_queue : ( ( XInteger ) ) -> ( ( XInteger ) ) -> UExpression PhantomType false . 
 Parameter onTip3LendOwnership : ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger32 ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XCell ) ) -> UExpression OrderRetLRecord false . 
 Parameter processQueue : UExpression PhantomType false . 
 Parameter cancelSell : UExpression PhantomType false . 
 Parameter cancelBuy : UExpression PhantomType false . 
 Parameter getDetails : UExpression DetailsInfoXchgLRecord false . 
 Parameter getPriceNum : UExpression XInteger128 false . 
 Parameter getPriceDenum : UExpression XInteger128 false . 
 Parameter getMinimumAmount : UExpression XInteger128 false . 
 Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
 Parameter getSells : UExpression ( XHMap XInteger OrderInfoXchgLRecord ) false . 
 Parameter getBuys : UExpression ( XHMap XInteger OrderInfoXchgLRecord ) false . 
 Parameter getSellAmount : UExpression XInteger128 false . 
 Parameter getBuyAmount : UExpression XInteger128 false . 
 Parameter _fallback : ( XCell ) -> ( XSlice ) -> UExpression XInteger false . 
 Parameter onTip3LendOwnershipMinValue : UExpression XInteger128 false . 
 Parameter verify_tip3_addr : ( ( Tip3ConfigLRecord ) ) -> ( ( XAddress ) ) -> ( ( XInteger256 ) ) -> ( ( XInteger256 ) ) -> UExpression XBool false . 
 Parameter expected_wallet_address : ( ( Tip3ConfigLRecord ) ) -> ( ( XInteger256 ) ) -> ( ( XInteger256 ) ) -> UExpression XInteger256 false . 
 Parameter on_ord_fail : ( ( XInteger ) ) -> ( ( XAddress (* ITONTokenWalletPtrLRecord *) ) ) -> ( ( XInteger128 ) ) -> UExpression OrderRetLRecord false . 
 Parameter numerator : UExpression XInteger128 false . 
 Parameter denominator : UExpression XInteger128 false .
 Parameter prepare_price_xchg_state_init_and_addr : ( ( ContractLRecord ) ) -> ( ( XCell ) ) -> UExpression ( StateInitLRecord # XInteger256 ) false . 
 Parameter is_active_time : ( ( XInteger32 ) ) -> UExpression XBool false . 
 Parameter minor_cost : ( ( XInteger128 ) ) -> ( ( RationalPriceLRecord ) ) -> UExpression (XMaybe XInteger128) false . 
 Parameter process_queue_impl : ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XAddress (* IFlexNotifyPtrLRecord *) ) ) -> ( ( RationalPriceLRecord ) ) -> ( ( XInteger8 ) ) -> ( ( TonsConfigLRecord ) ) -> ( ( XInteger ) ) -> ( ( XInteger ) ) -> ( ( XInteger128 ) ) -> ( ( XQueue OrderInfoXchgLRecord ) ) -> ( ( XInteger128 ) ) -> ( ( XQueue OrderInfoXchgLRecord ) ) -> UExpression process_retLRecord false . 
 Parameter cancel_order_impl : ( ( XQueue OrderInfoXchgLRecord ) ) -> ( ( addr_std_fixedLRecord ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> ( ( XInteger (* Grams *) ) ) -> ( ( XInteger (* Grams *) ) ) -> ( ( XInteger (* Grams *) ) ) -> UExpression (XQueue OrderInfoXchgLRecord) false . 
 Parameter int_sender_and_value : UExpression ( XAddress # XInteger (* Grams *) ) false . 

End SpecSig.

End Spec.  