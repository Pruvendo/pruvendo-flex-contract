Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG26.

Require Import PriceClass.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdFuncNotations.
Require Import UrsusStdLib.stdNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Module specPriceSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export LedgerClassModule := LedgerPriceClass xt sm . 

Module Export tvmNotationsModule := tvmNotations xt sm LedgerClassModule.

Module Type specPriceSig.

Parameter Ф_calc_cost : XInteger128 -> XInteger128 -> UExpression ( XMaybe XInteger128 ) false . 
 Parameter dealer_Ф_make_deal : OrderInfo -> OrderInfo -> UExpression ( XBool # XBool # XInteger128 )%sol false . 
 Parameter Ф_is_active_time : XInteger32 -> UExpression XBool false . 
 Parameter dealer_Ф_extract_active_order : ( XMaybe (XInteger # OrderInfo)%sol ) -> XList OrderInfo -> XInteger128 -> XBool -> UExpression ( ( XMaybe (XInteger # OrderInfo)%sol ) # (XList OrderInfo) # XInteger128 )%sol false . 
 Parameter Price_Ф_processQueue : UExpression PhantomType false . 
 Parameter dealer_Ф_process_queue : XInteger -> XInteger -> UExpression PhantomType false . 
 Parameter Price_Ф_onTip3LendOwnershipMinValue : UExpression XInteger128 false . 
 Parameter Price_Ф_expected_wallet_address : XInteger256 -> XInteger256 -> UExpression XInteger256 false . 
 Parameter Price_Ф_verify_tip3_addr : XAddress -> XInteger256 -> XInteger256 -> UExpression XBool false . 
 Parameter Price_Ф_on_sell_fail : XInteger -> ITONTokenWalletPtr -> UExpression OrderRet false . 
 Parameter Price_Ф_onTip3LendOwnership : XAddress -> XInteger128 -> XInteger32 -> XInteger256 -> XAddress -> TvmCell -> UExpression OrderRet false . 
 Parameter Price_Ф_buyTip3MinValue : XInteger128 -> UExpression XInteger128 false . 
 Parameter Price_Ф_buyTip3 : XInteger128 -> XAddress -> XInteger32 -> UExpression OrderRet true . 
 Parameter Ф_cancel_order_impl : XList OrderInfo -> addr_std_fixed -> XInteger128 -> XBool -> Grams -> Grams -> Grams -> UExpression ( XList OrderInfo ) false . 
 Parameter Price_Ф_cancelSell : UExpression PhantomType false . 
 Parameter Price_Ф_cancelBuy : UExpression PhantomType false . 
 Parameter Price_Ф_getPrice : UExpression XInteger128 false . 
 Parameter Price_Ф_getMinimumAmount : UExpression XInteger128 false . 
 Parameter Price_Ф_getSellAmount : UExpression XInteger128 false . 
 Parameter Price_Ф_getBuyAmount : UExpression XInteger128 false . 
 Parameter Price_Ф_getDetails : UExpression DetailsInfo false . 
 Parameter Price_Ф_getTonsCfg : UExpression TonsConfig false . 
 Parameter Price_Ф_getSells : UExpression ( XHMap XInteger OrderInfo) false . 
 Parameter Price_Ф_getBuys : UExpression ( XHMap XInteger OrderInfo) false . 
 Parameter Price_Ф__fallback : TvmCell -> UExpression XInteger false . 

End specPriceSig.

End specPriceSpec.

