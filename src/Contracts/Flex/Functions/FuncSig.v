Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger .

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module Export ClassTypesForFuncSig := ClassTypes xt sm .
Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig.
(*ничего не импортируем после этой строчки*)

Module Type SpecSig.

 Parameter Flex_Ф_constructor : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XAddress -> UExpression PhantomType false . 
 Parameter Flex_Ф_setPairCode : XCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_setXchgPairCode : XCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_setPriceCode : XCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_setXchgPriceCode : XCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_isFullyInitialized : UExpression XBool false . 
 Parameter Flex_Ф_getTonsCfg : UExpression TonsConfigStateLRecord false . 
 Parameter Flex_Ф_getTradingPairCode : UExpression XCell false . 
 Parameter Flex_Ф_getXchgPairCode : UExpression XCell false . 
 Parameter Flex_Ф_getSellPriceCode : XAddress -> UExpression XCell true . 
 Parameter Flex_Ф_getXchgPriceCode : XAddress -> XAddress -> UExpression XCell true . 
 Parameter Flex_Ф_getSellTradingPair : XAddress -> UExpression XAddress false . 
 Parameter Flex_Ф_getXchgTradingPair : XAddress -> XAddress -> UExpression XAddress false . 
 Parameter Flex_Ф_getDealsLimit : UExpression XInteger8 false . 
 Parameter Flex_Ф_getNotifyAddr : UExpression XAddress false . 
 Parameter Flex_Ф__fallback : XCell -> UExpression XInteger false . 

End SpecSig.


End Spec.  