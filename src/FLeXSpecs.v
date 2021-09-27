Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.

Require Import FLeXClass.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdFuncNotations.
Require Import UrsusStdLib.stdNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Module specFlexSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export LedgerClassModule := LedgerFLeXClass xt sm . 

Module Export tvmNotationsModule := tvmNotations xt sm LedgerClassModule.

Module Type specFLeXSig.



Parameter Flex_Ф_constructor : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XAddress -> UExpression PhantomType false . 
 Parameter Flex_Ф_setPairCode : XCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_setXchgPairCode : XCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_setPriceCode : XCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_setXchgPriceCode : XCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_isFullyInitialized : UExpression XBool false . 
 Parameter Flex_Ф_getTonsCfg : UExpression TonsConfig false . 
 Parameter Flex_Ф_getTradingPairCode : UExpression XCell false . 
 Parameter Flex_Ф_getXchgPairCode : UExpression XCell false . 
 Parameter Flex_Ф_getSellPriceCode : XAddress -> UExpression XCell true . 
 Parameter Flex_Ф_getXchgPriceCode : XAddress -> XAddress -> UExpression XCell true . 
 Parameter Flex_Ф_getSellTradingPair : XAddress -> UExpression XAddress false . 
 Parameter Flex_Ф_getXchgTradingPair : XAddress -> XAddress -> UExpression XAddress false . 
 Parameter Flex_Ф_getDealsLimit : UExpression XInteger8 false . 
 Parameter Flex_Ф_getNotifyAddr : UExpression XAddress false . 
 Parameter Flex_Ф__fallback : UExpression XInteger false -> UExpression XInteger false . 


End specFLeXSig.

End specFlexSpec.