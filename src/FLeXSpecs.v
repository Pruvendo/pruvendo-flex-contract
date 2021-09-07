Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG26.

Require Import FLeXClass.

Require Import UrsusStdLib.stdFunc.
Require Import UrsusStdLib.stdFuncNotations.
Require Import UrsusStdLib.stdNotations.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Module specFlexSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export LedgerClassModule := LedgerClass xt sm . 

Module Export tvmNotationsModule := tvmNotations xt sm LedgerClassModule.

Module Type specFLeXSig.



Parameter Flex_Ф_constructor : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XAddress -> UExpression PhantomType false . 
 Parameter Flex_Ф_setPairCode : TvmCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_setXchgPairCode : TvmCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_setPriceCode : TvmCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_setXchgPriceCode : TvmCell -> UExpression PhantomType true . 
 Parameter Flex_Ф_isFullyInitialized : UExpression XBool false . 
 Parameter Flex_Ф_getTonsCfg : UExpression TonsConfig false . 
 Parameter Flex_Ф_getTradingPairCode : UExpression TvmCell false . 
 Parameter Flex_Ф_getXchgPairCode : UExpression TvmCell false . 
 Parameter Flex_Ф_getSellPriceCode : XAddress -> UExpression TvmCell true . 
 Parameter Flex_Ф_getXchgPriceCode : XAddress -> XAddress -> UExpression TvmCell true . 
 Parameter Flex_Ф_getSellTradingPair : XAddress -> UExpression XAddress false . 
 Parameter Flex_Ф_getXchgTradingPair : XAddress -> XAddress -> UExpression XAddress false . 
 Parameter Flex_Ф_getDealsLimit : UExpression XInteger8 false . 
 Parameter Flex_Ф_getNotifyAddr : UExpression XAddress false . 
 Parameter Flex_Ф__fallback : UExpression XInteger false -> UExpression XInteger false . 


End specFLeXSig.

End specFlexSpec.