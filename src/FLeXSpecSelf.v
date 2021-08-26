Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG25.

Require Import classFlex.
Require Import stdFunc.
Require Import stdFuncNotations.

Module specFlexSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export LedgerClassModule := LedgerClass xt sm . 
Module Export stdFuncNotationsModule := stdFuncNotations xt sm LedgerClassModule.

Module Type specFLeXSig.
(* Import xt. Import sm. *)

Parameter Ф_prepare_trading_pair_state_init_and_addr : StateInit -> XInteger256 -> UExpression ( TradingPair # TvmCell )%sol false . 
Parameter Ф_prepare_xchg_pair_state_init_and_addr : StateInit -> XInteger256 -> UExpression ( XchgPair # TvmCell )%sol false . 
Parameter FLeX_Ф_constructor : XInteger256 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger128 -> XInteger8 -> XAddress -> UExpression PhantomType false . 
Parameter FLeX_Ф_setPairCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_setXchgPairCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_setPriceCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_setXchgPriceCode : TvmCell -> UExpression PhantomType false . 
Parameter FLeX_Ф_isFullyInitialized : UExpression XBool false . 
Parameter FLeX_Ф_getTonsCfg : UExpression TonsConfig false . 
Parameter FLeX_Ф_getTradingPairCode : UExpression TvmCell false .
Parameter FLeX_Ф_getXchgPairCode : UExpression TvmCell false . 
Parameter FLeX_Ф_getSellPriceCode : XAddress -> UExpression TvmCell false . 
Parameter FLeX_Ф_getXchgPriceCode : XAddress -> XAddress -> UExpression TvmCell false . 
Parameter FLeX_Ф_getSellTradingPair : XAddress -> UExpression XAddress false . 
Parameter FLeX_Ф_getXchgTradingPair : XAddress -> XAddress -> UExpression XAddress false . 
Parameter FLeX_Ф_getMinAmount : UExpression XInteger128 false . 
Parameter FLeX_Ф_getDealsLimit : UExpression XInteger8 false . 
Parameter FLeX_Ф_getNotifyAddr : UExpression XAddress false . 
Parameter FLeX_Ф__fallback : UExpression XInteger false . 

End specFLeXSig.

End specFlexSpec.
