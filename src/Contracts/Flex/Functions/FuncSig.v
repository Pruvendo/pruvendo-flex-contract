Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module Export ClassTypesModuleForFuncSig := ClassTypes xt sm.
Module  LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.

Parameter constructor1 : URValue XInteger256 false -> URValue XString false -> URValue ( XMaybe XAddress) false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger128 false -> URValue XInteger8 false -> UExpression PhantomType false . 
 Parameter setPairCode : URValue XCell false -> UExpression PhantomType true . 
 Parameter setXchgPairCode : URValue XCell false -> UExpression PhantomType true . 
 Parameter setPriceCode : URValue XCell false -> UExpression PhantomType true . 
 Parameter setXchgPriceCode : URValue XCell false -> UExpression PhantomType true . 
 Parameter transfer : URValue XAddress false -> URValue XInteger128 false -> UExpression PhantomType true . 
 Parameter isFullyInitialized : UExpression XBool false . 
 Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
 Parameter getTradingPairCode : UExpression XCell false . 
 Parameter getXchgPairCode : UExpression XCell false . 
 Parameter getSellPriceCode : URValue XAddress false -> UExpression XCell true . 
 Parameter getXchgPriceCode : URValue XAddress false -> URValue XAddress false -> UExpression XCell true . 
 Parameter getSellTradingPair : URValue XAddress false -> UExpression XAddress false . 
 Parameter getXchgTradingPair : URValue XAddress false -> URValue XAddress false -> UExpression XAddress false . 
 Parameter getDealsLimit : UExpression XInteger8 false . 
 Parameter getOwnershipInfo : UExpression FlexOwnershipInfoLRecord false . 
 Parameter _fallback : URValue XCell false -> URValue XSlice false -> UExpression XInteger false . 
 Parameter prepare_flex_state_init_and_addr : URValue ContractLRecord false -> URValue XCell false -> UExpression ( StateInitLRecord # XInteger256 )%sol false . 

Locate constructor1.
End SpecSig.
Locate constructor1.
End Spec.  



