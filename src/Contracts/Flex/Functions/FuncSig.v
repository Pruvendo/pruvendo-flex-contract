Require Import FinProof.Common. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module Export ClassTypesModuleForFuncSig := ClassTypes xt sm.
Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.
 
Parameter constructor : URValue ( XInteger256 ) false -> URValue ( XString ) false -> URValue ( XMaybe XAddress ) false -> URValue ( TonsConfigLRecord ) false -> URValue ( XInteger8 ) false -> URValue ( ListingConfigLRecord ) false -> UExpression PhantomType true . 
 Parameter setSpecificCode : URValue ( XInteger8 ) false -> URValue ( XCell ) false -> UExpression PhantomType false . 
 Parameter setPairCode : URValue ( XCell ) false -> UExpression PhantomType true . 
 Parameter setXchgPairCode : URValue ( XCell ) false -> UExpression PhantomType true . 
 Parameter setWrapperCode : URValue ( XCell ) false -> UExpression PhantomType true . 
 Parameter setPriceCode : URValue ( XCell ) false -> UExpression PhantomType true . 
 Parameter setXchgPriceCode : URValue ( XCell ) false -> UExpression PhantomType true . 
 Parameter setExtWalletCode : URValue ( XCell ) false -> UExpression PhantomType true . 
 Parameter setFlexWalletCode : URValue ( XCell ) false -> UExpression PhantomType true . 
 Parameter transfer : URValue ( XAddress ) false -> URValue ( XInteger128 ) false -> UExpression PhantomType false . 
 Parameter registerTradingPair : URValue ( XInteger256 ) false -> URValue ( XAddress ) false -> URValue ( XInteger128 ) false -> URValue ( XAddress ) false -> UExpression XAddress true . 
 Parameter approveTradingPair : URValue ( XInteger256 ) false -> UExpression XAddress false . 
 Parameter rejectTradingPair : URValue ( XInteger256 ) false -> UExpression XBool false . 
 Parameter registerXchgPair : URValue ( XInteger256 ) false -> URValue ( XAddress ) false -> URValue ( XAddress ) false -> URValue ( XInteger128 ) false -> URValue ( XAddress ) false -> UExpression XAddress true . 
 Parameter approveXchgPair : URValue ( XInteger256 ) false -> UExpression XAddress false . 
 Parameter rejectXchgPair : URValue ( XInteger256 ) false -> UExpression XBool false . 
 Parameter registerWrapper : URValue ( XInteger256 ) false -> URValue ( Tip3ConfigLRecord ) false -> UExpression XAddress true . 
 Parameter approveWrapper : URValue ( XInteger256 ) false -> UExpression XAddress false . 
 Parameter rejectWrapper : URValue ( XInteger256 ) false -> UExpression XBool false . 
 Parameter isFullyInitialized : UExpression XBool false . 
 Parameter getDetails : UExpression FlexDetailsLRecord false . 
 Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
 Parameter getListingCfg : UExpression ListingConfigLRecord false . 
 Parameter getTradingPairCode : UExpression XCell false . 
 Parameter getXchgPairCode : UExpression XCell false . 
 Parameter getSellPriceCode : URValue ( XAddress ) false -> UExpression XCell true . 
 Parameter getXchgPriceCode : URValue ( XAddress ) false -> URValue ( XAddress ) false -> UExpression XCell true . 
 Parameter getSellTradingPair : URValue ( XAddress ) false -> UExpression XAddress false . 
 Parameter getXchgTradingPair : URValue ( XAddress ) false -> URValue ( XAddress ) false -> UExpression XAddress false . 
 Parameter getDealsLimit : UExpression XInteger8 false . 
 Parameter getOwnershipInfo : UExpression FlexOwnershipInfoLRecord false .
 Parameter getWrapperListingRequests : UExpression ( XHMap XInteger WrapperListingRequestWithPubkeyLRecord) false .
 Parameter getTradingPairListingRequests : UExpression ( XHMap XInteger TradingPairListingRequestWithPubkeyLRecord) false . 
 Parameter getXchgPairListingRequests : UExpression ( XHMap XInteger XchgPairListingRequestWithPubkeyLRecord) false . 
 Parameter check_owner : UExpression PhantomType true . 
 Parameter _fallback : URValue ( XCell ) false -> URValue ( XSlice ) false -> UExpression XInteger false . 
 Parameter prepare_wrapper_state_init_and_addr : URValue ( XCell ) false -> URValue ( DWrapperLRecord ) false -> UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 Parameter prepare_flex_state_init_and_addr : URValue ( ContractLRecord ) false -> URValue ( XCell ) false -> UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 Parameter prepare_external_wallet_state_init_and_addr : URValue ( XString ) false -> URValue ( XString ) false -> URValue ( XInteger8 ) false -> URValue ( XInteger256 ) false -> URValue ( XInteger256 ) false -> URValue ( XAddress ) false -> URValue ( XMaybe XAddress ) false -> URValue ( XCell ) false -> URValue ( XInteger8 ) false -> UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 Parameter prepare_internal_wallet_state_init_and_addr : URValue ( XString ) false -> URValue ( XString ) false -> URValue ( XInteger8 ) false -> URValue ( XInteger256 ) false -> URValue ( XInteger256 ) false -> URValue ( XAddress ) false -> URValue ( XMaybe XAddress ) false -> URValue ( XCell ) false -> URValue ( XInteger8 ) false -> UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 Parameter prepare_trading_pair_state_init_and_addr : URValue ( DTradingPairLRecord ) false -> URValue ( XCell ) false -> UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 Parameter prepare_trading_pair : URValue ( XAddress ) false -> URValue ( XAddress ) false -> URValue ( XCell ) false -> UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 Parameter prepare_xchg_pair_state_init_and_addr : URValue ( DXchgPairLRecord ) false -> URValue ( XCell ) false -> UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 Parameter approveTradingPairImpl : URValue ( XInteger256 ) false -> URValue ( XHMap XInteger256 TradingPairListingRequestLRecord ) false -> URValue ( XCell ) false -> URValue ( XInteger8 ) false -> URValue ( ListingConfigLRecord ) false -> UExpression ( XHMap XInteger256 TradingPairListingRequestLRecord ) true . 
 Parameter rejectTradingPairImpl : URValue ( XInteger256 ) false -> URValue ( XHMap XInteger256 TradingPairListingRequestLRecord ) false -> URValue ( ListingConfigLRecord ) false -> UExpression ( XHMap XInteger TradingPairListingRequestLRecord) true . 
 Parameter approveXchgPairImpl : URValue ( XInteger256 ) false -> URValue ( XHMap XInteger256  XchgPairListingRequestLRecord ) false -> URValue ( XCell ) false -> URValue ( XInteger8 ) false -> URValue ( ListingConfigLRecord ) false -> UExpression ( XHMap XInteger XchgPairListingRequestLRecord ) true . 
 Parameter rejectXchgPairImpl : URValue ( XInteger256 ) false -> URValue ( XHMap XInteger256  XchgPairListingRequestLRecord ) false -> URValue ( ListingConfigLRecord ) false -> UExpression ( XHMap XInteger XchgPairListingRequestLRecord ) true . 
 Parameter approveWrapperImpl : URValue ( XInteger256 ) false -> URValue ( XHMap XInteger256 WrapperListingRequestLRecord ) false -> URValue ( XCell ) false -> URValue ( XCell ) false -> URValue ( XCell ) false -> URValue ( XInteger8 ) false -> URValue ( ListingConfigLRecord ) false -> UExpression ( XHMap XInteger WrapperListingRequestLRecord ) true . 
 Parameter rejectWrapperImpl : URValue ( XInteger256 ) false -> URValue (  XHMap XInteger256 WrapperListingRequestLRecord ) false -> URValue ( ListingConfigLRecord ) false -> UExpression ( XHMap XInteger WrapperListingRequestLRecord) true . 


End SpecSig.

End Spec.  



