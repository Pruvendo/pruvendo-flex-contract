Require Import FinProof.Common. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

(* Module Export ClassTypesModuleForFuncSig := ClassTypes xt sm. *)
Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.
 
Parameter constructor : ( XInteger256 ) -> ( XString ) -> ( XMaybe XAddress ) -> ( TonsConfigLRecord ) -> ( XInteger8 ) -> ( ListingConfigLRecord ) -> UExpression PhantomType true . 
 Parameter setSpecificCode : ( XInteger8 ) -> ( XCell ) -> UExpression PhantomType false . 
 Parameter setPairCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setXchgPairCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setWrapperCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setPriceCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setXchgPriceCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setExtWalletCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setFlexWalletCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter transfer : ( XAddress ) -> ( XInteger128 ) -> UExpression PhantomType true . 
 Parameter registerTradingPair : ( XInteger256 ) -> ( XAddress ) -> ( XInteger128 ) -> ( XAddress ) -> UExpression XAddress true . 
 Parameter approveTradingPair : ( XInteger256 ) -> UExpression XAddress true . 
 Parameter rejectTradingPair : ( XInteger256 ) -> UExpression XBool true . 
 Parameter registerXchgPair : ( XInteger256 ) -> ( XAddress ) -> ( XAddress ) -> ( XInteger128 ) -> ( XAddress ) -> UExpression XAddress true . 
 Parameter approveXchgPair : ( XInteger256 ) -> UExpression XAddress true . 
 Parameter rejectXchgPair : ( XInteger256 ) -> UExpression XBool true . 
 Parameter registerWrapper : ( XInteger256 ) -> ( Tip3ConfigLRecord ) -> UExpression XAddress true . 
 Parameter approveWrapper : ( XInteger256 ) -> UExpression XAddress true . 
 Parameter rejectWrapper : ( XInteger256 ) -> UExpression XBool true . 
 Parameter isFullyInitialized : UExpression XBool false . 
 Parameter getDetails : UExpression FlexDetailsLRecord false . 
 Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
 Parameter getListingCfg : UExpression ListingConfigLRecord false . 
 Parameter getTradingPairCode : UExpression XCell false . 
 Parameter getXchgPairCode : UExpression XCell false . 
 Parameter getSellPriceCode : ( XAddress ) -> UExpression XCell true . 
 Parameter getXchgPriceCode : ( XAddress ) -> ( XAddress ) -> UExpression XCell true . 
 Parameter getSellTradingPair : ( XAddress ) -> UExpression XAddress false . 
 Parameter getXchgTradingPair : ( XAddress ) -> ( XAddress ) -> UExpression XAddress false . 
 Parameter getDealsLimit : UExpression XInteger8 false . 
 Parameter getOwnershipInfo : UExpression FlexOwnershipInfoLRecord false .
 Parameter getWrapperListingRequests : UExpression ( XHMap XInteger WrapperListingRequestWithPubkeyLRecord) false .
 Parameter getTradingPairListingRequests : UExpression ( XHMap XInteger TradingPairListingRequestWithPubkeyLRecord) false . 
 Parameter getXchgPairListingRequests : UExpression ( XHMap XInteger XchgPairListingRequestWithPubkeyLRecord) false . 
 Parameter check_owner : UExpression PhantomType true . 
 Parameter _fallback : ( XCell ) -> ( XSlice ) -> UExpression XInteger false . 
 Parameter prepare_wrapper_state_init_and_addr : ( XCell ) -> ( DWrapperLRecord ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 
 Parameter prepare_flex_state_init_and_addr : ( ContractLRecord ) -> ( XCell ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 
 Parameter prepare_external_wallet_state_init_and_addr : ( XString ) -> ( XString ) -> ( XInteger8 ) -> ( XInteger256 ) -> ( XInteger256 ) -> ( XAddress ) -> ( XMaybe XAddress ) -> ( XCell ) -> ( XInteger8 ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 
 Parameter prepare_internal_wallet_state_init_and_addr : ( XString ) -> ( XString ) -> ( XInteger8 ) -> ( XInteger256 ) -> ( XInteger256 ) -> ( XAddress ) -> ( XMaybe XAddress ) -> ( XCell ) -> ( XInteger8 ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 
 Parameter prepare_trading_pair_state_init_and_addr : ( DTradingPairLRecord ) -> ( XCell ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 
 Parameter prepare_trading_pair : ( XAddress ) -> ( XAddress ) -> ( XCell ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 
 Parameter prepare_xchg_pair_state_init_and_addr : ( DXchgPairLRecord ) -> ( XCell ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 
 Parameter approveTradingPairImpl : ( XInteger256 ) -> (XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord)) -> ( XCell ) -> ( XInteger8 ) -> ( ListingConfigLRecord ) -> UExpression ( XAddress * (XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord) ) ) true .
 Parameter rejectTradingPairImpl : ( XInteger256 ) -> (XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord) ) -> ( ListingConfigLRecord ) -> UExpression ( XHMap XInteger256 (XInteger256 * TradingPairListingRequestLRecord) ) true . 
 Parameter approveXchgPairImpl : ( XInteger256 ) -> ( XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord) ) -> ( XCell ) -> ( XInteger8 ) -> ( ListingConfigLRecord ) -> UExpression ( XAddress * (XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord) ) ) true . 
 Parameter rejectXchgPairImpl : ( XInteger256 ) -> ( XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord) ) -> ( ListingConfigLRecord ) -> UExpression ( XHMap XInteger256 (XInteger256 * XchgPairListingRequestLRecord) ) true . 
 Parameter approveWrapperImpl : ( XInteger256 ) -> ( XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) -> ( XCell ) -> ( XCell ) -> ( XCell ) -> ( XInteger8 ) -> ( ListingConfigLRecord ) -> UExpression ( XAddress * (XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) ) true . 
 Parameter rejectWrapperImpl : ( XInteger256 ) -> ( XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) -> ( ListingConfigLRecord ) -> UExpression ( XHMap XInteger256 (XInteger256 * WrapperListingRequestLRecord) ) true . 


End SpecSig.

End Spec.  



