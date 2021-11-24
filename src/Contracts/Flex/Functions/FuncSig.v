Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import CommonNotations.
Require Import Contracts.Flex.ClassTypesNotations.
Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

(* Module Export ClassTypesModuleForFuncSig := ClassTypes xt sm. *)
Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Parameter constructor : ( uint256 ) -> ( XString ) -> ( XMaybe XAddress ) -> ( TonsConfigLRecord ) -> ( uint8 ) -> ( ListingConfigLRecord ) -> UExpression PhantomType true . 
 Parameter setSpecificCode : ( uint8 ) -> ( XCell ) -> UExpression PhantomType false . 
 Parameter setPairCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setXchgPairCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setWrapperCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setPriceCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setXchgPriceCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setExtWalletCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter setFlexWalletCode : ( XCell ) -> UExpression PhantomType true . 
 Parameter transfer : ( XAddress ) -> ( uint128 ) -> UExpression PhantomType true . 
 Parameter registerTradingPair : ( uint256 ) -> ( XAddress ) -> ( uint128 ) -> ( XAddress ) -> UExpression XAddress true . 
 Parameter approveTradingPair : ( uint256 ) -> UExpression XAddress true . 
 Parameter rejectTradingPair : ( uint256 ) -> UExpression XBool true . 
 Parameter registerXchgPair : ( uint256 ) -> ( XAddress ) -> ( XAddress ) -> ( uint128 ) -> ( XAddress ) -> UExpression XAddress true . 
 Parameter approveXchgPair : ( uint256 ) -> UExpression XAddress true . 
 Parameter rejectXchgPair : ( uint256 ) -> UExpression XBool true . 
 Parameter registerWrapper : ( uint256 ) -> ( Tip3ConfigLRecord ) -> UExpression XAddress true . 
 Parameter approveWrapper : ( uint256 ) -> UExpression XAddress true . 
 Parameter rejectWrapper : ( uint256 ) -> UExpression XBool true . 
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
 Parameter getDealsLimit : UExpression uint8 false . 
 Parameter getOwnershipInfo : UExpression FlexOwnershipInfoLRecord false .
 Parameter getWrapperListingRequests : UExpression ( XHMap uint WrapperListingRequestWithPubkeyLRecord) false .
 Parameter getTradingPairListingRequests : UExpression ( XHMap uint TradingPairListingRequestWithPubkeyLRecord) false . 
 Parameter getXchgPairListingRequests : UExpression ( XHMap uint XchgPairListingRequestWithPubkeyLRecord) false . 
 Parameter check_owner : UExpression PhantomType true . 
 Parameter _fallback : ( XCell ) -> ( XSlice ) -> UExpression uint false . 
 Parameter prepare_wrapper_state_init_and_addr : ( XCell ) -> ( DWrapperLRecord ) -> UExpression ( StateInitLRecord * uint256 ) false . 
 Parameter prepare_flex_state_init_and_addr : ( ContractLRecord ) -> ( XCell ) -> UExpression ( StateInitLRecord * uint256 ) false . 
 Parameter prepare_external_wallet_state_init_and_addr : ( XString ) -> ( XString ) -> ( uint8 ) -> ( uint256 ) -> ( uint256 ) -> ( XAddress ) -> ( XMaybe XAddress ) -> ( XCell ) -> ( uint8 ) -> UExpression ( StateInitLRecord * uint256 ) false . 
 Parameter prepare_internal_wallet_state_init_and_addr : ( XString ) -> ( XString ) -> ( uint8 ) -> ( uint256 ) -> ( uint256 ) -> ( XAddress ) -> ( XMaybe XAddress ) -> ( XCell ) -> ( uint8 ) -> UExpression ( StateInitLRecord * uint256 ) false . 
 Parameter prepare_trading_pair_state_init_and_addr : ( DTradingPairLRecord ) -> ( XCell ) -> UExpression ( StateInitLRecord * uint256 ) false . 
 Parameter prepare_trading_pair : ( XAddress ) -> ( XAddress ) -> ( XCell ) -> UExpression ( StateInitLRecord * uint256 ) false . 
 Parameter prepare_xchg_pair_state_init_and_addr : ( DXchgPairLRecord ) -> ( XCell ) -> UExpression ( StateInitLRecord * uint256 ) false . 
 Parameter approveTradingPairImpl : ( uint256 ) -> (XHMap uint256 (uint256 * TradingPairListingRequestLRecord)) -> ( XCell ) -> ( uint8 ) -> ( ListingConfigLRecord ) -> UExpression ( XAddress * (XHMap uint256 (uint256 * TradingPairListingRequestLRecord) ) ) true .
 Parameter rejectTradingPairImpl : ( uint256 ) -> (XHMap uint256 (uint256 * TradingPairListingRequestLRecord) ) -> ( ListingConfigLRecord ) -> UExpression ( XHMap uint256 (uint256 * TradingPairListingRequestLRecord) ) true . 
 Parameter approveXchgPairImpl : ( uint256 ) -> ( XHMap uint256 (uint256 * XchgPairListingRequestLRecord) ) -> ( XCell ) -> ( uint8 ) -> ( ListingConfigLRecord ) -> UExpression ( XAddress * (XHMap uint256 (uint256 * XchgPairListingRequestLRecord) ) ) true . 
 Parameter rejectXchgPairImpl : ( uint256 ) -> ( XHMap uint256 (uint256 * XchgPairListingRequestLRecord) ) -> ( ListingConfigLRecord ) -> UExpression ( XHMap uint256 (uint256 * XchgPairListingRequestLRecord) ) true . 
 Parameter approveWrapperImpl : ( uint256 ) -> ( XHMap uint256 (uint256 * WrapperListingRequestLRecord) ) -> ( XCell ) -> ( XCell ) -> ( XCell ) -> ( uint8 ) -> ( ListingConfigLRecord ) -> UExpression ( XAddress * (XHMap uint256 (uint256 * WrapperListingRequestLRecord) ) ) true . 
 Parameter rejectWrapperImpl : ( uint256 ) -> ( XHMap uint256 (uint256 * WrapperListingRequestLRecord) ) -> ( ListingConfigLRecord ) -> UExpression ( XHMap uint256 (uint256 * WrapperListingRequestLRecord) ) true . 


End SpecSig.

End Spec.  



