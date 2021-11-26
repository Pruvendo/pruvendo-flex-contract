Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import CommonNotations.
Require Import Flex.ClassTypesNotations.
Require Import Flex.ClassTypes.
Require Import Flex.Ledger.

Require TradingPair.ClassTypes.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter constructor : uint256 -> String -> optional raw_address -> TonsConfigLRecord -> uint8 -> 
                        ListingConfigLRecord -> UExpression PhantomType true . 
Parameter setSpecificCode : uint8 -> TvmCell -> UExpression PhantomType false . 
Parameter setPairCode : TvmCell -> UExpression PhantomType true . 
Parameter setXchgPairCode : TvmCell -> UExpression PhantomType true . 
Parameter setWrapperCode : TvmCell -> UExpression PhantomType true . 
Parameter setPriceCode : TvmCell -> UExpression PhantomType true . 
Parameter setXchgPriceCode : TvmCell -> UExpression PhantomType true . 
Parameter setExtWalletCode : TvmCell -> UExpression PhantomType true . 
Parameter setFlexWalletCode : TvmCell -> UExpression PhantomType true . 
Parameter transfer : raw_address -> uint128 -> UExpression PhantomType true . 
Parameter registerTradingPair : uint256 -> raw_address -> uint128 -> raw_address -> UExpression raw_address true . 
Parameter approveTradingPair : uint256 -> UExpression raw_address true . 
Parameter rejectTradingPair : uint256 -> UExpression boolean true . 
Parameter registerXchgPair : uint256 -> raw_address -> raw_address -> uint128 -> raw_address -> UExpression raw_address true . 
Parameter approveXchgPair : uint256 -> UExpression raw_address true . 
Parameter rejectXchgPair : uint256 -> UExpression boolean true . 
Parameter registerWrapper : uint256 -> Tip3ConfigLRecord -> UExpression raw_address true . 
Parameter approveWrapper : uint256 -> UExpression raw_address true . 
Parameter rejectWrapper : uint256 -> UExpression boolean true . 
Parameter isFullyInitialized : UExpression boolean false . 
Parameter getDetails : UExpression FlexDetailsLRecord false . 
Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
Parameter getListingCfg : UExpression ListingConfigLRecord false . 
Parameter getTradingPairCode : UExpression TvmCell false . 
Parameter getXchgPairCode : UExpression TvmCell false . 
Parameter getSellPriceCode : raw_address -> UExpression TvmCell true . 
Parameter getXchgPriceCode : raw_address -> raw_address -> UExpression TvmCell true . 
Parameter getSellTradingPair : raw_address -> UExpression raw_address false . 
Parameter getXchgTradingPair : raw_address -> raw_address -> UExpression raw_address false . 
Parameter getDealsLimit : UExpression uint8 false . 
Parameter getOwnershipInfo : UExpression FlexOwnershipInfoLRecord false .
Parameter getWrapperListingRequests : UExpression ( mapping uint WrapperListingRequestWithPubkeyLRecord) false .
Parameter getTradingPairListingRequests : UExpression ( mapping uint TradingPairListingRequestWithPubkeyLRecord) false . 
Parameter getXchgPairListingRequests : UExpression ( mapping uint XchgPairListingRequestWithPubkeyLRecord) false . 
Parameter check_owner : UExpression PhantomType true . 
Parameter _fallback : TvmCell -> TvmSlice -> UExpression uint false . 
Parameter prepare_wrapper_state_init_and_addr : TvmCell -> WrapperClassTypesModule.DWrapperLRecord -> UExpression ( StateInitLRecord * uint256 ) false . 
Parameter prepare_flex_state_init_and_addr : ContractLRecord -> TvmCell -> UExpression ( StateInitLRecord * uint256 ) false . 

Parameter prepare_external_wallet_state_init_and_addr : String -> String -> uint8 -> uint256 -> uint256 -> raw_address -> 
                                                        optional raw_address -> TvmCell -> uint8 -> UExpression ( StateInitLRecord * uint256 ) false . 
Parameter prepare_internal_wallet_state_init_and_addr : String -> String -> uint8 -> uint256 -> uint256 -> raw_address -> 
                                                        optional raw_address -> TvmCell -> uint8 -> UExpression ( StateInitLRecord * uint256 ) false . 
Parameter prepare_trading_pair_state_init_and_addr : TradingPairClassTypesModule.DTradingPairLRecord -> TvmCell ->
                                                     UExpression ( StateInitLRecord * uint256 ) false . 
Parameter prepare_trading_pair : raw_address -> raw_address -> TvmCell -> UExpression ( StateInitLRecord * uint256 ) false . 
Parameter prepare_xchg_pair_state_init_and_addr : XchgPairClassTypesModule.DXchgPairLRecord -> TvmCell -> 
                                                  UExpression ( StateInitLRecord * uint256 ) false . 
Parameter approveTradingPairImpl : uint256 -> mapping uint256 (uint256 * TradingPairListingRequestLRecord) -> 
                                   TvmCell -> uint8 -> ListingConfigLRecord -> 
                                   UExpression ( raw_address * (mapping uint256 (uint256 * TradingPairListingRequestLRecord) ) ) true .
Parameter rejectTradingPairImpl : uint256 -> mapping uint256 (uint256 * TradingPairListingRequestLRecord)-> 
                                  ListingConfigLRecord -> UExpression ( mapping uint256 (uint256 * TradingPairListingRequestLRecord) ) true . 
Parameter approveXchgPairImpl : uint256 -> mapping uint256 (uint256 * XchgPairListingRequestLRecord) -> TvmCell -> uint8 -> 
                                ListingConfigLRecord -> UExpression ( raw_address * (mapping uint256 (uint256 * XchgPairListingRequestLRecord) ) ) true . 
Parameter rejectXchgPairImpl : uint256 -> mapping uint256 (uint256 * XchgPairListingRequestLRecord) -> ListingConfigLRecord -> 
                               UExpression ( mapping uint256 (uint256 * XchgPairListingRequestLRecord) ) true . 
Parameter approveWrapperImpl : uint256 -> mapping uint256 (uint256 * WrapperListingRequestLRecord) -> TvmCell -> TvmCell -> 
                               TvmCell -> uint8 -> ListingConfigLRecord -> 
                               UExpression ( raw_address * (mapping uint256 (uint256 * WrapperListingRequestLRecord) ) ) true . 
Parameter rejectWrapperImpl : uint256 -> mapping uint256 (uint256 * WrapperListingRequestLRecord) ->
                              ListingConfigLRecord -> UExpression ( mapping uint256 (uint256 * WrapperListingRequestLRecord) ) true . 


End SpecSig.

End Spec.  



