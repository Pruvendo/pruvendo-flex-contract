Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.TvmCells. 

Require Import Project.CommonAxioms.
Require Import Flex.ClassTypesNotations.
Require Import Flex.ClassTypes.
Require Import Flex.Ledger.

Require TradingPair.ClassTypes.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Notation wrappers_map := ( mapping uint256 ((* uint256 # *) WrapperListingRequestLRecord) ).
Notation trading_pairs_map := ( mapping uint256 ((* uint256 # *) TradingPairListingRequestLRecord) ).
Notation xchg_pairs_map := ( mapping uint256 ((* uint256 # *) XchgPairListingRequestLRecord) ).

Module Type SpecSig.

Parameter constructor : uint256 -> String -> optional address -> TonsConfigLRecord -> uint8 -> 
                        ListingConfigLRecord -> UExpression PhantomType true . 
Parameter setSpecificCode : uint8 -> cell -> UExpression PhantomType true . 
Parameter setPairCode : cell -> UExpression PhantomType true . 
Parameter setXchgPairCode : cell -> UExpression PhantomType true . 
Parameter setWrapperCode : cell -> UExpression PhantomType true . 
Parameter setPriceCode : cell -> UExpression PhantomType true . 
Parameter setXchgPriceCode : cell -> UExpression PhantomType true . 
Parameter setExtWalletCode : cell -> UExpression PhantomType true . 
Parameter setFlexWalletCode : cell -> UExpression PhantomType true . 
Parameter transfer : address -> uint128 -> UExpression PhantomType true . 
Parameter registerTradingPair : uint256 -> address -> uint128 -> address -> UExpression address true . 
Parameter approveTradingPair : uint256 -> UExpression address true . 
Parameter rejectTradingPair : uint256 -> UExpression boolean true . 
Parameter registerXchgPair : uint256 -> address -> address -> uint128 -> address -> UExpression address true . 
Parameter approveXchgPair : uint256 -> UExpression address true . 
Parameter rejectXchgPair : uint256 -> UExpression boolean true . 
Parameter registerWrapper : uint256 -> Tip3ConfigLRecord -> UExpression address true . 
Parameter approveWrapper : uint256 -> UExpression address true . 
Parameter rejectWrapper : uint256 -> UExpression boolean true . 
Parameter isFullyInitialized : UExpression boolean false . 
Parameter getDetails : UExpression FlexDetailsLRecord true . 
Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
Parameter getListingCfg : UExpression ListingConfigLRecord false . 
Parameter getTradingPairCode : UExpression cell true . 
Parameter getXchgPairCode : UExpression cell true . 
Parameter getSellPriceCode : address -> UExpression cell true . 
Parameter getXchgPriceCode : address -> address -> UExpression cell true . 
Parameter getSellTradingPair : address -> UExpression address true . 
Parameter getXchgTradingPair : address -> address -> UExpression address true . 
Parameter getDealsLimit : UExpression uint8 false . 
Parameter getOwnershipInfo : UExpression FlexOwnershipInfoLRecord false .
Parameter getWrapperListingRequests : UExpression ( mapping uint WrapperListingRequestWithPubkeyLRecord) false .
Parameter getTradingPairListingRequests : UExpression ( mapping uint TradingPairListingRequestWithPubkeyLRecord) false . 
Parameter getXchgPairListingRequests : UExpression ( mapping uint XchgPairListingRequestWithPubkeyLRecord) false . 
Parameter check_owner : UExpression PhantomType true . 
Parameter _fallback : cell -> slice -> UExpression uint false . 
Parameter prepare_wrapper_state_init_and_addr : cell -> WrapperClassTypesModule.DWrapperLRecord -> UExpression ( StateInitLRecord # uint256 ) false . 
Parameter prepare_flex_state_init_and_addr : ContractLRecord -> cell -> UExpression ( StateInitLRecord # uint256 ) false . 

Parameter prepare_external_wallet_state_init_and_addr : String -> String -> uint8 -> uint256 -> uint256 -> address -> 
                                                        optional address -> cell -> int -> UExpression ( StateInitLRecord # uint256 ) false . 
Parameter prepare_internal_wallet_state_init_and_addr : String -> String -> uint8 -> uint256 -> uint256 -> address -> 
                                                        optional address -> cell -> int -> UExpression ( StateInitLRecord # uint256 ) false . 
Parameter prepare_trading_pair_state_init_and_addr : TradingPairClassTypesModule.DTradingPairLRecord -> cell ->
                                                     UExpression ( StateInitLRecord # uint256 ) false . 
Parameter prepare_trading_pair : address -> address -> cell -> UExpression ( StateInitLRecord # uint256 ) false . 
Parameter prepare_xchg_pair_state_init_and_addr : XchgPairClassTypesModule.DXchgPairLRecord -> cell -> 
                                                  UExpression ( StateInitLRecord # uint256 ) false . 
Parameter approveTradingPairImpl : uint256 -> trading_pairs_map -> 
                                   cell -> int -> ListingConfigLRecord -> 
                                   UExpression ( address # trading_pairs_map ) true .
Parameter rejectTradingPairImpl : uint256 -> trading_pairs_map-> 
                                  ListingConfigLRecord -> UExpression trading_pairs_map true . 
Parameter approveXchgPairImpl : uint256 -> xchg_pairs_map -> cell -> int -> 
                                ListingConfigLRecord -> UExpression ( address # xchg_pairs_map ) true . 
Parameter rejectXchgPairImpl : uint256 -> xchg_pairs_map -> ListingConfigLRecord -> 
                               UExpression xchg_pairs_map true . 
Parameter approveWrapperImpl : uint256 -> wrappers_map -> cell -> cell -> 
                               cell -> int -> ListingConfigLRecord -> 
                               UExpression ( address # wrappers_map )  true . 
Parameter rejectWrapperImpl : uint256 -> wrappers_map ->
                              ListingConfigLRecord -> UExpression wrappers_map true . 


End SpecSig.

End Spec.  



