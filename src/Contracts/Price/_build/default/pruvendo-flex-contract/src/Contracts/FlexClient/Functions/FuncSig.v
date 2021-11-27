Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonNotations.

Require Import FlexClient.ClassTypes.
Require Import FlexClient.Ledger.
Require Import FlexClient.ClassTypesNotations.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module  LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter constructor :  uint256 ->  TvmCell ->  TvmCell -> UExpression PhantomType true . 
Parameter setFlexCfg :  TonsConfigLRecord  ->  raw_address -> UExpression PhantomType true . 
Parameter setExtWalletCode :  TvmCell -> UExpression PhantomType true . 
Parameter setFlexWalletCode :  TvmCell -> UExpression PhantomType true . 
Parameter setFlexWrapperCode :  TvmCell -> UExpression PhantomType true . 
Parameter deployTradingPair :  raw_address -> uint128 -> uint128 -> uint128 ->  raw_address -> UExpression raw_address true . 
Parameter deployXchgPair :  raw_address ->  raw_address -> uint128 -> uint128 -> uint128 ->  
                            raw_address -> UExpression raw_address true . 
Parameter deployPriceWithSell : uint128 ->  uint128 -> uint32 -> uint128 -> uint8 -> uint128 ->  
                                TvmCell ->  raw_address ->  raw_address -> Tip3ConfigLRecord -> 
                                raw_address -> UExpression raw_address true . 
Parameter deployPriceWithBuy :  uint128 ->  uint128 ->  uint32 ->  uint128 ->  uint8 ->  uint128 ->  TvmCell ->  
                                raw_address ->  Tip3ConfigLRecord ->  raw_address -> UExpression raw_address true . 
Parameter cancelSellOrder :  uint128 ->  uint128 ->  uint8 ->  uint128 ->  TvmCell ->  Tip3ConfigLRecord ->  
                             raw_address -> UExpression PhantomType true . 
Parameter cancelBuyOrder :  uint128 ->  uint128 ->  uint8 ->  uint128 ->  TvmCell ->  Tip3ConfigLRecord -> 
                            raw_address -> UExpression PhantomType true . 
Parameter cancelXchgOrder :  boolean ->  uint128 ->  uint128 ->  uint128 ->  uint8 ->  uint128 ->  
                            TvmCell ->  Tip3ConfigLRecord ->  Tip3ConfigLRecord ->  raw_address -> 
                            UExpression PhantomType true . 
Parameter transfer :  raw_address ->  uint128 ->  boolean -> UExpression PhantomType true . 
Parameter deployPriceXchg :  boolean ->  uint128 ->  uint128 ->  uint128 ->  uint128 ->  uint32 ->  
                             uint128 ->  uint8 ->  uint128 ->  TvmCell ->  raw_address ->  raw_address ->  
                             Tip3ConfigLRecord ->  Tip3ConfigLRecord ->  raw_address -> UExpression raw_address true . 
Parameter registerWrapper : uint256 ->  uint128 ->  Tip3ConfigLRecord -> UExpression PhantomType true . 
Parameter registerTradingPair : uint256 ->  uint128 ->  raw_address ->  uint128 ->  raw_address -> UExpression PhantomType true . 
Parameter registerXchgPair : uint256 ->  uint128 ->  raw_address ->  raw_address ->  uint128 ->  raw_address -> UExpression PhantomType true . 
Parameter deployEmptyFlexWallet : uint256 ->  uint128 ->  Tip3ConfigLRecord -> UExpression raw_address true . 
Parameter burnWallet :  uint128 -> uint256 ->  raw_address ->  raw_address -> UExpression PhantomType true . 
Parameter getOwner : UExpression uint256 false . 
Parameter getFlex : UExpression raw_address false . 
Parameter hasExtWalletCode : UExpression boolean false . 
Parameter hasFlexWalletCode : UExpression boolean false . 
Parameter hasFlexWrapperCode : UExpression boolean false . 
Parameter getPayloadForDeployInternalWallet : uint256 ->  raw_address ->  uint128 -> UExpression TvmCell false . 
Parameter _fallback : TvmCell -> TvmSlice -> UExpression uint false . 
Parameter preparePrice : uint128 ->  uint128 ->  uint8 -> TvmCell ->  Tip3ConfigLRecord ->  
                         TvmCell ->  raw_address -> UExpression ( StateInitLRecord # ( raw_address # uint256 ) )  false . 
Parameter preparePriceXchg :  uint128 ->  uint128 ->  uint128 ->  uint8 ->  Tip3ConfigLRecord ->  
                              Tip3ConfigLRecord ->  TvmCell ->  raw_address -> 
                              UExpression ( StateInitLRecord # ( raw_address # uint256 ) )  false . 

End SpecSig.


End Spec.  