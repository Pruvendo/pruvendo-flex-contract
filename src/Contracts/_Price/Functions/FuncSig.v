Require Import FinProof.Common. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.Price.ClassTypes.
Require Import Contracts.Price.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module Export ClassTypesModuleForFuncSig := ClassTypes xt sm.
Module  LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.

Parameter calc_cost : URValue XInteger128 false -> URValue XInteger128 false -> UExpression ( XMaybe XInteger128 ) false . 
 Parameter make_deal : URValue OrderInfoLRecord false -> URValue OrderInfoLRecord false -> UExpression ( XBool # XBool # XInteger128 )%sol false . 
 Parameter is_active_time : URValue XInteger32 false -> UExpression XBool false . 
 Parameter extract_active_order : URValue ( XMaybe ( XInteger # OrderInfoLRecord)%sol ) false -> URValue ( XQueue OrderInfoLRecord) false -> URValue XInteger128 false -> URValue XBool false -> UExpression ( XList OrderInfoLRecord ) false . 
 Parameter process_queue : URValue XInteger false -> URValue XInteger false -> UExpression PhantomType false . 
 Parameter process_queue_impl : URValue XAddress false -> URValue XAddress (* IFlexNotifyPtr *) false -> URValue XInteger128 false -> URValue XInteger8 false -> URValue TonsConfigLRecord false -> URValue XInteger false -> URValue XInteger false -> URValue XInteger128 false -> URValue ( XQueue OrderInfoLRecord) false -> URValue XInteger128 false -> URValue ( XQueue OrderInfoLRecord) false -> UExpression process_retLRecord false . 
 Parameter processQueue : UExpression PhantomType false . 
 Parameter onTip3LendOwnershipMinValue : UExpression XInteger128 false . 
 Parameter expected_wallet_address : URValue XInteger256 false -> URValue XInteger256 false -> UExpression XInteger256 false . 
 Parameter verify_tip3_addr : URValue XAddress false -> URValue XInteger256 false -> URValue XInteger256 false -> UExpression XBool false . 
 Parameter on_sell_fail : URValue XInteger false -> URValue XAddress (* ITONTokenWalletPtr *) false -> URValue XInteger128 false -> UExpression OrderRetLRecord false . 
 Parameter onTip3LendOwnership : URValue XAddress false -> URValue XInteger128 false -> URValue XInteger32 false -> URValue XInteger256 false -> URValue XAddress false -> URValue XCell false -> UExpression OrderRetLRecord false . 
 Parameter buyTip3MinValue : URValue XInteger128 false -> UExpression XInteger128 false . 
 Parameter buyTip3 : URValue XInteger128 false -> URValue XAddress false -> URValue XInteger32 false -> UExpression OrderRetLRecord true . 
 Parameter cancel_order_impl : URValue ( XQueue OrderInfoLRecord) false -> URValue addr_std_fixedLRecord false -> URValue XInteger128 false -> URValue XBool false -> URValue XInteger (* Grams *) false -> URValue XInteger (* Grams *) false -> URValue XInteger (* Grams *) false -> UExpression ( XQueue OrderInfoLRecord ) false . 
 Parameter cancelSell : UExpression PhantomType false . 
 Parameter cancelBuy : UExpression PhantomType false . 
 Parameter getPrice : UExpression XInteger128 false . 
 Parameter getMinimumAmount : UExpression XInteger128 false . 
 Parameter getSellAmount : UExpression XInteger128 false . 
 Parameter getBuyAmount : UExpression XInteger128 false . 
 Parameter getDetails : UExpression DetailsInfoLRecord false . 
 Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
 Parameter getSells : UExpression ( XHMap XInteger OrderInfoLRecord ) false . 
 Parameter getBuys : UExpression ( XHMap XInteger OrderInfoLRecord ) false . 
 Parameter _fallback : URValue XCell false -> URValue XSlice false -> UExpression XInteger false . 
 Parameter prepare_price_state_init_and_addr : URValue ContractLRecord false -> URValue XCell false -> UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 
End SpecSig.

End Spec.  