Require Import FinProof.Common. 

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.Price.ClassTypes.
Require Import Contracts.Price.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModuleForFuncSig. 

Module Type SpecSig.

Local Open Scope ursus_scope.

Parameter make_deal : ( ( OrderInfoLRecord ) ) -> ( ( OrderInfoLRecord ) ) -> UExpression ( XBool # (XBool # XInteger128) ) false . 
 Parameter extract_active_order : ( XMaybe (XInteger # OrderInfoLRecord ) ) -> ( ( XQueue OrderInfoLRecord ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> UExpression ( ( XMaybe (XInteger # OrderInfoLRecord) ) # (( XQueue OrderInfoLRecord ) # XInteger128) ) false . 
 Parameter process_queue : ( ( XInteger ) ) -> ( ( XInteger ) ) -> UExpression PhantomType false . 
 Parameter onTip3LendOwnership : ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger32 ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XCell ) ) -> UExpression OrderRetLRecord false . 
 Parameter buyTip3 : ( ( XInteger128 ) ) -> ( ( XAddress ) ) -> ( ( XInteger32 ) ) -> UExpression OrderRetLRecord true . 
 Parameter processQueue : UExpression PhantomType false . 
 Parameter cancelSell : UExpression PhantomType false . 
 Parameter cancelBuy : UExpression PhantomType false . 
 Parameter getDetails : UExpression DetailsInfoLRecord false . 
 Parameter getPrice : UExpression XInteger128 false . 
 Parameter getMinimumAmount : UExpression XInteger128 false . 
 Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
 Parameter getSells : UExpression ( XHMap XInteger OrderInfoLRecord ) false . 
 Parameter getBuys : UExpression ( XHMap XInteger OrderInfoLRecord ) false . 
 Parameter getSellAmount : UExpression XInteger128 false . 
 Parameter getBuyAmount : UExpression XInteger128 false . 
 Parameter _fallback : XCell -> XSlice -> UExpression XInteger false . 
 Parameter onTip3LendOwnershipMinValue : UExpression XInteger128 false . 
 Parameter buyTip3MinValue : ( ( XInteger128 ) ) -> UExpression XInteger128 false . 
 Parameter verify_tip3_addr : ( ( XAddress ) ) -> ( ( XInteger256 ) ) -> ( ( XInteger256 ) ) -> UExpression XBool false . 
 Parameter expected_wallet_address : ( ( XInteger256 ) ) -> ( ( XInteger256 ) ) -> UExpression XInteger256 false . 
 Parameter on_sell_fail : ( ( XInteger ) ) -> ( XAddress (*ITONTokenWalletPtr*) ) -> ( ( XInteger128 ) ) -> UExpression OrderRetLRecord false . 
 Parameter prepare_price_state_init_and_addr : ( ( ContractLRecord ) ) -> ( ( XCell ) ) -> UExpression ( StateInitLRecord # XInteger256 ) false . 
 Parameter is_active_time : ( ( XInteger32 ) ) -> UExpression XBool false . 
 Parameter calc_cost : ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> UExpression (XMaybe XInteger128) false . 
 Parameter process_queue_impl : ( ( XAddress ) ) -> ( XAddress (*IFlexNotifyPtr*) ) -> ( ( XInteger128 ) ) -> ( ( XInteger8 ) ) -> ( ( TonsConfigLRecord ) ) -> ( ( XInteger ) ) -> ( ( XInteger ) ) -> ( ( XInteger128 ) ) -> ( ( XQueue OrderInfoLRecord ) ) -> ( ( XInteger128 ) ) -> ( ( XQueue OrderInfoLRecord ) ) -> UExpression process_retLRecord false . 
 Parameter cancel_order_impl : ( ( XQueue OrderInfoLRecord ) ) -> ( ( addr_std_fixedLRecord ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> ( XInteger (*Grams*) ) -> ( XInteger (*Grams*) ) -> ( XInteger (*Grams*) ) -> UExpression ((XQueue OrderInfoLRecord) # XInteger128) false . 


End SpecSig.

End Spec.  