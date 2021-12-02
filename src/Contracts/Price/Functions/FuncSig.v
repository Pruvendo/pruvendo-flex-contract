Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonAxioms.

Require Import Price.ClassTypes.
Require Import Price.Ledger.
Require Import Price.ClassTypesNotations.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Notation OrderInfoWithIdx := (uint # OrderInfoLRecord).

Module Type SpecSig.

Parameter make_deal : ULValue dealerLRecord -> ULValue OrderInfoLRecord  ->  ULValue OrderInfoLRecord -> UExpression ( boolean # (boolean # uint128)) true . 
(*Check  ULValue !!!!*)
Parameter extract_active_order : optional OrderInfoWithIdx -> 
                                 queue OrderInfoLRecord -> 
                                 uint128 -> 
                                 boolean -> 
                                 UExpression ( optional OrderInfoWithIdx # ((queue OrderInfoLRecord) # uint128))  true .                                 
Parameter process_queue : ULValue dealerLRecord ->  uint ->  uint  -> UExpression PhantomType true . 

Parameter onTip3LendOwnership : address -> uint128 -> uint32 -> uint256 -> address -> cell -> UExpression OrderRetLRecord true . 
Parameter buyTip3 : uint128 -> address -> uint32 -> UExpression OrderRetLRecord true . 
Parameter processQueue : UExpression PhantomType true . 
Parameter cancelSell : UExpression PhantomType false . 
Parameter cancelBuy : UExpression PhantomType false . 
Parameter getDetails : UExpression DetailsInfoLRecord false . 
Parameter getPrice : UExpression uint128 false . 
Parameter getMinimumAmount : UExpression uint128 false . 
Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
Parameter getSells : UExpression ( mapping uint OrderInfoLRecord ) false . 
Parameter getBuys : UExpression ( mapping uint OrderInfoLRecord ) false . 
Parameter getSellAmount : UExpression uint128 false . 
Parameter getBuyAmount : UExpression uint128 false . 
Parameter _fallback : cell -> slice -> UExpression uint false . 
Parameter onTip3LendOwnershipMinValue : UExpression uint128 false . 
Parameter buyTip3MinValue : uint128 -> UExpression uint128 false . 
Parameter verify_tip3_addr : address -> uint256 -> uint256 -> UExpression boolean false . 
Parameter expected_wallet_address : uint256 -> uint256 -> UExpression uint256 false . 
Parameter on_sell_fail : uint -> address (*ITONTokenWalletPtr*) -> uint128 -> UExpression OrderRetLRecord false . 
Parameter prepare_price_state_init_and_addr : DPriceLRecord -> cell -> UExpression ( StateInitLRecord # uint256 ) false . 
Parameter is_active_time : uint32 -> UExpression boolean false . 
Parameter calc_cost : uint128 -> uint128 -> UExpression (optional uint128) true . 
Parameter process_queue_impl : address -> address (*IFlexNotifyPtr*) -> uint128 -> uint8 -> TonsConfigLRecord -> 
                               uint -> uint -> uint128 -> queue OrderInfoLRecord -> 
                               uint128 -> 
                               queue OrderInfoLRecord -> UExpression process_retLRecord true . 
Parameter cancel_order_impl : queue OrderInfoLRecord -> addr_std_fixed -> uint128 -> boolean -> Grams -> 
                              Grams -> Grams -> UExpression ((queue OrderInfoLRecord) # uint128) false . 

End SpecSig.

End Spec.  