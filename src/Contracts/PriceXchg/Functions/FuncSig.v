Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonNotations.

Require Import PriceXchg.ClassTypes.
Require Import PriceXchg.Ledger.
Require Import PriceXchg.ClassTypesNotations.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.


Notation price_t := (RationalPriceLRecord).
Notation OrderInfoXchgWithIdx := (uint # OrderInfoXchgLRecord).

Module Type SpecSig.


(* Parameter make_deal : ULValue OrderInfoXchgLRecord -> ULValue OrderInfoXchgLRecord -> UExpression ( boolean # (boolean # uint128) ) false . 
 *)
(* static std::tuple<std::optional<OrderInfoXchgWithIdx>, big_queue<OrderInfoXchg>, uint128>
  extract_active_order(std::optional<OrderInfoXchgWithIdx> cur_order,
                       big_queue<OrderInfoXchg> orders, uint128 all_amount, bool_t sell) *)
(*Error: not ULValue !!!*)
(* Parameter extract_active_order : ULValue ( optional OrderInfoXchgWithIdx ) -> 
                                 ULValue ( queue OrderInfoXchgLRecord )  -> 
                                 ULValue ( uint128 ) -> boolean -> 
          UExpression ( optional OrderInfoXchgWithIdx # ((queue OrderInfoXchgLRecord) # uint128) )  true .  *)
(* Parameter process_queue : uint -> uint -> UExpression PhantomType true .  *)
Parameter onTip3LendOwnership : address -> uint128 -> uint32 -> uint256 -> address -> TvmCell -> UExpression OrderRetLRecord true . 
Parameter processQueue : UExpression PhantomType false . 
Parameter cancelSell : UExpression PhantomType false . 
Parameter cancelBuy : UExpression PhantomType false . 
Parameter getDetails : UExpression DetailsInfoXchgLRecord false . 
Parameter getPriceNum : UExpression uint128 false . 
Parameter getPriceDenum : UExpression uint128 false . 
Parameter getMinimumAmount : UExpression uint128 false . 
Parameter getTonsCfg : UExpression TonsConfigLRecord false . 
Parameter getSells : UExpression ( mapping uint OrderInfoXchgLRecord ) false . 
Parameter getBuys : UExpression ( mapping uint OrderInfoXchgLRecord ) false . 
Parameter getSellAmount : UExpression uint128 false . 
Parameter getBuyAmount : UExpression uint128 false . 
Parameter _fallback : TvmCell -> TvmSlice  -> UExpression uint false . 
Parameter onTip3LendOwnershipMinValue : UExpression uint128 false . 
Parameter verify_tip3_addr : Tip3ConfigLRecord -> address -> uint256 -> uint256 -> UExpression boolean false . 
Parameter expected_wallet_address : Tip3ConfigLRecord -> uint256 -> uint256 -> UExpression uint256 false . 
Parameter on_ord_fail :  uint -> address (* ITONTokenWalletPtrLRecord *)  -> uint128  -> UExpression OrderRetLRecord false . 

Parameter prepare_price_xchg_state_init_and_addr: ContractLRecord -> TvmCell -> UExpression ( StateInitLRecord # uint256 ) false . 
Parameter is_active_time : uint32  -> UExpression boolean false . 
Parameter minor_cost : uint128 -> price_t -> UExpression (optional uint128) false . 
Parameter process_queue_impl : address -> address -> address (* IFlexNotifyPtrLRecord *) -> 
                               price_t -> uint8 -> TonsConfigLRecord -> 
                               uint -> uint -> uint128 -> queue OrderInfoXchgLRecord ->
                               uint128 -> queue OrderInfoXchgLRecord -> UExpression process_retLRecord false .
Parameter cancel_order_impl : queue OrderInfoXchgLRecord -> 
                              addr_std_fixed -> uint128 -> boolean -> 
                              Grams -> Grams -> Grams -> UExpression ((queue OrderInfoXchgLRecord) # uint128) false . 
Parameter int_sender_and_value : UExpression ( address # Grams ) false . 

End SpecSig.

End Spec.  