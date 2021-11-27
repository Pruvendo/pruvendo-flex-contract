Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.
Require Import Project.CommonNotations.
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Price.Ledger.
Require Import Price.Functions.FuncSig.
Require Import Price.Functions.FuncNotations.
(* Require Contracts.Price.Interface. *)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.

Module Funcs (co: CompilerOptions) (dc : ConstsTypesSig XTypesModule StateMonadModule) .

Import co.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module TONTonkenWalletModuleForPrice := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .
(* Export SpecModuleForFuncNotations(* ForFuncs *).CommonNotationsModule. *)

Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.


(*move somewhere*)
Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.

Existing Instance LedgerPruvendoRecord.

(***************************************************************************)						   

Definition calc_cost ( amount : ( uint128 ) ) ( price : ( uint128 ) ) : UExpression (XMaybe uint128) false . 
 	 	 refine {{ new 'tons_cost : ( uint ) @ "tons_cost" := (#{amount}) * (#{price}) ; { _ } }} . 
 	 	 refine {{ if ( !{tons_cost} >> #{128} ) 
                     then { { _:UExpressionP (XMaybe uint128) false } } ; { _ } }} . 
 	 	 	 refine {{ return_ {} }} . 
 	 	 refine {{ return_ ( (!{tons_cost}) -> set () ) }} . 
Defined . 

Definition calc_cost_right { a1 a2 }  ( amount : URValue uint128 a1 ) 
									  ( price : URValue uint128 a2 ) : URValue (optional uint128) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_cost amount price ) . 
 		
 Notation " 'calc_cost_' '(' amount ',' price ')' " := 
 ( calc_cost_right 
 amount price ) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom URValue at level 0 ) : ursus_scope . 

Definition make_deal 
( sell : ULValue( OrderInfoLRecord ) ) 
( buy : ULValue ( OrderInfoLRecord ) ) 
: UExpression ( XBool # (XBool # uint128) ) true . 

 	 	refine {{ new 'deal_amount : ( uint ) @ "deal_amount" := min ( (!{sell}) ↑ OrderInfo.amount , (!{buy}) ↑ OrderInfo.amount ) ; { _ } }} . 
 	 	refine {{ new 'last_tip3_sell : ( XBool ) @ "last_tip3_sell" := 	 	 
                   ( !{deal_amount} == ( ( !{sell} ) ↑ OrderInfo.amount ) ) ; { _ } }} .
  	 refine {{ ( {sell} ↑ OrderInfo.amount ) -= !{deal_amount} ; { _ } }} . 
 	 	 refine {{ ( {buy} ↑ OrderInfo.amount ) -= !{deal_amount} ; { _ } }} . 

 	 	 refine {{ new 'cost : ( XMaybe uint ) @ "cost" := calc_cost_ ( !{deal_amount} , _price_ ) ; { _ } }} .
 
 	 	 refine {{ new 'sell_costs : ( uint128 ) @ "sell_costs" := 0 ; { _ } }} . 
 	 	 refine {{ new 'buy_costs : ( uint128 ) @ "buy_costs" := 
                                              ((!{cost}) -> get ()) ; { _ } }} . 

 	 	 refine {{ if ( !{last_tip3_sell} ) then { { _:UExpressionP (XBool * (XBool * uint128)) false } } 
                                          else { { _:UExpressionP (XBool * (XBool * uint128)) false } } ; { _ } }} . 
 	 	 	 refine {{ {sell_costs} += ( (_tons_cfg_ ↑ TonsConfig.transfer_tip3) + 
                                   (_tons_cfg_ ↑ TonsConfig.send_notify) ) }} .
 
 	 	 refine {{ {buy_costs} += ( (_tons_cfg_ ↑ TonsConfig.transfer_tip3) +
                                (_tons_cfg_ ↑ TonsConfig.send_notify) ) }} . 

 	 	 refine {{ new 'sell_out_of_tons : ( XBool ) @ "sell_out_of_tons" := 
                  ( ((!{sell}) ↑ OrderInfo.account) < !{sell_costs} ) ; { _ } }} . 
 	 	 refine {{ new 'buy_out_of_tons : ( XBool ) @ "buy_out_of_tons" := 
                 ( ((!{buy}) ↑ OrderInfo.account) < !{buy_costs} ) ; { _ } }} . 

 	 	 refine {{ if ( !{sell_out_of_tons} \\ !{buy_out_of_tons} ) 
                  then { { _ :UExpressionP (XBool * (XBool * uint128)) false} } ; { _ } }} . 
 	 	 	 refine {{ return_ [ !{ sell_out_of_tons } , !{ buy_out_of_tons } , 0 ] }} . 
 	 	  refine {{ (({sell}) ↑ OrderInfo.account) -= !{sell_costs} ; { _ } }} . 
 	 	 refine {{ (({buy})  ↑ OrderInfo.account) -= !{buy_costs} ; { _ } }} .
(*  	 	 refine {{ ITONTokenWalletPtr ( sell . tip3_wallet ) ( Grams ( tons_cfg_ . transfer_tip3 . get ( ) ) ) . transfer ( sell . tip3_wallet , buy . tip3_wallet , deal_amount , uint128 ( 0 ) , bool_t { false } ) ; { _ } }} .  *)
(*  	 	 refine {{ tvm.transfer ( sell . client_addr , cost - > get ( ) , true , SENDER_WANTS_TO_PAY_FEES_SEPARATELY ) ; { _ } }} .  *)
(*  	 	 refine {{ notify_addr_ ( Grams ( _tons_cfg_ ^^ TonsConfig.send_notify ) ) . onDealCompleted ( _tip3root_ , _price_ , !{deal_amount} ) ; { _ } }} .  *)
	refine {{ return_ [ FALSE , FALSE , !{ deal_amount } ] }} . 
Defined .

Notation "'λ2LL'" := (@UExpression_Next_LedgerableWithLArgs _ _ _ _ _( @UExpression_Next_LedgerableWithLArgs _ _ _ _ _ λ0)) (at level 0) : ursus_scope.

Definition make_deal_right  ( sell : ULValue OrderInfoLRecord ) ( buy : ULValue OrderInfoLRecord ) 
                            : URValue ( boolean # (boolean # uint128) ) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2LL ) make_deal sell buy ) . 
 
Notation " 'make_deal_' '(' sell ',' buy ')' " := 
 ( make_deal_right sell buy ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 , buy custom URValue at level 0 ) : ursus_scope . 

Parameter safe_delay_period : uint.

Definition is_active_time ( order_finish_time : uint32 ) : UExpression boolean false . 
 	refine {{ return_ ( ( (tvm.now ()) +  (#{safe_delay_period}) ) < (#{order_finish_time} ) ) }} . 
Defined. 
 
Definition is_active_time_right { a1 }  ( order_finish_time : URValue uint32 a1 ) : URValue boolean a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) is_active_time order_finish_time ) . 
 
 Notation " 'is_active_time_' '(' order_finish_time ')' " := 
 ( is_active_time_right 
 order_finish_time ) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope .

Definition extract_active_order 
( cur_order : ULValue ( XMaybe (uint # OrderInfoLRecord) ) ) 
( orders : ULValue( XQueue OrderInfoLRecord ) ) 
( all_amount : ULValue ( uint128 ) ) 
( sell : ( XBool ) ) 
: UExpression (( XMaybe (uint # OrderInfoLRecord) ) 
                # ( ( XQueue OrderInfoLRecord ) # uint128 ) ) true  . 

 	 	 refine {{ if ( !{ cur_order } ) then { { _:UEf  } } ; { _ } }} .
 	 	 	 refine {{ return_ [ (!{ cur_order }) , (!{ orders }) , (!{ all_amount }) ] }} .
 
 	 	 refine {{ while ( ~ ((!{orders}) -> empty ()) ) do { { _:UEt } } ; { _ } }} . 
   	 	 	 refine {{ ({cur_order}) := (!{orders}) ->front_with_idx_opt () ; { _ } }} .
 	 	 	 refine {{ new 'ord : ( OrderInfoLRecord ) @ "ord" := 
                               ( second ((!{cur_order}) -> get () )) ; { _ } }} . 
 	 	 	 refine {{ if ( ~ ( is_active_time_ ( (!{ord}) ↑ OrderInfo.order_finish_time ) ) )
                                  then { { _:UEt } } ; { _ } }} . 
  	 	 	 	 refine {{ {all_amount} -= (!{ord}) ↑ OrderInfo.amount ; { _ } }} .
 	 	 	 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 	 	 	 
 	 	 	            [ ec::expired , (!{ord}) ↑ OrderInfo.original_amount , 0 ] ; { _ } }} . 
(*  	 	 	 	 refine {{ IPriceCallbackPtr ( ord . client_addr ) ( Grams ( ord . account . get ( ) ) ) . onOrderFinished ( ret , sell ) ; { _ } }} .  *)
  	 	 	 	 refine {{ {orders} -> pop () ; { _ } }} .
  	 	 	 	 refine {{ {cur_order} -> reset () ; { _ } }} .  
  	 	 	 	 refine {{ continue_ }} . 
 	 	 refine {{ break_ }} .
    refine {{ return_ [ !{cur_order} , !{orders} , !{all_amount} ] }} . 
Defined .  

Notation "'λ1LLL'" :=  ( @UExpression_Next_LedgerableWithLArgs _ _ _ _ _
                       ( @UExpression_Next_LedgerableWithLArgs _ _ _ _ _
                       ( @UExpression_Next_LedgerableWithLArgs _ _ _ _ _ λ1))) 
                       (at level 0) : ursus_scope.


Definition extract_active_order_right { a4 }  
			( cur_order : ULValue ( optional (uint # OrderInfoLRecord) ) ) 
			( orders : ULValue ( queue OrderInfoLRecord ) ) 
			( all_amount : ULValue uint128 ) 
			( sell : URValue boolean a4 ) : URValue (( optional (uint # OrderInfoLRecord) ) # ( ( queue OrderInfoLRecord ) # uint128 ) ) true := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1LLL ) extract_active_order cur_order orders all_amount sell ) . 
 
Notation " 'extract_active_order_' '(' cur_order ',' orders ',' all_amount ',' sell ')' " := 
 ( extract_active_order_right  cur_order orders all_amount sell ) 
 (in custom URValue at level 0 , cur_order custom URValue at level 0 , orders custom ULValue at level 0 , 
  all_amount custom ULValue at level 0 , sell custom URValue at level 0 ) : ursus_scope .
 
Definition process_queue ( sell_idx : uint ) ( buy_idx : uint ) : UExpression PhantomType true . 
 	 	 refine {{ new 'sell_opt : ( XMaybe (uint # OrderInfoLRecord) ) @ "sell_opt" := {} ; { _ } }} . 
 	 	 refine {{ new 'buy_opt : ( XMaybe (uint # OrderInfoLRecord) ) @ "buy_opt" := {} ; { _ } }} . 
 	 	 refine {{ new 'deals_count : ( uint ) @ "deals_count" := 0 ; { _ } }} . 
 	 	 refine {{ while ( TRUE ) do { { _ : UEt} } ; { _ } }} .  
 	 	 	 refine {{ [ {sell_opt} , _sells_ , _sells_amount_ ] := 
              extract_active_order_ ( {sell_opt} , _sells_ , _sells_amount_ , TRUE )  ; { _ } }} . 
 	 	 	 refine {{ [ {buy_opt} , _buys_ , _buys_amount_ ] := 
              extract_active_order_ ( {buy_opt} , _buys_ , _buys_amount_ , FALSE )  ; { _ } }} . 
 	 	 	 refine {{ if ( (~ (!{ sell_opt })) \\ (~ (!{ buy_opt })) ) 
                    then { { _: UEt } } ; { _ } }} .
 	 	 	 	 refine {{  break_ }} . 
 	 	 refine {{ new ( 'sell_idx_cur : uint , 'sell : OrderInfoLRecord ) @
                ( "sell_idx_cur" , "sell" ) := (!{sell_opt}) -> get () ; { _ } }} .
 	 	 refine {{ new ( 'buy_idx_cur : uint , 'buy : OrderInfoLRecord ) @
                ( "buy_idx_cur" , "buy" ) := (!{buy_opt}) -> get () ; { _ } }} .
 	 	 	 refine {{ new 'sell_out_of_tons : ( XBool ) @ "sell_out_of_tons" := FALSE ; { _ } }} . 
 	 	 	 refine {{ new 'buy_out_of_tons : ( XBool ) @ "buy_out_of_tons" := FALSE ; { _ } }} . 
 	 	 	 refine {{ new 'deal_amount : ( uint128 ) @ "deal_amount" := 0 ; { _ } }} . 
 
 	 	 	 refine {{ if ( ++ ({ deals_count }) > _deals_limit_ ) 
                      then { { _: UEt } } }} . 
 	 	 	 	 refine {{ new 'half_process_queue : uint @ "half_process_queue" 
                         := (_tons_cfg_ ↑ TonsConfig.process_queue) / #{2} ; { _ } }} . 
 	 	 	 	 refine {{ new 'safe_extra : ( uint ) @ "safe_extra" := 
                        (_tons_cfg_ ↑ TonsConfig.return_ownership) + 
                        (_tons_cfg_ ↑ TonsConfig.order_answer ) ; { _ } }} . 
 	 	 	 	 refine {{ if ( (!{sell} ↑ OrderInfo.account) < 
                     (!{half_process_queue} + !{ safe_extra }) ) 
                            then { { _: UEf } } ; { _ } }} .
 	 	 	 	 	 refine {{ {sell_out_of_tons} := TRUE }} . 
 	 	 	 refine {{ if ( ( (!{buy}) ↑ OrderInfo.account )
                        < !{half_process_queue} + !{ safe_extra } ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ {buy_out_of_tons} := TRUE }} .
 	 	   refine {{ if ( (~ !{ sell_out_of_tons } ) && (~ !{ buy_out_of_tons } ) ) 
                        then { { _:UEt } } ; { _ } }} . 	 	 	 
         refine {{ ({sell} ↑ OrderInfo.account) -= !{half_process_queue} ; { _ } }} . 
 	 	 	   refine {{ ({buy} ↑ OrderInfo.account) -= !{half_process_queue} ; { _ } }} . 
(*  	 	 	 refine {{ IPricePtr ( address { tvm.address ( ) } ) ( Grams ( tons_cfg_ . process_queue . get ( ) ) ) . processQueue ( ) ; { _ } }} .  *)
 	 	 	     refine {{ if ( (#{sell_idx}) == !{sell_idx_cur} ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	     (* refine {{ dealer.ret_ := [ 1 (* ec::deals_limit *) , 
                              ((!{sell}) ↑ OrderInfo.original_amount) - 
                              ((!{sell}) ↑ OrderInfo.amount) , 
                              ((!{sell}) ↑ OrderInfo.amount) ] }} . *) 
             refine {{ return_ {} }} .
 	 	 	 refine {{ if ( (#{ buy_idx }) == !{ buy_idx_cur } ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 (* refine {{ dealer.ret_ := [ 1 (* ec::deals_limit *) , 
                              ((!{buy}) ↑ OrderInfo.original_amount) - 
                              ((!{buy}) ↑ OrderInfo.amount) , 
                              ((!{buy}) ↑ OrderInfo.amount) ] }} . *)
             refine {{ return_ {} }} .

 	 	 	 refine {{ break_ }} . 

 refine {{ if ( (~ !{ sell_out_of_tons }) && (~ !{ buy_out_of_tons }) ) then { { _:UEt } } ; { _ } }} . 
 
 	 refine {{ [ {sell_out_of_tons} , {buy_out_of_tons} , {deal_amount} ] := 
                         make_deal_ ( {sell} , {buy} ) }} . 
 refine {{ if ( !{ sell_out_of_tons } ) then { { _:UEf } } ; { _ } }} . 
  	 refine {{ _sells_ -> pop () ; { _ } }} .
 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	                      [ ec::out_of_tons , 
                              ((!{sell}) ↑ OrderInfo.original_amount) - 
                              ((!{sell}) ↑ OrderInfo.amount) , 
                              ((!{sell}) ↑ OrderInfo.amount) ] ; { _ } }} .
 	 refine {{ if ( (#{ sell_idx }) == !{sell_idx_cur} ) then { { _:UEf } } ; { _ } }} . 
 	 	 refine {{ (* dealer.ret_ *) {ret} := !{ ret } }} . 
 	 refine {{ if ( ((!{sell}) ↑ OrderInfo.account) > 
                (_tons_cfg_ ↑ TonsConfig.return_ownership) ) then { { _:UEf } } ; { _ } }} . 
 	 	 refine {{ (({sell}) ↑ OrderInfo.account) -= (_tons_cfg_ ↑ TonsConfig.return_ownership) (* ; { _ } }} . 
 	 	 refine {{ ITONTokenWalletPtr ( sell . tip3_wallet ) ( Grams ( tons_cfg_ . return_ownership . get ( ) ) ) . returnOwnership ( sell . amount ) ; { _ } }} . 
 	 	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { true } ) *) }} . 
 refine {{ {sell_opt} -> reset () }} . 

 refine {{ if ( !{buy_out_of_tons} ) then { { _:UEf } } ; { _ } }} . 
 	 (* refine {{ { dealer.buys_ -> pop () ; { _ } }} .  *)
 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	                      [ 1 (*ec::out_of_tons*),
                              ((!{buy}) ↑ OrderInfo.original_amount) - 
                              ((!{buy}) ↑ OrderInfo.amount) , 
                              0 ] ; { _ } }} .
 	 refine {{ if ( (#{ buy_idx }) == !{ buy_idx_cur } ) then { { _:UEf } } ; { _ } }} . 
 	 	 refine {{ (* dealer.ret_ *) { ret } := !{ ret } }} . 
(*  	 refine {{ IPriceCallbackPtr ( buy . client_addr ) ( Grams ( buy . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { false } ) ; { _ } }} .  *)
 	 refine {{ ({buy_opt}) -> reset () }} . 
 refine {{ if ( !{ sell_out_of_tons } \\ !{ buy_out_of_tons } ) then { { _:UEt } } ; { _ } }} . 
 	 refine {{ continue_ }} .
(*                      TODO:
The term "sell_opt" has type "ULValue (optional (uint # OrderInfoLRecord))"
  refine {{  second ( {sell_opt} ) := !{sell} ; { _ } }} .
  refine {{ { buy_opt } - > second = buy ; { _ } }} .  *)

 refine {{ _sells_amount_ -= !{ deal_amount } ; { _ } }} . 
 refine {{ _buys_amount_ -= !{ deal_amount } ; { _ } }} .
 refine {{ if ( ~ ( (!{sell}) ↑ OrderInfo.amount ) ) then { { _:UEf } } ; { _ } }} . 
(*  	 refine {{ dealer.sells_ -> pop () ; { _ } }} .  *)
 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	                            [ ok , 
                                    ((!{sell}) ↑ OrderInfo.amount) , 
                                    0 ] ; { _ } }} . 
 	 refine {{ if ( (#{sell_idx}) == !{sell_idx_cur} ) then { { _:UEf } } ; { _ } }} . 
 	 	 refine {{ (* dealer.ret_ *) {ret} := !{ ret } }} . 
(*  	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { true } ) ; { _ } }} .  *)
 	 refine {{ ({sell_opt}) -> reset () }} . 
 refine {{ if ( ~ ((!{buy}) ↑ OrderInfo.amount ) ) then { { _:UEf } } }} . 
 	 refine {{  (* dealer.buys_ . pop () *) ({sell_opt}) -> reset () ; { _ } }} . 
 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	                          [ ok , 
                                    ((!{buy}) ↑ OrderInfo.amount) , 
                                    0 ] ; { _ } }} . 
 	 refine {{ if ( (#{buy_idx}) == !{buy_idx_cur} ) then { { _:UEf } } ; { _ } }} . 
 	 	 refine {{ (* dealer.ret_ *) {ret} := !{ ret } }} .
(*  	 refine {{ IPriceCallbackPtr ( buy . client_addr ) ( Grams ( buy . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { false } ) ; { _ } }} .  *)
 	 refine {{ {buy_opt} -> reset () }} .
 refine {{ if (  ?(!{sell_opt}) && ?((second ( (!{sell_opt}) -> get () )) ↑ OrderInfo.amount) ) 
                         then { { _:UEt } } ; { _ } }} . 
 	 refine {{ new 'sell : OrderInfoLRecord @ "sell" 
                         := second ( (!{sell_opt}) -> get () ) ; { _ } }} . 
  	(*  refine {{ _sells_ -> change_front ( sell ) ; { _ } }} . *)
 	 refine {{ if ( (#{sell_idx}) == ( first ((!{sell_opt}) -> get ()) ) ) 
                           then { { _:UEf } } }} . 
refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := {} ; { _ } }} . (* TODO: delete *)
 	 	 refine {{ (* dealer.ret_ *) {ret}
 	 	 	                       :=   [ ok , 
                                    ((!{sell}) ↑ OrderInfo.original_amount) -
                                    ((!{sell}) ↑ OrderInfo.amount) , 
                                     (!{sell}) ↑ OrderInfo.amount ] }} . 
 refine {{ if ( ? !{buy_opt} && ? ((second ( (!{buy_opt}) -> get () )) ↑ OrderInfo.amount) ) 
                         then { { _:UEt } } }} .  
 	 refine {{ new 'buy : OrderInfoLRecord @ "buy" 
                         := second ( (!{buy_opt}) -> get () ) ; { _ } }} . 
(*  	 refine {{ buys_ -> change_front ( sell ) ; { _ } }} .  *)
 	 refine {{ if ( (#{buy_idx}) == ( first ((!{buy_opt}) -> get ()) ) ) 
                           then { { _:UEf } } }} . 
refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := {} ; { _ } }} . (* TODO: delete *)
 	 	 refine {{ (* dealer.ret_ *) {ret}
 	 	 	                       :=   [ ok , 
                                    ((!{buy}) ↑ OrderInfo.original_amount) -
                                    ((!{buy}) ↑ OrderInfo.amount) , 
                                     (!{buy}) ↑ OrderInfo.amount ] }} . 
Defined.

 Definition process_queue_left { R a1 a2 }  
( sell_idx : URValue ( uint ) a1 ) 
( buy_idx : URValue ( uint ) a2 ) 
: UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) process_queue 
 sell_idx buy_idx ) . 
 
 Notation " 'process_queue_' '(' sell_idx ',' buy_idx ')' " := 
 ( process_queue_left 
 sell_idx buy_idx ) 
 (in custom ULValue at level 0 , sell_idx custom URValue at level 0 
 , buy_idx custom URValue at level 0 ) : ursus_scope . 

(* pair<address, Grams> int_sender_and_value() {
    address sender = int_sender();
    return { sender, int_value_ };
  }  *) 
(* Parameter int_sender : XAddress . *)
Parameter int_value_ : uint (*Grams*) .

Definition int_sender_and_value : UExpression ( XAddress # uint (*Grams*)) false .
  refine {{ new 'sender : XAddress @ "sender" := int_sender() ; { _ } }} .
  refine {{ return_ [ !{sender} , #{int_value_} ] }} .
Defined.

Definition int_sender_and_value_right : URValue ( XAddress # uint (*Grams*)) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) int_sender_and_value ) . 
 
 Notation " 'int_sender_and_value_' '(' ')' " := 
 ( int_sender_and_value_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

(* 
struct addr_var {
  bitconst<2, 0b11> kind;
  optional<anycast_info> Anycast;
  uint_t<9> addr_len;
  int32 workchain_id;
  dynamic_bitfield<&addr_var::addr_len> address;

  DEFAULT_EQUAL(addr_var)
};
using MsgAddressInt = variant<addr_std, addr_var>;
 void set_int_sender(lazy<MsgAddressInt> val) { 
    int_sender_ = val; } *)             
Parameter set_int_sender : UExpression OrderRetLRecord false .
Notation " 'set_int_sender_' '(' ')' " := 
 ( set_int_sender ) 
 (in custom ULValue at level 0 ) : ursus_scope . 

 Definition onTip3LendOwnershipMinValue : UExpression uint128 false . 
 	 	 refine {{ return_ ((_tons_cfg_ ↑ TonsConfig.process_queue) + 
                        (_tons_cfg_ ↑ TonsConfig.transfer_tip3) + 
                        (_tons_cfg_ ↑ TonsConfig.send_notify) + 
                        (_tons_cfg_ ↑ TonsConfig.return_ownership) + 
                        (_tons_cfg_ ↑ TonsConfig.order_answer) ) }} . 
 Defined . 
 Definition onTip3LendOwnershipMinValue_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) onTip3LendOwnershipMinValue 
 ) . 
 
 Notation " 'onTip3LendOwnershipMinValue_' '(' ')' " := 
 ( onTip3LendOwnershipMinValue_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition prepare_persistent_data { X Y } (persistent_data_header : X) 
                                           (base : Y): UExpression XCell false .
 refine {{ return_ {} }} .  
Defined .

Definition prepare_persistent_data_right { X Y a1 a2 }  
                                    ( persistent_data_header : URValue ( X ) a1 ) 
                                    ( base : URValue ( Y ) a2 ) 
               : URValue ( XCell ) (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args ( LedgerableWithArgs:= λ2 ) prepare_persistent_data 
persistent_data_header base ) . 
 
 Notation " 'prepare_persistent_data_' '(' a ',' b ')' " := 
 ( prepare_persistent_data_right 
 a b ) 
 (in custom URValue at level 0 , 
   a custom URValue at level 0 
 , b custom URValue at level 0 ) : ursus_scope . 
 
 Definition prepare_internal_wallet_state_init_and_addr 
( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  ( uint8 ) )
 ( root_public_key :  ( uint256 ) )
 ( wallet_public_key :  ( uint256 ) ) 
( root_address :  ( XAddress ) ) 
( owner_address :  ( XMaybe XAddress ) ) 
( code :  ( XCell ) ) 
( workchain_id :  ( uint8 ) ) 
: UExpression ( StateInitLRecord * uint256 ) false .
 	 	 refine {{ new 'wallet_data : ( TONTonkenWalletModuleForPrice.DTONTokenWalletInternalLRecord ) @ "wallet_data" := 
                 [ #{name} , #{symbol} , #{decimals} , 0 , #{root_public_key} , 
                   #{wallet_public_key} , #{root_address} , #{owner_address} , 
                   {} , #{code} , #{workchain_id} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_data_cl : ( XCell ) @ "wallet_data_cl" := 
               prepare_persistent_data_ ( {} , !{wallet_data} ) ; { _ } }} . 
 	 	 refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 
              [ {} , {} , (#{code}) -> set () , (!{wallet_data_cl}) -> set () , {} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_init_cl : ( XCell ) @ "wallet_init_cl" := {}  
 	 	            (*  build ( !{ wallet_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ wallet_init } ,  tvm_hash ( !{wallet_init_cl} )  ] }} . 
 Defined . 

 Definition prepare_internal_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( uint8 ) a3 ) ( root_public_key : URValue ( uint256 ) a4 ) ( wallet_public_key : URValue ( uint256 ) a5 ) ( root_address : URValue ( XAddress ) a6 ) ( owner_address : URValue ( XMaybe XAddress ) a7 ) ( code : URValue ( XCell ) a8 ) ( workchain_id : URValue ( uint8 ) a9 ) : URValue ( StateInitLRecord * uint256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_internal_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_internal_wallet_state_init_and_addr_' '(' name ',' symbol ',' decimals ',' root_public_key ',' wallet_public_key ',' root_address ',' owner_address ',' code ',' workchain_id ')' " := 
 ( prepare_internal_wallet_state_init_and_addr_right 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 
 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 
 , root_public_key custom URValue at level 0 
 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , code custom URValue at level 0 
 , workchain_id custom URValue at level 0 ) : ursus_scope . 


 Definition expected_wallet_address ( wallet_pubkey : ( uint256 ) ) ( internal_owner : ( uint256 ) ) : UExpression uint256 false . 
 	 	 refine {{ new 'owner_addr : ( XMaybe XAddress ) @ "owner_addr" := {} ; { _ } }} . 
 	 	 refine {{ if ( #{internal_owner} ) then { { _:UEf } } ; { _ } }} .
 	 	 	 refine {{ {owner_addr} := {} (* Address :: make_std ( workchain_id_ , !{ internal_owner } ) *) }} . 
 	 	 refine {{ return_ second ( prepare_internal_wallet_state_init_and_addr_ (
           _tip3cfg_ ↑ Tip3Config.name , 
           _tip3cfg_ ↑ Tip3Config.symbol , 
           _tip3cfg_ ↑ Tip3Config.decimals , 
           _tip3cfg_ ↑ Tip3Config.root_public_key , 
           #{ wallet_pubkey } , 
           _tip3cfg_ ↑ Tip3Config.root_address , 
           !{owner_addr} ,  
           _tip3_code_ ,
           _workchain_id_
            ) ) }} . 
 Defined . 
 
 Definition expected_wallet_address_right { a1 a2 }  ( wallet_pubkey : URValue ( uint256 ) a1 ) ( internal_owner : URValue ( uint256 ) a2 ) : URValue uint256 ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) expected_wallet_address 
 wallet_pubkey internal_owner ) . 
 
 Notation " 'expected_wallet_address_' '(' wallet_pubkey ',' internal_owner ')' " := 
 ( expected_wallet_address_right 
 wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope .

Definition verify_tip3_addr ( tip3_wallet : ( XAddress ) ) ( wallet_pubkey : ( uint256 ) ) ( internal_owner : ( uint256 ) ) : UExpression XBool false . 
 	 	 refine {{ new 'expected_address : ( uint256 ) @ "expected_address" := 
          expected_wallet_address_ ( #{ wallet_pubkey } , #{ internal_owner } ) ; { _ } }} . 
 	 	 refine {{ return_ (* Std :: get < addr_std > ( !{ tip3_wallet } ( ) ) . address *) 1 == !{expected_address} }} . 
Defined . 

 Definition verify_tip3_addr_right { a1 a2 a3 }  ( tip3_wallet : URValue ( XAddress ) a1 ) ( wallet_pubkey : URValue ( uint256 ) a2 ) ( internal_owner : URValue ( uint256 ) a3 ) : URValue XBool ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) verify_tip3_addr 
 tip3_wallet wallet_pubkey internal_owner ) . 
 
 Notation " 'verify_tip3_addr_' '(' tip3_wallet ',' wallet_pubkey ',' internal_owner ')' " := 
 ( verify_tip3_addr_right 
 tip3_wallet wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , tip3_wallet custom URValue at level 0 
 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope . 

Parameter set_int_return_flag :UExpression OrderRetLRecord false .
Notation " 'set_int_return_flag_' '(' ')' " := 
 ( set_int_return_flag ) 
 (in custom ULValue at level 0 ) : ursus_scope .

Parameter int_value__ : URValue uint false .
Notation " 'int_value' '(' ')' " := 
 ( int_value__ ) 
 (in custom URValue at level 0 ) : ursus_scope .

Definition on_sell_fail ( ec : ( uint ) ) 
( wallet_in : ( XAddress (* ITONTokenWalletPtrLRecord *) ) ) 
( amount : ( uint128 ) ) : UExpression OrderRetLRecord false . 
 	 (* wallet_in(Grams(tons_cfg_.return_ownership.get())).returnOwnership(amount);  *)
 	 refine {{ if ( ( _sells_ -> empty () ) && ( _buys_ -> empty () ) )
             then { { _: UExpression OrderRetLRecord false } } 
             else { { _: UExpression OrderRetLRecord false } } ; { _ } }} .
 	 	 refine {{ set_int_return_flag_  ( ) (* SEND_ALL_GAS | DELETE_ME_IF_I_AM_EMPTY *) }} . 
 	 refine {{ new 'incoming_value : uint @ "incoming_value" := int_value ( ) (* ( ) . get ( ) *) ; { _ } }} . 
  	 refine {{ tvm.rawreserve ( tvm.balance () - !{incoming_value} , rawreserve_flag::up_to ) ; { _ } }} .
 	 refine {{ set_int_return_flag_ ( ) (* SEND_ALL_GAS *) }} . 
 refine {{ return_ [ #{ec} , {} , {} ] }} . 
Defined . 

 Definition on_sell_fail_right { a1 a2 a3 }  ( ec : URValue ( uint ) a1 ) ( wallet_in : URValue ( XAddress (* ITONTokenWalletPtrLRecord *) ) a2 ) ( amount : URValue ( uint128 ) a3 ) : URValue OrderRetLRecord ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) on_sell_fail 
 ec wallet_in amount ) . 
 
 Notation " 'on_sell_fail_' '(' ec ',' wallet_in ',' amount ')' " := 
 ( on_sell_fail_right 
 ec wallet_in amount ) 
 (in custom URValue at level 0 , ec custom URValue at level 0 
 , wallet_in custom URValue at level 0 
 , amount custom URValue at level 0 ) : ursus_scope .

 Definition process_queue_impl 
( tip3root : ( XAddress ) ) 
( notify_addr : ( XAddress (* IFlexNotifyPtrLRecord *) ) ) 
( price : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) 
( tons_cfg : ( TonsConfigLRecord ) ) 
( sell_idx : ( uint ) ) 
( buy_idx : ( uint ) ) 
( sells_amount : ( uint128 ) ) 
( sells : ( XQueue OrderInfoLRecord ) ) 
( buys_amount : ( uint128 ) ) 
( buys : ( XQueue OrderInfoLRecord ) ) 
: UExpression process_retLRecord true . 
 	 	 refine {{ new 'd : ( dealerLRecord ) @ "d" := 	 	 
 	 	 	 [ #{tip3root} , #{notify_addr} , #{price} , #{deals_limit} , #{tons_cfg} ,
           #{sells_amount} , #{sells} , #{buys_amount} , #{buys} , {} ] ; { _ } }} . 
 	 	 refine {{ process_queue_ ( #{sell_idx} , #{buy_idx} ) ; { _ } }} . 
 	 	 refine {{ return_ [ (!{d}) ↑ dealer.sells_amount_ , 
                         (!{d}) ↑ dealer.sells_ , 
                         (!{d}) ↑ dealer.buys_amount_ , 
                         (!{d}) ↑ dealer.buys_ , 
                         (!{d}) ↑ dealer.ret_ ] }} . 
 Defined . 

 Definition process_queue_impl_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 } 
 ( tip3root : URValue ( XAddress ) a1 ) 
( notify_addr : URValue ( XAddress (* IFlexNotifyPtrLRecord *) ) a2 ) 
( price : URValue ( uint128 ) a3 ) 
( deals_limit : URValue ( uint8 ) a4 ) 
( tons_cfg : URValue ( TonsConfigLRecord ) a5 ) 
( sell_idx : URValue ( uint ) a6 ) 
( buy_idx : URValue ( uint ) a7 ) 
( sells_amount : URValue ( uint128 ) a8 ) 
( sells : URValue ( XQueue OrderInfoLRecord ) a9 ) 
( buys_amount : URValue ( uint128 ) a10 ) 
( buys : URValue ( XQueue OrderInfoLRecord ) a11 ) : 
  URValue process_retLRecord true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ11 ) process_queue_impl 
 tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) . 
 
 Notation " 'process_queue_impl_' '(' tip3root ',' notify_addr ',' price ',' deals_limit ',' tons_cfg ',' sell_idx ',' buy_idx ',' sells_amount ',' sells ',' buys_amount ',' buys ')' " := 
 ( process_queue_impl_right 
 tip3root notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) 
 (in custom URValue at level 0 , tip3root custom URValue at level 0 
 , notify_addr custom URValue at level 0 
 , price custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_cfg custom URValue at level 0 
 , sell_idx custom URValue at level 0 
 , buy_idx custom URValue at level 0 
 , sells_amount custom URValue at level 0 
 , sells custom URValue at level 0 
 , buys_amount custom URValue at level 0 
 , buys custom URValue at level 0 ) : ursus_scope . 


Definition onTip3LendOwnership ( answer_addr : ( XAddress ) ) ( balance : ( uint128 ) ) ( lend_finish_time : ( uint32 ) ) ( pubkey : ( uint256 ) ) ( internal_owner : ( XAddress ) ) ( payload : ( XCell ) ) : UExpression OrderRetLRecord true . 
 	 	 refine {{ new ( 'tip3_wallet : XAddress , 'value : uint (*Grams*) ) 
                     @ ( "tip3_wallet" , "value" ) := 
                                        int_sender_and_value_ ( ) ; { _ } }} . 
(*  	 	 refine {{ ITONTokenWalletPtr wallet_in ( tip3_wallet ) ; { _ } }} .  *)
refine {{ new 'wallet_in : XAddress @ "wallet_in" := {} ; { _ } }} .
 	 	 refine {{ new 'ret_owner_gr : uint(*Grams*) @ "ret_owner_gr" :=
              ( _tons_cfg_ ↑ TonsConfig.return_ownership ) ; { _ } }} . 
 	 	 refine {{ set_int_sender_ ( ) (* answer_addr *) ; { _ } }} . 
(*  	 	 refine {{ set_int_return_value ( tons_cfg_ . order_answer . get ( ) ) ; { _ } }} .  *)
 	 	 refine {{ new 'min_value : ( uint128 ) @ "min_value" := 
                              onTip3LendOwnershipMinValue_ ( ) ; { _ } }} . 
 	 	 refine {{ new 'args : ( SellArgsLRecord ) @ "args" := {} 
                          (* parse ( payload . ctos ( ) )  *) ; { _ } }} . 
 	 	 refine {{ new 'amount : ( uint128 ) @ "amount" := 
                               (!{args}) ↑ SellArgs.amount ; { _ } }} . (*TODO - test the type!*)
 	 	 refine {{ new 'err : ( uint ) @ "err" := 0 ; { _ } }} . 

 	 	 refine {{ if ( !{value} < !{ min_value } ) 
                  then { { _:UExpression OrderRetLRecord false } } ; { _ } }} . 
 	 	 	 refine {{ {err} := ec::not_enough_tons_to_process }} . 
 	 	 refine {{ if ( ~ (verify_tip3_addr_ ( !{ tip3_wallet } , 
                                           #{ pubkey } , 
                       {} (* ( std::get<addr_std>( internal_owner.val ( ) ).address ) *) ) ) )
                            then { { _:UExpression OrderRetLRecord false } }  ; { _ } }} . 
 	 	 	 refine {{ {err} := ec::unverified_tip3_wallet }} . 
 	 	 refine {{ if ( !{ amount } < _min_amount_ ) 
                 then { { _:UExpression OrderRetLRecord false } } ; { _ } }} . 
 	 	 	 refine {{ {err} := ec::not_enough_tokens_amount }} . 
 	 	 refine {{ if ( (#{balance}) < !{amount} ) 
                 then { { _:UExpression OrderRetLRecord false } } ; { _ } }} . 
 	 	 	 refine {{ { err } := ec::too_big_tokens_amount }} . 
 	 	 refine {{ if ( ~ ( calc_cost_ ( !{amount} , _price_ ) ) ) 
                      then { { _:UExpression OrderRetLRecord false } } ; { _ } }} . 
 	 	 	 refine {{ {err} := ec::too_big_tokens_amount }} . 
 	 	 refine {{ if ( ~ ( is_active_time_ ( #{ lend_finish_time } ) ) ) 
                      then { { _:UExpression OrderRetLRecord false } } ; { _ } }} . 
 	 	 	 refine {{ {err} := ec::expired }} . 
 	 	 refine {{ if ( !{err} ) then { { _:UExpression OrderRetLRecord false } } ; { _ } }} . 
 	 	 	 refine {{ return_ ( on_sell_fail_ ( !{err} , !{wallet_in} , !{ amount } ) ) }} . 
 	 	 refine {{ new 'account : ( uint128 ) @ "account" := 
            (!{value}) - (_tons_cfg_ ↑ TonsConfig.process_queue) 
                       - (_tons_cfg_ ↑ TonsConfig.order_answer ); { _ } }} . 
 	 	 refine {{ new 'sell : ( OrderInfoLRecord ) @ "sell" := 	 	 
 	 	 	 [ !{amount} , !{amount} , !{account} , (* !{tip3_wallet} *) {} , 
        (* ((!{args}) ↑ SellArgs.receive_wallet) *) {} , #{lend_finish_time} ] ; { _ } }} . (*TODO!*)
 	 	 refine {{ _sells_ -> push ( !{sell} ) ; { _ } }} . 
 	 	 refine {{ _sells_amount_ += ((!{sell}) ↑ OrderInfo.amount) ; { _ } }} . 
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderAdded ( bool_t { true } , tip3cfg_ . root_address , price_ , sell . amount , sells_amount_ ) ; { _ } }} .  *)
 	 	 refine {{ new ('sells_amount:uint128 , 
                    'sells:( XQueue OrderInfoLRecord ) , 
                    'buys_amount:uint128 , 
                    'buys:(XQueue OrderInfoLRecord) , 
                    'ret:(XMaybe OrderRetLRecord) ) @
                   ( "sells_amount" , "sells" , "buys_amount" , "buys" , "ret" ) :=
               process_queue_impl_ ( _tip3cfg_ ↑ Tip3Config.root_address , 
                                     _notify_addr_ , 
                                     _price_ , 
                                     _deals_limit_ , 
                                     _tons_cfg_ , 
                                     first ( _sells_ -> back_with_idx ()) , 
                                     0 , 
                                     _sells_amount_ , 
                                     _sells_ , 
                                     _buys_amount_ , 
                                     _buys_ ) ; { _ } }} .
 	 	 refine {{ _sells_ := !{sells} ; { _ } }} . 
 	 	 refine {{ _buys_ := !{buys} ; { _ } }} . 
 	 	 refine {{ _sells_amount_ := !{ sells_amount } ; { _ } }} . 
 	 	 refine {{ _buys_amount_ := !{buys_amount} ; { _ } }} . 
 	 	 refine {{ if ( (_sells_  -> empty ()) && ( _buys_ -> empty () ) )
              then { { _:UExpression OrderRetLRecord false } } ; { _ } }} . 
 	 	 	 refine {{ {buys_amount} := !{buys_amount} (* suicide ( _flex_ ) *) }} . 
 	 	 refine {{ if ( !{ret} ) then { { _:UEt } } ; { _ } }} . 
 	 	 	 refine {{ return_ (!{ret}) -> get () }} .
 
 	 	 refine {{ return_ [ ok , 0 , (!{sell}) ↑ OrderInfo.amount ] }} . 
Defined .

 Definition buyTip3MinValue ( buy_cost : ( uint128 ) ) : UExpression uint128 false . 
 	 	 refine {{ return_ (#{buy_cost}) + ( _tons_cfg_ ↑ TonsConfig.process_queue ) 
                                     + ( _tons_cfg_ ↑ TonsConfig.transfer_tip3 )
                                     + ( _tons_cfg_ ↑ TonsConfig.send_notify )
                                     + ( _tons_cfg_ ↑ TonsConfig.order_answer ) }} . 
 Defined . 

 Definition buyTip3MinValue_right { a1 }  ( buy_cost : URValue ( uint128 ) a1 ) : URValue uint128 a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) buyTip3MinValue 
 buy_cost ) . 
 
 Notation " 'buyTip3MinValue_' '(' buy_cost ')' " := 
 ( buyTip3MinValue_right 
 buy_cost ) 
 (in custom URValue at level 0 , buy_cost custom URValue at level 0 ) : ursus_scope . 

(* void set_int_return_value(unsigned val) { int_return_value_ = val; } *)
Parameter set_int_return_value : UExpression PhantomType false .
Notation " 'set_int_return_value_' '(' ')' " := 
 ( set_int_sender ) 
 (in custom ULValue at level 0 ) : ursus_scope .

Definition buyTip3 ( amount : ( uint128 ) ) ( receive_tip3_wallet : ( XAddress ) ) ( order_finish_time : ( uint32 ) ) : UExpression OrderRetLRecord true . 
 	 	 refine {{ new ( 'sender:XAddress , 'value_gr:uint ) @ ( "sender" , "value_gr" ) := int_sender_and_value_ ( ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( (#{ amount }) >= _min_amount_ ) , 1 (* ec::not_enough_tokens_amount *) ) ; { _ } }} . 
 	 	 refine {{ new 'cost : ( ( XMaybe uint ) ) @ "cost" := 
                         calc_cost_ ( #{ amount } , _price_ ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( !{cost} ) , ec::too_big_tokens_amount ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( (!{value_gr}) > buyTip3MinValue_ ( (!{cost}) -> get_default () ) ) , 
                              ec::not_enough_tons_to_process ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( is_active_time_ ( #{ order_finish_time } ) ) , 1 (* ec::expired *) ) ; { _ } }} . 
 	 	 refine {{ set_int_return_value_ ( ) (* tons_cfg_ . order_answer . get ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'account : ( uint128 ) @ "account" := 
               (!{value_gr}) - (_tons_cfg_ ↑ TonsConfig.process_queue) 
                             - (_tons_cfg_ ↑ TonsConfig.order_answer) ; { _ } }} . 

 	 	 refine {{ new 'buy : ( OrderInfoLRecord ) @ "buy" := 	 	 
                  [ #{amount} , #{amount} , !{account} , {} (* #{receive_tip3_wallet} *)  , 
(*TODO cannot unify "XAddress" and "addr_std_fixedLRecord"*)
                    (* !{sender} *) {} , #{order_finish_time} ] ; { _ } }} . 

 	 	 refine {{ _buys_ -> push ( !{buy} ) ; { _ } }} . 
 	 	 refine {{ _buys_amount_ += ( ( !{buy} ) ↑ OrderInfo.amount ) ; { _ } }} . 
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderAdded ( bool_t { false } , tip3cfg_ . root_address , price_ , buy . amount , buys_amount_ ) ; { _ } }} .  *)
 	 	 refine {{ new ('sells_amount:uint128 , 
                    'sells:( XQueue OrderInfoLRecord ) , 
                    'buys_amount:uint128 , 
                    'buys:(XQueue OrderInfoLRecord) , 
                    'ret:(XMaybe OrderRetLRecord) ) @
                   ( "sells_amount" , "sells" , "buys_amount" , "buys" , "ret" ) :=
              process_queue_impl_ ( _tip3cfg_ ↑ Tip3Config.root_address , 
                                     _notify_addr_ , 
                                     _price_ , 
                                     _deals_limit_ , 
                                     _tons_cfg_ , 
                                     0 , 
                                     first ( _buys_ -> back_with_idx () ) , 
                                     _sells_amount_ , 
                                     _sells_ , 
                                     _buys_amount_ , 
                                     _buys_ ) ; { _ } }} .
 	 	 refine {{ _sells_ := !{sells} ; { _ } }} . 
 	 	 refine {{ _buys_ := !{buys} ; { _ } }} . 
 	 	 refine {{ _sells_amount_ := !{ sells_amount } ; { _ } }} . 
 	 	 refine {{ _buys_amount_ := !{buys_amount} ; { _ } }} . 
 	 	 refine {{ if ( ( _sells_ -> empty () ) && ( _buys_ -> empty () ) ) 
                 then { { _: UExpression _ false } } ; { _ } }} . 
 	 	 	 refine {{ _sells_amount_ := !{ sells_amount } (* suicide ( _flex_ ) *) }} . 
 	 	 refine {{ if ( !{ret} ) then { { _: UEt } } ; { _ } }} . 
 	 	 	 refine {{ return_ (!{ret}) -> get () }} . 
 	 	 refine {{ return_ [ ok , 0 , (!{buy}) ↑ OrderInfo.amount ] }} . 
Defined . 
 
Definition processQueue : UExpression PhantomType true . 
 	 	 refine {{ if ( (_sells_ -> empty ()) \\ ( _buys_ -> empty () ) ) 
                 then { { _: UEf } } ; { _ } }} . 
 	 	 	 refine {{ return_ {} }} . 
 	 	 refine {{ new ('sells_amount:uint128 , 
                    'sells:( XQueue OrderInfoLRecord ) , 
                    'buys_amount:uint128 , 
                    'buys:(XQueue OrderInfoLRecord) , 
                    'ret:(XMaybe OrderRetLRecord) ) @
                   ( "sells_amount" , "sells" , "buys_amount" , "buys" , "ret" ) :=
              process_queue_impl_ ( _tip3cfg_ ↑ Tip3Config.root_address , 
                                     _notify_addr_ , 
                                     _price_ , 
                                     _deals_limit_ , 
                                     _tons_cfg_ , 
                                     0 , 
                                     0 , 
                                     _sells_amount_ , 
                                     _sells_ , 
                                     _buys_amount_ , 
                                     _buys_ ) ; { _ } }} .
 	 	 refine {{ _sells_ := !{sells} ; { _ } }} . 
 	 	 refine {{ _buys_ := !{buys} ; { _ } }} . 
 	 	 refine {{ _sells_amount_ := !{ sells_amount } ; { _ } }} . 
 	 	 refine {{ _buys_amount_ := !{buys_amount} ; { _ } }} . 
 	 	 refine {{ if ( ( _sells_ -> empty () ) && ( _buys_ -> empty () ) ) 
                  then { { _: UExpression PhantomType false } } }} . 
 	 	 	 refine {{ _sells_amount_ := !{ sells_amount } (* suicide ( flex_ ) *) }} .
Defined . 

 Definition cancel_order_impl 
( orders : ( XQueue OrderInfoLRecord ) ) 
( client_addr : ( addr_std_fixedLRecord ) ) 
( all_amount : ( uint128 ) ) 
( sell : ( XBool ) ) 
( return_ownership : ( uint(* Grams *) ) ) 
( process_queue : ( uint(* Grams *) ) ) 
( incoming_val : ( uint(* Grams *) ) ) 
: UExpression ((XQueue OrderInfoLRecord) # uint128) false . 
 	 	 refine {{ new 'is_first : ( XBool ) @ "is_first" := TRUE ; { _ } }} . 
 	 	 refine {{ new 'it : ( XQueue OrderInfoLRecord ) @ "it" := {} ; { _ } }} . 
 	 	(*  refine {{ for ( {it} = orders -> begin () ; ~ ({it} != orders -> end ()) ) { { _ } } ; { _ } }} . 
 	 	 	 refine {{ new 'next_it : OrderInfoLRecord @ "next_it" := std : : next ( it ) ; { _ } }} . 
 	 	 	 refine {{ new 'ord : ( OrderInfoLRecord ) @ "ord" := *it ; { _ } }} . 
 	 	 	 refine {{ if ( ({ord} ↑ OrderInfo.client_addr) == !{client_addr} ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ new 'minus_val : XUInteger @ "minus_val" := !{is_first} ? #{process_queue} : 0 ; { _ } }} . 
 	 	 	 	 refine {{ if ( #{sell} ) then { { _:UEf } } ; { _ } }} . 
(*  	 	 	 refine {{ { ITONTokenWalletPtr ( ord . tip3_wallet ) ( return_ownership ) . returnOwnership ( ord . amount ) ; { _ } }} .  *)
 	 	 	 	 	 refine {{ {minus_val} += (#{return_ownership}) }} . 
 	 	 	 refine {{ new 'plus_val : ( XUInteger ) @ "plus_val" := 
                      (((!{ord}) ↑ OrderInfo.account) + ( !{is_first} ? (#{incoming_val}) : 0 )) ; { _ } }} . 
 	 	 	 refine {{ {is_first} := FALSE ; { _ } }} . 
 	 	 	 refine {{ if ( !{plus_val} > !{minus_val} ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ new 'ret_val : XUInteger @ "ret_val" := (!{plus_val} - !{minus_val}) ; { _ } }} . 
 	 	 	 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 	 	 	 
 	 	 	                          [$ ec::canceled , !{ord} ↑ OrderInfo.original_amount 
                                                - !{ord} ↑ OrderInfo.amount, 0 $] (* ; { _ } }} . 
 	 	 	 	 refine {{ IPriceCallbackPtr ( ord . client_addr ) ( Grams ( ret_val ) ) . onOrderFinished ( ret , sell ) *) }} . 
 	 	 refine {{ {all_amount} -= !{ord} ↑ OrderInfo.amount ; { _ } }} . 
 	 	 refine {{ {orders} -> erase ( it ) }} . 
   refine {{ {it} := !{next_it} }} .  *)
 refine {{ return_ [ #{ orders } , #{ all_amount } ] }} . 
Defined . 

 Definition cancel_order_impl_right { a1 a2 a3 a4 a5 a6 a7 }  
( orders : URValue ( XQueue OrderInfoLRecord ) a1 ) 
( client_addr : URValue ( addr_std_fixedLRecord ) a2 ) 
( all_amount : URValue ( uint128 ) a3 ) 
( sell : URValue ( XBool ) a4 ) 
( return_ownership : URValue ( uint (* Grams *) ) a5 ) 
( process_queue : URValue ( uint (* Grams *) ) a6 ) 
( incoming_val : URValue ( uint (* Grams *) ) a7 ) 
: URValue ((XQueue OrderInfoLRecord) # uint128)
 ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancel_order_impl 
 orders client_addr all_amount sell return_ownership process_queue incoming_val ) . 
 
 Notation " 'cancel_order_impl_' '(' orders ',' client_addr ',' all_amount ',' sell ',' return_ownership ',' process_queue ',' incoming_val ')' " := 
 ( cancel_order_impl_right 
 orders client_addr all_amount sell return_ownership process_queue incoming_val ) 
 (in custom URValue at level 0 , orders custom URValue at level 0 
 , client_addr custom URValue at level 0 
 , all_amount custom URValue at level 0 
 , sell custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , process_queue custom URValue at level 0 
 , incoming_val custom URValue at level 0 ) : ursus_scope . 

Definition cancelSell : UExpression PhantomType false . 
 	 	 refine {{ new 'canceled_amount : ( uint128 ) @ "canceled_amount" := _sells_amount_ ; { _ } }} . 
 	 	 refine {{ new 'client_addr : ( addr_std_fixedLRecord ) @ "client_addr" := 
                            {} (* int_sender_ ( )  *); { _ } }} . 
 	 	 refine {{ new 'value : ( uint ) @ "value" := 
                               int_value ( ) ; { _ } }} . 
 	 	 refine {{ new ( 'sells : (XQueue OrderInfoLRecord) , 'sells_amount : uint128 )
                 @ ( "sells" , "sells_amount" ) :=
                cancel_order_impl_ ( _sells_ , !{client_addr} , _sells_amount_ , TRUE , 
                   _tons_cfg_ ↑ TonsConfig.return_ownership , 
                   _tons_cfg_ ↑ TonsConfig.process_queue , 
                   !{value} ) ; { _ } }} . 
 	 	 refine {{ _sells_ := !{ sells } ; { _ } }} . 
 	 	 refine {{ _sells_amount_ := !{sells_amount} ; { _ } }} . 
 	 	 refine {{ {canceled_amount} -= !{sells_amount} ; { _ } }} . 
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderCanceled ( bool_t { true } , tip3cfg_ . root_address , price_ , canceled_amount , sells_amount_ ) ; { _ } }} .  *)
 	 	 refine {{ if ( ( _sells_ -> empty () ) && ( _buys_ -> empty () ) ) 
                    then { { _: UExpression PhantomType false } } }} . 
 	 	 	 refine {{ {value} := !{value} (* suicide ( _flex_ ) *) }} . 
Defined . 
 
Definition cancelBuy : UExpression PhantomType false . 
 	 	 refine {{ new 'canceled_amount : ( uint128 ) @ "canceled_amount" := 
                             _buys_amount_ ; { _ } }} . 
 	 	 refine {{ new 'client_addr : ( addr_std_fixedLRecord ) @ "client_addr" := {} 
                             (* int_sender ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'value : ( uint ) @ "value" := 
                         int_value ( ) ; { _ } }} . 
 	 	 refine {{ new ( 'buys:(XQueue OrderInfoLRecord) , 'buys_amount:uint128 ) 
                       @ ( "buys" , "buys_amount" ) :=
               cancel_order_impl_ ( _buys_ , !{client_addr} , _buys_amount_ , FALSE , 
                   _tons_cfg_ ↑ TonsConfig.return_ownership , 
                   _tons_cfg_ ↑ TonsConfig.process_queue , 
                   !{value} ) ; { _ } }} . 
 	 	 refine {{ _buys_ := !{ buys } ; { _ } }} . 
 	 	 refine {{ _buys_amount_ := !{buys_amount} ; { _ } }} . 
 	 	 refine {{ { canceled_amount } -= !{buys_amount} ; { _ } }} . 
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderCanceled ( bool_t { false } , tip3cfg_ . root_address , price_ , canceled_amount , buys_amount_ ) ; { _ } }} .  *)
 	 	 refine {{ if ( ( _sells_ -> empty () ) && ( _buys_ -> empty () ) ) 
                   then { { _: UExpression PhantomType false } } }} . 
 	 	 	 refine {{ _buys_ := !{ buys } (* suicide ( _flex_ ) *) }} . 
Defined . 

Definition getPrice : UExpression uint128 false . 
 	 	 refine {{ return_ _price_ }} . 
 Defined .

 Definition getPrice_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPrice 
 ) . 
 
 Notation " 'getPrice_' '(' ')' " := 
 ( getPrice_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getMinimumAmount : UExpression uint128 false . 
 	 	 refine {{ return_ _min_amount_ }} . 
 Defined . 
 
 Definition getMinimumAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getMinimumAmount 
 ) . 
 
 Notation " 'getMinimumAmount_' '(' ')' " := 
 ( getMinimumAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getTonsCfg : UExpression TonsConfigLRecord false . 
 	 	 refine {{ return_ _tons_cfg_ }} . 
 Defined . 
 
 Definition getTonsCfg_right  : URValue TonsConfigLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTonsCfg 
 ) . 
 
 Notation " 'getTonsCfg_' '(' ')' " := 
 ( getTonsCfg_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getSells : UExpression ( XHMap uint OrderInfoLRecord ) false . 
 	 	 refine {{ return_ {} (* dict_array ( sells_ . begin ( ) , sells_ . end ( ) ) *) }} . 
 Defined . 
 
 Definition getSells_right  : URValue ( XHMap uint OrderInfoLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSells 
 ) . 
 
 Notation " 'getSells_' '(' ')' " := 
 ( getSells_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getBuys : UExpression ( XHMap uint OrderInfoLRecord ) false . 
 	 	 refine {{ return_ {} (* dict_array ( buys_ . begin ( ) , buys_ . end ( ) ) *) }} . 
 Defined . 
 
Definition getSellAmount : UExpression uint128 false . 
 	 	 refine {{ return_ _sells_amount_ }} . 
 Defined . 
 
 Definition getSellAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSellAmount 
 ) . 
 
 Notation " 'getSellAmount_' '(' ')' " := 
 ( getSellAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getBuyAmount : UExpression uint128 false . 
 	 	 refine {{ return_ _buys_amount_ }} . 
 Defined . 
 
Definition getBuyAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuyAmount 
 ) . 
 
 Notation " 'getBuyAmount_' '(' ')' " := 
 ( getBuyAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope .
 
 
Definition _fallback ( x : ( XCell )) ( y : XSlice ): UExpression uint false . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
Definition getDetails : UExpression DetailsInfoLRecord false . 
 	 	 refine {{ return_ [ getPrice_ ( ) , getMinimumAmount_ ( ) , getSellAmount_ ( ) , getBuyAmount_ ( ) ] }} . 
 Defined . 
 
Definition prepare_price_state_init_and_addr ( price_data : ( DPriceLRecord ) ) ( price_code : ( XCell ) ) : UExpression ( StateInitLRecord * uint256 ) false . 
		refine {{ new 'price_data_cl : ( XCell ) @ "price_data_cl" := 
				prepare_persistent_data_ ( {} , #{price_data} ) ; { _ } }} . 
		refine {{ new 'price_init : ( StateInitLRecord ) @ "price_init" := 	 	 
			[ {} , {} , (#{price_code}) -> set () , 
						(!{price_data_cl}) -> set () , {} ] ; { _ } }} . 
		refine {{ new 'price_init_cl : ( XCell ) @ "price_init_cl" := {}
				(*  build ( !{ price_init } ) . make_cell ( ) *) ; { _ } }} . 
		refine {{ return_ [ !{ price_init } , tvm_hash ( !{price_init_cl} ) ] }} . 
Defined . 
 
End FuncsInternal.
End Funcs.








