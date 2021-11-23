Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
From elpi Require Import elpi.
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
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.PriceXchg.Ledger.
Require Import Contracts.PriceXchg.Functions.FuncSig.
Require Import Contracts.PriceXchg.Functions.FuncNotations.
Require Contracts.PriceXchg.Interface.

(*this elpi code move to the Ursus lib afterwards*)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.


(* Elpi Command AddLocalState.

Elpi Accumulate lp:{{

main [Name , Term, LocalStateFieldT] :-
  trm TrmInternal = Term,
  trm LocalStateField = LocalStateFieldT,
  str NameStr = Name,
  N is NameStr ^ "_j",
  coq.env.add-axiom N  (app [LocalStateField , TrmInternal]) _ , 
  coq.locate  N GR, 
  coq.TC.declare-instance GR 0,
  coq.say TrmInternal.
main _ :- coq.error "usage: AddLocalState <name> <term> <LocalStateField>".

}}.

Elpi Typecheck.
Elpi Export AddLocalState.

Elpi Command TestDefinitions. 
Elpi Accumulate lp:{{

pred get_name i:string , o:term.
get_name NameS NameG :-
    coq.locate NameS GR ,
    NameG = global GR . 

pred constructors_names i:string , o:list constructor.
constructors_names IndName Names :-
  std.assert! (coq.locate IndName (indt GR)) "not an inductive type",
  coq.env.indt GR _ _ _ _ Names _.

pred coqlist->list i:term, o: list term.
coqlist->list {{ [ ]%xlist }} [ ].
coqlist->list {{ (lp:X::lp:XS)%xlist }} [X | M] :- coqlist->list XS M.
coqlist->list X _ :- coq.say "error",
                    coq.say X.

main [ A ] :-
  coq.say  A. 
}}. 

Elpi Typecheck. *)
 
(* Module trainContractSpecModuleForFuncs := trainContractSpec XTypesModule StateMonadModule.
 *)
Module Type Has_Internal.

Parameter Internal: bool .

End Has_Internal.

Module Funcs (ha : Has_Internal)(dc : ConstsTypesSig XTypesModule StateMonadModule) .

Import ha.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

Export SpecModuleForFuncNotations(* ForFuncs *).CommonNotationsModule.

Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Definition transfer_tip3_right {b} (x: URValue TonsConfigLRecord b): URValue XUInteger b :=
    || {x} ^^ {TonsConfig_ι_transfer_tip3} || : _.

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.

Existing Instance xbool_default.

 Definition minor_cost ( amount : ( uint128 ) ) ( price : ( RationalPriceLRecord ) ) : UExpression (XMaybe uint128) false . 
 	 	 refine {{ new 'cost : ( uint ) @ "cost" := {} 
                   (* __builtin_tvm_muldivr ( amount ^^ uint128:get ( ) , price ^^ RationalPriceLRecord:num , price ^^ RationalPriceLRecord:denum ) *) ; { _ } }} . 
 	 	 refine {{ if ( ( ?((!{cost}) >> #{128})) \\ ( (!{cost}) == 0 ) ) 
               then { { _:UExpression (XMaybe uint128) false } } ; { _ } }} . 
 	 	 	 refine {{ return_ {} }} . 
 	 	 refine {{ return_ (!{ cost }) -> set ()  }} . 
Defined . 

 Definition minor_cost_right { a1 a2 }  ( amount : URValue ( uint128 ) a1 ) ( price : URValue ( RationalPriceLRecord ) a2 ) : URValue (XMaybe uint128) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) minor_cost 
 amount price ) . 
 
 Notation " 'minor_cost_' '(' amount ',' price ')' " := 
 ( minor_cost_right 
 amount price ) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom URValue at level 0 ) : ursus_scope . 


Definition account_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfoXchg_ι_account} || : _.

Definition account_left (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfoXchg_ι_account} }} : _.

Notation " a '↑' 'OrderInfoXchg.account' " := ( account_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfoXchg.account' " := ( account_left a ) (in custom ULValue at level 0) : ursus_scope.
  
Definition amount_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfoXchg_ι_account} || : _.

Definition amount_left (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfoXchg_ι_account} }} : _.

Notation " a '↑' 'OrderInfoXchg.amount' " := ( amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfoXchg.amount' " := ( amount_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition make_deal
 ( sell : ULValue ( OrderInfoXchgLRecord ) ) 
( buy : ULValue ( OrderInfoXchgLRecord ) ) 
: UExpression ( XBool # (XBool # uint128) ) false . 
 	 	 refine {{ new 'deal_amount : ( uint128 ) @ "deal_amount" := {}  
 	 	        (* std::min ( (#{sell}) ^^ OrderInfoLRecord.amount , (#{buy}) ^^ OrderInfoXchgLRecord.amount ) *) ; { _ } }} . 
 	 	 refine {{ new 'last_tip3_sell : ( XBool ) @ "last_tip3_sell" := (*TODO: OrderInfoXchg.amount - cannot infer type*)
                   ( !{deal_amount} == ((!{sell}) ↑ OrderInfoXchg.amount) ) ; { _ } }} .
 	 	 refine {{ new 'last_tip3_buy : ( XBool ) @ "last_tip3_buy" := 	 	 
                   ( !{deal_amount} == ( (!{buy}) ↑ OrderInfoXchg.amount ) ) ; { _ } }} .
 	 	 refine {{ new 'buy_payment : ( (XMaybe uint128) ) @ "buy_payment" := 
                minor_cost_ ( !{deal_amount} , _price_ ) ; { _ } }} . 
 	 	 refine {{ if ( ~ !{ buy_payment } ) then { { _: UExpression _ false } } ; { _ } }} . 
 	 	 	 refine {{ return_ [ TRUE , TRUE , 0 ] }} . 
 	 	 refine {{ new 'sell_ton_costs : ( uint128 ) @ "sell_ton_costs" := 0 ; { _ } }} . 
 	 	 refine {{ new 'buy_ton_costs : ( uint128 ) @ "buy_ton_costs" := 0 ; { _ } }} . 
 	 	 refine {{ new 'transaction_costs : ( uint128 ) @ "transaction_costs" := 
                ( (_tons_cfg_ ↑ TonsConfig.transfer_tip3) * #{2} ) + 
                  (_tons_cfg_ ↑ TonsConfig.send_notify) ; { _ } }} . 
 	 	 refine {{ if ( !{ last_tip3_sell } ) then { { _:UEf } } else { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ { sell_ton_costs } += !{ transaction_costs } }} . 
 	 	   refine {{ { buy_ton_costs } += !{ transaction_costs } }} . 
 	 	 refine {{ new 'sell_out_of_tons : ( XBool ) @ "sell_out_of_tons" := 
              (!{ sell_ton_costs } ) > ( (!{sell}) ↑ OrderInfoXchg.account ) ; { _ } }} . 
 	 	 refine {{ new 'buy_out_of_tons : ( XBool ) @ "buy_out_of_tons" := 
              ((!{buy}) ↑ OrderInfoXchg.account) < (!{ buy_ton_costs } ) ; { _ } }} . 
 	 	 refine {{ if ( !{ sell_out_of_tons } \\ !{ buy_out_of_tons } ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ return_ [ !{ sell_out_of_tons } , !{ buy_out_of_tons } , 0 ] }} . 
 	 	 refine {{ (({sell}) ↑ OrderInfoXchg.amount) -= !{deal_amount} ; { _ } }} . 
 	 	 refine {{ (({buy}) ↑ OrderInfoXchg.amount) -= !{deal_amount} ; { _ } }} . 
 	 	 refine {{ (({sell}) ↑ OrderInfoXchg.account) -= !{sell_ton_costs} ; { _ } }} . 
 	 	 refine {{ (({buy}) ↑ OrderInfoXchg.account) -= !{buy_ton_costs} ; { _ } }} . 
(*  	 	 refine {{ ITONTokenWalletPtr ( (#{sell}) ^^ OrderInfoXchg.tip3_wallet_provide ) ( Grams ( tons_cfg_ . transfer_tip3 . get ( ) ) ) . transfer ( sell . tip3_wallet_provide , buy . tip3_wallet_receive , deal_amount , uint128 ( 0 ) , bool_t { false } ) ; { _ } }} .  *)
(*  	 	 refine {{ ITONTokenWalletPtr ( buy . tip3_wallet_provide ) ( Grams ( tons_cfg_ . transfer_tip3 . get ( ) ) ) . transfer ( buy . tip3_wallet_provide , sell . tip3_wallet_receive , *buy_payment , uint128 ( 0 ) , bool_t { false } ) ; { _ } }} .  *)
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onXchgDealCompleted ( tip3root_sell_ , tip3root_buy_ , price_ . num , price_ . denom , deal_amount ) ; { _ } }} .  *)
 	 	 refine {{ return_ [ FALSE , FALSE , !{ deal_amount } ] }} . 
Defined . 

Notation "'λ2LL'" := (@UExpression_Next_LedgerableWithLArgs _ _ _ _ _( @UExpression_Next_LedgerableWithLArgs _ _ _ _ _ λ0)) (at level 0) : ursus_scope.
 
Definition make_deal_right  
( sell : ULValue ( OrderInfoXchgLRecord ) ) 
( buy : ULValue ( OrderInfoXchgLRecord ) ) 
: URValue ( XBool # (XBool # uint128) ) 
false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2LL ) make_deal 
 sell buy ) . 
 
 Notation " 'make_deal_' '(' sell buy ')' " := 
 ( make_deal_right 
 sell buy ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , buy custom URValue at level 0 ) : ursus_scope . 

 Definition is_active_time ( order_finish_time : ( uint32 ) ) : UExpression XBool false . 
 	 	 refine {{ return_ ( (tvm.now ()) + (#{300})(* safe_delay_period *) ) 
                            <  (#{order_finish_time}) }} . 
 Defined . 

 Definition is_active_time_right { a1 }  ( order_finish_time : URValue ( uint32 ) a1 ) : URValue XBool a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) is_active_time 
 order_finish_time ) . 
 
 Notation " 'is_active_time_' '(' order_finish_time ')' " := 
 ( is_active_time_right 
 order_finish_time ) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope .


Definition original_amount_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfoXchg_ι_original_amount} || : _.

Definition original_amount_left (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfoXchg_ι_original_amount} }} : _.

Notation " a '↑' 'OrderInfoXchg.original_amount' " := ( original_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfoXchg.original_amount' " := ( original_amount_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition order_finish_time_right {b} (x: URValue OrderInfoXchgLRecord b): URValue XUInteger128 b :=
|| {x} ^^ {OrderInfoXchg_ι_order_finish_time} || : _.

Definition order_finish_time_left (x: ULValue OrderInfoXchgLRecord): ULValue XUInteger128 :=
{{ {x} ^^ {OrderInfoXchg_ι_order_finish_time} }} : _.

Notation " a '↑' 'OrderInfoXchg.order_finish_time' " := ( order_finish_time_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'OrderInfoXchg.order_finish_time' " := ( order_finish_time_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition extract_active_order 
( cur_order : ULValue ( XMaybe (uint # OrderInfoXchgLRecord ) ) ) 
( orders : ULValue ( XQueue OrderInfoXchgLRecord ) ) 
( all_amount : ULValue ( uint128 ) ) 
( sell : ( XBool ) ) : 
UExpression ( (XMaybe ( uint # OrderInfoXchgLRecord )) # ( (XQueue OrderInfoXchgLRecord) # uint128 ) ) false . 
 	 	 refine {{ if ( !{ cur_order } ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ return_ [ !{cur_order} , !{orders} , !{all_amount} ] }} . 

 	 	 refine {{ while ( (!{orders}) -> empty () ) do { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ {cur_order} := {} (* orders...front_with_idx_opt ( ) *) ; { _ } }} . 
 	 	 	 refine {{ new 'ord : ( OrderInfoXchgLRecord ) @ "ord" := 
                      second ( (!{cur_order}) -> get_default () ) ; { _ } }} . 
 	 	 	 refine {{ if ( ~ ( is_active_time_ ( (!{ord}) ↑ OrderInfoXchg.order_finish_time ) ) ) 
                     then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ ({all_amount}) -= ((!{ord}) ↑ OrderInfoXchg.amount) ; { _ } }} . 
 	 	 	 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 	 	 	 
 	 	 	 [ 1 (* ec::expired *) , ((!{ord}) ↑ OrderInfoXchg.original_amount)
                              - ((!{ord}) ↑ OrderInfoXchg.amount) , 0 ] ; { _ } }} . 
(*  	 	 	 	 refine {{ IPriceCallbackPtr ( ord . client_addr ) ( Grams ( ord . account . get ( ) ) ) . onOrderFinished ( ret , sell ) ; { _ } }} .  *)
 	 	 	 	 refine {{ {orders} -> pop () ; { _ } }} . 
 	 	 	 	 refine {{ {cur_order} -> reset () (* ; { _ } }} . 
 	 	 	 	 refine {{ continue *) }} . 
 	 	 refine {{ (* break *) {orders} -> pop () }} . 
 refine {{ return_ [ !{ cur_order } , !{ orders } , !{ all_amount } ] }} . 
Defined . 
 
(* Notation "'λ4LLLR'" :=   ( @UExpression_Next_LedgerableWithLArgs _ _ _ _ _ λ3) (at level 0) : ursus_scope. (*move 2 sml*) *)

(* Definition extract_active_order_right { (* a2 a3 a4 *) a5 }  
( cur_order : ULValue ( XMaybe (uint # OrderInfoXchgLRecord ) ) ) 
( orders : ULValue ( XQueue OrderInfoXchgLRecord ) ) 
( all_amount : ULValue ( uint128 ) ) 
( sell : URValue ( XBool ) a5 ) 
: URValue ( (XMaybe ( uint # OrderInfoXchgLRecord )) # ( (XQueue OrderInfoXchgLRecord) # uint128 ) )  
 (* ( orb ( orb ( orb a5 a4 ) a3 ) a2 ) *) a5 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4LLLR ) extract_active_order 
 cur_order orders all_amount sell ) . 
 
 Notation " 'extract_active_order_' '(' unsigned cur_order orders all_amount sell ')' " := 
 ( extract_active_order_right 
 unsigned cur_order orders all_amount sell ) 
 (in custom URValue at level 0 , unsigned custom URValue at level 0 
 , cur_order custom URValue at level 0 
 , orders custom URValue at level 0 
 , all_amount custom URValue at level 0 
 , sell custom URValue at level 0 ) : ursus_scope . *)




Definition process_queue ( sell_idx : ( uint ) ) ( buy_idx : ( uint ) ) : UExpression PhantomType false . 
 	 	 refine {{ new 'sell_opt : ( XMaybe (uint # OrderInfoXchgLRecord) ) @ "sell_opt" := {} ; { _ } }} . 
 	 	 refine {{ new 'buy_opt  : ( XMaybe (uint # OrderInfoXchgLRecord) ) @ "buy_opt"  := {} ; { _ } }} . 
 	 	 refine {{ new 'deals_count : ( uint ) @ "deals_count" := 0 ; { _ } }} . 

 	 	 refine {{ while ( TRUE ) do { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ [ {sell_opt} , _sells_ , _sells_amount_ ] 
              := {} (* extract_active_order ( #{sell_opt} , _sells_ , _sells_amount_ , TRUE ) *) ; { _ } }} . 
 	 	 	 refine {{ if ( (~!{sell_opt}) \\ (~!{buy_opt}) ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ (* break *) {sell_opt}:=!{sell_opt} }} . 
 	 	 refine {{ new ( 'sell_idx_cur:uint , 'sell:OrderInfoXchgLRecord ) @ ( "sell_idx_cur" , "sell" ) 
                                 := ( (!{sell_opt}) -> get_default () ) ; { _ } }} . 
 	 	 refine {{ new ( 'buy_idx_cur:uint , 'buy:OrderInfoXchgLRecord ) @ ( "sell_idx_cur" , "sell" ) 
                                 := ( (!{buy_opt}) -> get_default () ) ; { _ } }} . 

 	 	 	 refine {{ new 'sell_out_of_tons : ( XBool ) @ "sell_out_of_tons" := FALSE ; { _ } }} . 
 	 	 	 refine {{ new 'buy_out_of_tons : ( XBool ) @ "buy_out_of_tons" := FALSE ; { _ } }} . 
 	 	 	 refine {{ new 'deal_amount : ( uint128 ) @ "deal_amount" := 0 ; { _ } }} . 
 	 	 	 refine {{ if ( (++ ({deals_count})) > _deals_limit_ ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ new 'half_process_queue:uint @ "" := (_tons_cfg_ ↑ TonsConfig.process_queue) / #{2} ; { _ } }} . 
 	 	 	 	 refine {{ new 'safe_extra : ( uint ) @ "safe_extra" := 
                (_tons_cfg_ ↑ TonsConfig.return_ownership) + (_tons_cfg_ ↑ TonsConfig.order_answer) ; { _ } }} . 
 	 	 	 	 refine {{ if ( ((!{sell}) ↑ OrderInfoXchg.account) < (!{half_process_queue} + !{ safe_extra })
                                 ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 	 refine {{ {sell_out_of_tons} := TRUE }} . 
 	 	 	   refine {{ if ( ((!{buy}) ↑ OrderInfoXchg.account) < (!{half_process_queue} + !{ safe_extra }) ) 
                                  then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ { buy_out_of_tons } := TRUE }} . 
 	 	     refine {{ if ( (~(!{ sell_out_of_tons })) && (~(!{ buy_out_of_tons }) ) ) 
                        then { { _:UEf } }  }} . 
 	 	 	     refine {{ ({sell} ↑ OrderInfoXchg.account) -= !{half_process_queue} ; { _ } }} . 
 	 	 	     refine {{ ({buy} ↑ OrderInfoXchg.account) -= !{half_process_queue} ; { _ } }} . 

(*      	 	 	 refine {{ IPriceXchgPtr ( address { tvm.address ( ) } ) ( Grams ( tons_cfg_ . process_queue . get ( ) ) ) . processQueue ( ) ; { _ } }} .  *)
     	 	 	 refine {{ if ( (#{sell_idx}) == (!{sell_idx_cur}) ) then { { _:UEf } } ; { _ } }} . 
     	 	 	 	 refine {{ {sell} := !{sell} (* dealer.ret_ := [ 1 (* ec::deals_limit *) , 
                    ((!{sell}) ^^ OrderInfoXchg.original_amount) - 
                    ((!{sell}) ^^ OrderInfoXchg.amount) , ((!{sell}) ^^ OrderInfoXchg.amount) ] *) }} .
     	 	 	 refine {{ if ( (#{ buy_idx }) == !{ buy_idx_cur } ) then { { _:UEf } } ; { _ } }} . 
     	 	 	 	 refine {{ {sell} := !{sell} (* dealer.ret_ := [ 1 (* ec::deals_limit *) , 
                    ((!{buy}) ^^ OrderInfoXchg.original_amount) - 
                    ((!{buy}) ^^ OrderInfoXchg.amount) , 
                    ((!{buy}) ^^ OrderInfoXchg.amount) ] *) }} .
     	 	 	 refine {{ (* break *) {sell} := !{sell} }} . 
         refine {{ if ( (~ (!{ sell_out_of_tons })) && (~(!{ buy_out_of_tons })) ) then { { _:UEf } }  ; { _ } }} . 
         	 refine {{ [ {sell_out_of_tons} , {buy_out_of_tons} , {deal_amount} ] := {}
                            (* make_deal_ ( !{sell} , !{buy} ) *) }} . 
         refine {{ if ( !{sell_out_of_tons} ) then { { _:UEf } } ; { _ } }} . 
         	 refine {{ _sells_ -> pop () ; { _ } }} . 
         	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
         	 	 	 [ 1 (*ec::out_of_tons*) , ((!{sell}) ↑ OrderInfoXchg.original_amount) - 
                    ((!{sell}) ↑ OrderInfoXchg.amount) , 0 ] ; { _ } }} . 
         	 refine {{ if ( (#{sell_idx}) == !{sell_idx_cur} ) then { { _:UEf } } ; { _ } }} . 
         	 	 refine {{ (* dealer.ret_ *) { ret } := !{ ret } }} . 
         	 refine {{ if ( ((!{sell}) ↑ OrderInfoXchg.account) > (_tons_cfg_ ↑ TonsConfig.return_ownership) ) 
                             then { { _:UEf } } ; { _ } }} . 
         	 	 refine {{ ({sell} ↑ OrderInfoXchg.account) -= (_tons_cfg_ ↑ TonsConfig.return_ownership) (* ; { _ } }} . 
         	 	 refine {{ ITONTokenWalletPtr ( sell . tip3_wallet_provide ) ( Grams ( tons_cfg_ . return_ownership . get ( ) ) ) . returnOwnership ( sell . amount ) ; { _ } }} . 
         	 	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { true } ) *) }} . 
         refine {{ {sell_opt} -> reset () }} . 
       refine {{ if ( !{ buy_out_of_tons } ) then { { _:UEf } } ; { _ } }} . 
     	 refine {{ _buys_ -> pop () ; { _ } }} . 
     	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
     	 	 	 [ 1 (* ec::out_of_tons *) , ((!{buy}) ↑ OrderInfoXchg.original_amount) - 
                                       ((!{buy}) ↑ OrderInfoXchg.amount), 0 ] ; { _ } }} . 
     	 refine {{ if ( (#{ buy_idx }) == !{ buy_idx_cur } ) then { { _:UEf } } ; { _ } }} . 
     	 	 refine {{ (* dealer.ret_ *) { ret } := !{ ret } }} . 
     	 refine {{ if ( ((!{sell}) ↑ OrderInfoXchg.account) > (_tons_cfg_ ↑ TonsConfig.return_ownership) ) 
                          then { { _:UEf } } ; { _ } }} . 
(*      	 	 refine {{ { ITONTokenWalletPtr ( buy . tip3_wallet_provide ) ( Grams ( tons_cfg_ . return_ownership . get ( ) ) ) . returnOwnership ( buy . amount ) ; { _ } }} .  *)
     	 	 refine {{ { ret } := !{ ret } (* IPriceCallbackPtr ( buy . client_addr ) ( Grams ( buy . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { false } ) *) }} . 
       refine {{ {buy_opt} -> reset () }} . 
       refine {{ if ( !{ sell_out_of_tons } \\ !{ buy_out_of_tons } ) then { { _:UEf } } ; { _ } }} . 
       	 refine {{ (* continue *) {buy_opt} -> reset () }} . 
 (*       refine {{ second ( {sell_opt} -> get () ) := !{sell} ; { _ } }} . 
       refine {{ buy_opt - > second = buy ; { _ } }} .  *)
       refine {{ _sells_amount_ -= !{ deal_amount } ; { _ } }} . 
       refine {{ _buys_amount_ -= !{ deal_amount } ; { _ } }} .
       refine {{ if ( ~ { _:URValue uint false } )        then { { _:UEf } } ; { _ } }} . 

       refine || ((!{sell}) ↑ OrderInfoXchg.amount) || . (* TODO: *) 

(*        refine {{ if ( ~ !(({sell}) ^^ OrderInfoXchg.amount) ) then { { _:UEf } } ; { _ } }} .
compute. apply intFunBool.
 *)
(*  	       refine {{ dealer.sells_ -> pop () ; { _ } }} .  *)
 	       refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	             [ 1 (* ok *) , 
                    (!{sell} ↑ OrderInfoXchg.original_amount) , 0 ] ; { _ } }} . 
 	       refine {{ if ( (#{ sell_idx }) == !{ sell_idx_cur } ) then { { _:UEf } } ; { _ } }} . 
 	 	     refine {{ (* dealer.ret_ *) {ret} := !{ ret } }} . 
(*  	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { true } ) ; { _ } }} .  *)
 	       refine {{ {sell_opt} -> reset () }} . 
       refine {{ if ( ~ {_:URValue uint false} ) then { { _:UEf } } }} . 
         refine || ((!{buy}) ↑ OrderInfoXchg.amount) || .
(*  	       refine {{ dealer.buys_ -> pop () ; { _ } }} .  *)
 	       refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	           [ 1 (* ok *) , (!{buy} ↑ OrderInfoXchg.original_amount) , 0 ] ; { _ } }} . 
 	       refine {{ if ( (#{ buy_idx }) == !{ buy_idx_cur } ) then { { _:UEf } } ; { _ } }} . 
 	 	       refine {{ (* dealer.ret_ *) {ret} := !{ ret } }} . 
(*  	       refine {{ IPriceCallbackPtr ( buy . client_addr ) ( Grams ( buy . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { false } ) ; { _ } }} .  *)
 	       refine {{ {buy_opt} -> reset () }} . 
       refine {{ if ( 1 (* (?(!{sell_opt})) && 
                      (?(( second ( (!{sell_opt}) -> get_default () ) ) ^^ OrderInfoXchg.amount)) *) ) 
                       then { { _:UEf } } ; { _ } }} .
        refine {{ new 'sell:OrderInfoXchgLRecord @ "sell" := 
                     second ( (!{sell_opt}) -> get_default () ) ; { _ } }} . 
    	 refine {{ {sell_opt}:=!{sell_opt} (* dealer.sells_ ^^ change_front ( sell ) *)  }} .  
 	     refine {{ if ( (#{sell_idx}) == ( first ((!{sell_opt}) -> get_default () ) )) 
                          then { { _:UEf } } ; { _ } }} .
         refine {{ {sell_opt}:=!{sell_opt}(* dealer.ret_ := (* OrderRet *) [ 1 (* ok *) , 
                     ((#{sell}) ^^ OrderInfoXchg.original_amount) - 
                     ((#{sell}) ^^ OrderInfoXchg.amount) , ((#{sell}) ^^ OrderInfoXchg.amount) ] *) }} . 

       refine {{ if ( 1 (* (?(!{buy_opt})) && 
                      (?(( second ( (!{buy_opt}) -> get_default () ) ) ^^ OrderInfoXchg.amount)) *) ) 
                       then { { _:UEf } } }} .

        refine {{ new 'buy:OrderInfoXchgLRecord @ "sell" := 
                     second ( (!{buy_opt}) -> get_default () ) ; { _ } }} . 
(*  	 refine {{ buys_ ^^ change_front ( buy ) ; { _ } }} .  *)
 	   refine {{ if ( (#{buy_idx}) == first ( (!{buy_opt}) -> get_default () ) ) then { { _:UEf } } }} . 
 	 	 refine {{ {sell_opt}:=!{sell_opt} (* ret_ := OrderRet { ok , buy ^^ original_amount - buy ^^ amount , buy ^^ amount } *) }} . 
 Defined . 
 
 Definition int_sender_and_value : UExpression ( XAddress # uint (* Grams *) ) false . 
 	 	 refine {{ new 'sender : ( XAddress ) @ "sender" := {} (* int_sender ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ sender } , {} (* int_value_ *) ] }} . 
 Defined . 

 Definition int_sender_and_value_right  : URValue ( XAddress # uint (* Grams *) ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) int_sender_and_value 
 ) . 
 
 Notation " 'int_sender_and_value_' '(' ')' " := 
 ( int_sender_and_value_right 
 ) 
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

(* void set_int_return_value(unsigned val) { int_return_value_ = val; } *)
Parameter set_int_return_value : UExpression PhantomType false .
Notation " 'set_int_return_value_' '(' ')' " := 
 ( set_int_sender ) 
 (in custom ULValue at level 0 ) : ursus_scope .



Definition onTip3LendOwnershipMinValue : UExpression uint128 false . 
 	 	 refine {{ return_ ( _tons_cfg_ ↑ TonsConfig.process_queue )+ 
                       ( _tons_cfg_ ↑ TonsConfig.transfer_tip3 )+ 
                       ( _tons_cfg_ ↑ TonsConfig.send_notify )+ 
                       ( _tons_cfg_ ↑ TonsConfig.return_ownership) + 
                       ( _tons_cfg_ ↑ TonsConfig.order_answer) }} . 
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
: UExpression ( StateInitLRecord # uint256 ) false .
 	 	 refine {{ new 'wallet_data : ( DTONTokenWalletInternalLRecord ) @ "wallet_data" := 
                 [ #{name} , #{symbol} , #{decimals} , 0 , #{root_public_key} , 
                   #{wallet_public_key} , #{root_address} , #{owner_address} , 
                   {} , #{code} , #{workchain_id} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_data_cl : ( XCell ) @ "wallet_data_cl" := 
               prepare_persistent_data_ ( {} , !{wallet_data} ) ; { _ } }} . 
 	 	 refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 
              [ {} , {} , (#{code}) -> set () , (!{wallet_data_cl}) -> set () , {} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_init_cl : ( XCell ) @ "wallet_init_cl" := {}  
 	 	            (*  build ( !{ wallet_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ wallet_init } , {} (* tvm_hash ( wallet_init_cl ) *) ] }} . 
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

Definition name_right {b} (x: URValue Tip3ConfigLRecord b): URValue XString b :=
    || {x} ^^ {Tip3Config_ι_name} || : _ .
    
Definition name_left (x: ULValue Tip3ConfigLRecord): ULValue XString :=
    {{ {x} ^^ {Tip3Config_ι_name} }} : _.
    
Notation " a '↑' 'Tip3Config.name' " := ( name_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.name' " := ( name_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition symbol_right {b} (x: URValue Tip3ConfigLRecord b): URValue XString b :=
    || {x} ^^ {Tip3Config_ι_symbol} || : _ .
    
Definition symbol_left (x: ULValue Tip3ConfigLRecord): ULValue XString :=
    {{ {x} ^^ {Tip3Config_ι_symbol} }} : _.
    
Notation " a '↑' 'Tip3Config.symbol' " := ( symbol_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.symbol' " := ( symbol_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition decimals_right {b} (x: URValue Tip3ConfigLRecord b): URValue XUInteger8 b :=
    || {x} ^^ {Tip3Config_ι_decimals} || : _ .
    
Definition decimals_left (x: ULValue Tip3ConfigLRecord): ULValue XUInteger8 :=
    {{ {x} ^^ {Tip3Config_ι_decimals} }} : _.
    
Notation " a '↑' 'Tip3Config.decimals' " := ( decimals_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.decimals' " := ( decimals_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition root_public_key_right {b} (x: URValue Tip3ConfigLRecord b): URValue XUInteger256 b :=
    || {x} ^^ {Tip3Config_ι_root_public_key} || : _ .
    
Definition root_public_key_left (x: ULValue Tip3ConfigLRecord): ULValue XUInteger256 :=
    {{ {x} ^^ {Tip3Config_ι_root_public_key} }} : _.
    
Notation " a '↑' 'Tip3Config.root_public_key' " := ( root_public_key_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.root_public_key' " := ( root_public_key_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition root_address_right {b} (x: URValue Tip3ConfigLRecord b): URValue XAddress b :=
    || {x} ^^ {Tip3Config_ι_root_address} || : _ .
    
Definition root_address_left (x: ULValue Tip3ConfigLRecord): ULValue XAddress :=
    {{ {x} ^^ {Tip3Config_ι_root_address} }} : _.
    
Notation " a '↑' 'Tip3Config.root_address' " := ( root_address_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'Tip3Config.root_address' " := ( root_address_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition expected_wallet_address 
( cfg : ( Tip3ConfigLRecord ) ) 
( wallet_pubkey : ( uint256 ) ) 
( internal_owner : ( uint256 ) ) 
: UExpression uint256 false . 
 	 	 refine {{ new 'owner_addr : ( XMaybe XAddress ) @ "owner_addr" := {} ; { _ } }} . 
 	 	 refine {{ if ( 1 (* ?(#{internal_owner}) *) ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ {owner_addr} := {} (* Address :: make_std ( workchain_id_ , !{ internal_owner } ) *) }} . 
 	 	 refine {{ return_ 
           second ( prepare_internal_wallet_state_init_and_addr_ 
                         ( (#{cfg}) ↑ Tip3Config.name , 
                         (#{cfg}) ↑ Tip3Config.symbol , 
                         (#{cfg}) ↑ Tip3Config.decimals , 
                         (#{cfg}) ↑ Tip3Config.root_public_key , 
                          #{ wallet_pubkey } , 
                         (#{cfg}) ↑ Tip3Config.root_address , 
                          !{ owner_addr } , _tip3_code_ , _workchain_id_ ) ) }} . 
Defined . 

 Definition expected_wallet_address_right { a1 a2 a3 }  ( cfg : URValue ( Tip3ConfigLRecord ) a1 ) ( wallet_pubkey : URValue ( uint256 ) a2 ) ( internal_owner : URValue ( uint256 ) a3 ) : URValue uint256 ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) expected_wallet_address 
 cfg wallet_pubkey internal_owner ) . 
 
 Notation " 'expected_wallet_address_' '(' cfg ',' wallet_pubkey ',' internal_owner ')' " := 
 ( expected_wallet_address_right 
 cfg wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 
 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope .

Definition verify_tip3_addr ( cfg : ( Tip3ConfigLRecord ) ) ( tip3_wallet : ( XAddress ) ) ( wallet_pubkey : ( uint256 ) ) ( internal_owner : ( uint256 ) ) : UExpression XBool false . 
 refine {{ new 'expected_address : ( uint256 ) @ "expected_address" := 
             expected_wallet_address_ ( #{ cfg } , #{ wallet_pubkey } , #{ internal_owner } ) ; { _ } }} . 
 	 refine {{ return_ (* Std :: get < addr_std > ( !{ tip3_wallet } ( ) ) . address *) {} == !{ expected_address } }} . 
 Defined . 

 Definition verify_tip3_addr_right { a1 a2 a3 a4 }  ( cfg : URValue ( Tip3ConfigLRecord ) a1 ) ( tip3_wallet : URValue ( XAddress ) a2 ) ( wallet_pubkey : URValue ( uint256 ) a3 ) ( internal_owner : URValue ( uint256 ) a4 ) : URValue XBool ( orb ( orb ( orb a4 a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) verify_tip3_addr 
 cfg tip3_wallet wallet_pubkey internal_owner ) . 
 
 Notation " 'verify_tip3_addr_' '(' cfg ',' tip3_wallet ',' wallet_pubkey ',' internal_owner ')' " := 
 ( verify_tip3_addr_right 
 cfg tip3_wallet wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 
 , tip3_wallet custom URValue at level 0 
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

Parameter tvm_rawreserve : UExpression OrderRetLRecord false .
Notation " 'tvm.rawreserve' '(' ')' " := 
 ( tvm_rawreserve ) 
 (in custom ULValue at level 0 ) : ursus_scope .

 Definition on_ord_fail 
( ec : ( uint ) ) 
( wallet_in : ( XAddress (* ITONTokenWalletPtrLRecord *) ) ) 
( amount : ( uint128 ) ) 
: UExpression OrderRetLRecord false . 
(*  	 	 refine {{ wallet_in(Grams(tons_cfg_.return_ownership.get())).returnOwnership(amount) ; { _ } }} .  *)
 	 	 refine {{ if ( ( _sells_ -> empty () ) && ( _buys_ -> empty () ) ) then { { _:UEf } } else { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ set_int_return_flag_ ( ) (* SEND_ALL_GAS | DELETE_ME_IF_I_AM_EMPTY *) }} . 
     	 refine {{ new 'incoming_value : uint @ "incoming_value" := int_value ( ) ; { _ } }} . 
     	 refine {{ tvm.rawreserve ( ) (*tvm.balance () - !{incoming_value} , 1 (* rawreserve_flag::up_to *) *) ; { _ } }} . 
     	 refine {{ set_int_return_flag_ ( ) (* SEND_ALL_GAS *) }} . 
 refine {{ return_ [ 1 (* ec *) , {} , {} ] }} . 
Defined . 

 Definition on_ord_fail_right { a1 a2 a3 }  ( ec : URValue ( uint ) a1 ) ( wallet_in : URValue ( XAddress (* ITONTokenWalletPtrLRecord *) ) a2 ) ( amount : URValue ( uint128 ) a3 ) : URValue OrderRetLRecord ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) on_ord_fail 
 ec wallet_in amount ) . 
 
 Notation " 'on_ord_fail_' '(' ec ',' wallet_in ',' amount ')' " := 
 ( on_ord_fail_right 
 ec wallet_in amount ) 
 (in custom URValue at level 0 , ec custom URValue at level 0 
 , wallet_in custom URValue at level 0 
 , amount custom URValue at level 0 ) : ursus_scope . 

 Definition process_queue_impl 
( tip3root_sell : ( XAddress ) ) 
( tip3root_buy : ( XAddress ) ) 
( notify_addr : ( XAddress (* IFlexNotifyPtr *) ) ) 
( price : ( RationalPriceLRecord ) ) 
( deals_limit : ( uint8 ) ) 
( tons_cfg : ( TonsConfigLRecord ) ) 
( sell_idx : ( uint ) ) 
( buy_idx : ( uint ) ) 
( sells_amount : ( uint128 ) ) 
( sells : ( XQueue OrderInfoXchgLRecord ) ) 
( buys_amount : ( uint128 ) ) 
( buys : ( XQueue OrderInfoXchgLRecord ) ) : UExpression process_retLRecord false . 
 	 	 refine {{ new 'd : ( dealerLRecord ) @ "d" := 	 	 
 	 	 	 [ #{tip3root_sell}, #{tip3root_buy}, #{notify_addr}, #{price}, #{deals_limit}, #{tons_cfg},
           #{sells_amount}, #{sells}, #{buys_amount}, #{buys}, {} ] ; { _ } }} . 
(*  	 	 refine {{ d.process_queue ( sell_idx , buy_idx ) ; { _ } }} .  *)
 	 	 refine {{ return_ [ (!{d}) ^^ dealer.sells_amount_ , 
                         (!{d}) ^^ dealer.sells_ , 
                         (!{d}) ^^ dealer.buys_amount_ , 
                         (!{d}) ^^ dealer.buys_ , 
                         (!{d}) ^^ dealer.ret_ ] }} . 
Defined . 

 Definition process_queue_impl_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 }  
( tip3root_sell : URValue ( XAddress ) a1 ) 
( tip3root_buy : URValue ( XAddress ) a2 ) 
( notify_addr : URValue ( XAddress (* IFlexNotifyPtrLRecord *) ) a3 ) 
( price : URValue ( RationalPriceLRecord ) a4 ) 
( deals_limit : URValue ( uint8 ) a5 ) 
( tons_cfg : URValue ( TonsConfigLRecord ) a6 ) 
( sell_idx : URValue ( uint ) a7 ) 
( buy_idx : URValue ( uint ) a8 ) 
( sells_amount : URValue ( uint128 ) a9 ) 
( sells : URValue ( XQueue OrderInfoXchgLRecord ) a10 ) 
( buys_amount : URValue ( uint128 ) a11 ) 
( buys : URValue ( XQueue OrderInfoXchgLRecord ) a12 ) 
: URValue process_retLRecord 
( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a12 a11 ) a10 ) a9 ) a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) 
:= 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ12 ) process_queue_impl 
 tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) . 
 
 Notation " 'process_queue_impl_' '(' tip3root_sell ',' tip3root_buy ',' notify_addr ',' price ',' deals_limit ',' tons_cfg ',' sell_idx ',' buy_idx ',' sells_amount ',' sells ',' buys_amount ',' buys ')' " := 
 ( process_queue_impl_right 
 tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) 
 (in custom URValue at level 0 , tip3root_sell custom URValue at level 0 
 , tip3root_buy custom URValue at level 0 
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


Definition sell_right {b} (x: URValue PayloadArgsLRecord b): URValue XBool b :=
    || {x} ^^ {PayloadArgs_ι_sell} || : _ .
    
Definition sell_left (x: ULValue PayloadArgsLRecord): ULValue XBool :=
    {{ {x} ^^ {PayloadArgs_ι_sell} }} : _.
    
Notation " a '↑' 'PayloadArgs.sell' " := ( sell_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.sell' " := ( sell_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition receive_tip3_wallet_right {b} (x: URValue PayloadArgsLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {PayloadArgs_ι_receive_tip3_wallet} || : _ .
    
Definition receive_tip3_wallet_left (x: ULValue PayloadArgsLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {PayloadArgs_ι_receive_tip3_wallet} }} : _.
    
Notation " a '↑' 'PayloadArgs.receive_tip3_wallet' " := ( receive_tip3_wallet_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.receive_tip3_wallet' " := ( receive_tip3_wallet_left a ) (in custom ULValue at level 0) : ursus_scope.


Definition PayloadArgs_amount_right {b} (x: URValue PayloadArgsLRecord b): URValue uint128 b :=
    || {x} ^^ {PayloadArgs_ι_amount} || : _ .
    
Definition PayloadArgs_amount_left (x: ULValue PayloadArgsLRecord): ULValue uint128 :=
    {{ {x} ^^ {PayloadArgs_ι_amount} }} : _.
    
Notation " a '↑' 'PayloadArgs.amount' " := ( PayloadArgs_amount_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.amount' " := ( PayloadArgs_amount_left a ) (in custom ULValue at level 0) : ursus_scope.

Definition client_addr_right {b} (x: URValue PayloadArgsLRecord b): URValue addr_std_fixedLRecord b :=
    || {x} ^^ {PayloadArgs_ι_client_addr} || : _ .
    
Definition client_addr_left (x: ULValue PayloadArgsLRecord): ULValue addr_std_fixedLRecord :=
    {{ {x} ^^ {PayloadArgs_ι_client_addr} }} : _.
    
Notation " a '↑' 'PayloadArgs.client_addr' " := ( client_addr_right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'PayloadArgs.amount' " := ( client_addr_left a ) (in custom ULValue at level 0) : ursus_scope.



Definition onTip3LendOwnership 
( answer_addr : ( XAddress ) ) 
( balance : ( uint128 ) ) 
( lend_finish_time : ( uint32 ) ) 
( pubkey : ( uint256 ) ) 
( internal_owner : ( XAddress ) ) 
( payload : ( XCell ) ) 
: UExpression OrderRetLRecord false . 
 	 	 refine {{ new ( 'tip3_wallet:XAddress , 'value:uint (* Grams *) ) @ 
                 ( "tip3_wallet" , "value" ) := int_sender_and_value_ ( ) ; { _ } }} . 
  	 refine {{ new 'wallet_in:XAddress @ "wallet_in" (* ITONTokenWalletPtr *) := !{tip3_wallet} ; { _ } }} . 
 	 	 refine {{new 'ret_owner_gr:uint (* Grams *)@ "ret_owner_gr" :=
                  ( _tons_cfg_ ↑ TonsConfig.return_ownership ) ; { _ } }} . 
 	 	 refine {{ set_int_sender_ ( ) (* #{answer_addr} *) ; { _ } }} . 
 	 	 refine {{ set_int_return_value_ ( ) (* _tons_cfg_ ^^ TonsConfig.order_answer *) ; { _ } }} . 
 	 	 refine {{ new 'min_value : ( uint128 ) @ "min_value" := 
                    onTip3LendOwnershipMinValue_ ( ) ; { _ } }} . 
  	 	 refine {{ new 'args : ( PayloadArgsLRecord ) @ "args" := {} (* parse ( payload . ctos ( ) ) *) ; { _ } }} .

 	 	 refine {{ new 'is_sell : ( XBool ) @ "is_sell" := (!{args}) ↑ PayloadArgs.sell ; { _ } }} . 
 	 	 refine {{ new 'amount : ( uint128 ) @ "amount" := (!{args}) ↑ PayloadArgs.amount ; { _ } }} . 
 	 	 refine {{ new 'minor_amount : ( XMaybe uint128 ) @ "minor_amount" := 
                             minor_cost_ ( !{ amount } , _price_ ) ; { _ } }} . 
 	 	 refine {{ new 'err : ( uint ) @ "err" := 0 ; { _ } }} . 
 	 	 refine {{ new 'internal_owner_std : ( uint ) @ "internal_owner_std" := {} 
                   (*  Std :: get < addr_std > ( internal_owner ^^ XAddress:val ( ) ) . address *) ; { _ } }} . 

 	 	 refine {{ if ( (!{value}) < !{min_value} ) then { { _:UEf } } else { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ {err} := 1 (* ec : : not_enough_tons_to_process *) }} . 
 	 	   refine {{ if ( (!{is_sell}) 
                       ? 
        (~( verify_tip3_addr_ ( _major_tip3cfg_ , !{ tip3_wallet } , #{ pubkey } , !{ internal_owner_std } ) ) ) 
                       : 
        (~( verify_tip3_addr_ ( _minor_tip3cfg_ , !{ tip3_wallet } , #{ pubkey } , !{ internal_owner_std } ) ) ) )
                  then { { _:UEf } } else { { _:UEf } } }} . 
         	 	 	 refine {{ { err } := 1 (* ec::unverified_tip3_wallet *) }} . 
         	 	   refine {{ if ( ~ (?(!{ minor_amount })) ) 
                         then { { _:UEf } } else { { _:UEf } } }} . 
         	 	 	 refine {{ {err} := 1 (* ec::too_big_tokens_amount *) }} . 
         	 	   refine {{ if ( !{amount} < _min_amount_ ) then { { _:UEf } } else { { _:UEf } } }} . 
         	 	 	 refine {{ { err } := 1 (* ec : : not_enough_tokens_amount *) }} . 
         	 	 refine {{ if ( (#{balance}) < 
                   ( !{ is_sell } ? !{ amount } : ((!{minor_amount}) -> get_default () ) ) ) 
                          then { { _:UEf } } else { { _:UEf } } }} . 
         	 	 	 refine {{ { err } := 1 (* ec : : too_big_tokens_amount *) }} . 
         	 	   refine {{ if ( ~ (is_active_time_ ( #{ lend_finish_time } )) ) then { { _:UEf } } }} . 
         	 	 	 refine {{ { err } := 1 (* ec : : expired *) }} . 

 	 	 refine {{ if ( !{ err } ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ return_ on_ord_fail_ ( !{err} , !{wallet_in} , !{amount} ) }} . 
 	 	 refine {{ new 'account : ( uint128 ) @ "account" := 
                (!{value}) - (_tons_cfg_ ↑ TonsConfig.process_queue) - 
                             (_tons_cfg_ ↑ TonsConfig.order_answer) ; { _ } }} . 
 	 	 refine {{ new 'ord : ( OrderInfoXchgLRecord ) @ "ord" := 	 	 
 	 	 	 [ !{amount} , !{amount} , !{account} , {} (* (* (*TODO !{tip3_wallet} *) *) *) , 
    { _:_ _ false }     (* (!{args}) ^^ PayloadArgs.receive_tip3_wallet *) , 
    { _:_ _ false }     (* (!{args}) ^^ PayloadArgs.client_addr *)  , #{lend_finish_time} ] ; { _ } }} .
     refine || (!{args}) ↑ PayloadArgs.receive_tip3_wallet ||.
     refine || (!{args}) ↑ PayloadArgs.client_addr ||.
    
 	 	 refine {{ new 'sell_idx : ( uint ) @ "sell_idx" := 0 ; { _ } }} . 
 	 	 refine {{ new 'buy_idx : ( uint ) @ "buy_idx" := 0 ; { _ } }} . 
 	 	 refine {{ new 'notify_amount:( uint128 ) @ "notify_amount" := {}  ; { _ } }} . 
 	 	 refine {{ if ( !{ is_sell } ) then { { _:UEf } } else { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ _sells_ -> push ( !{ord} ) ; { _ } }} . 
 	 	 	 refine {{ _sells_amount_ += ((!{ord}) ↑ OrderInfoXchg.amount) ; { _ } }} . 

Check || _sells_ || .
Print OrderInfoXchgLRecord .
Print ClassGenerator.prod_list .

 	 	 	 refine {{ { sell_idx } := {} (* sells_.back_with_idx().first *); { _ } }} . 
 	 	 	 refine {{ {notify_amount} := _sells_amount_ }} . 

     	 refine {{ _buys_ -> push ( !{ord} ) ; { _ } }} . 
     	 refine {{ _buys_amount_ += !{ord} ↑ OrderInfoXchg.amount ; { _ } }} . 
     	 refine {{ { buy_idx } := {} (* buys_ ^^ back_with_idx ( ) . first *) ; { _ } }} . 
     	 refine {{ {notify_amount} := _buys_amount_ }} . 
(*  refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onXchgOrderAdded ( is_sell , major_tip3cfg_ . root_address , minor_tip3cfg_ . root_address , price_ . num , price_ . denum , ord . amount , notify_amount ) ; { _ } }} .  *)
 	 	 refine {{ new ( 'sells_amount:uint128 , 'sells:(XQueue OrderInfoXchgLRecord) , 
                     'buys_amount:uint128 , 
                     'buys:(XQueue OrderInfoXchgLRecord) , 
                     'ret: (XMaybe OrderRetLRecord) )
                @ ( "sells_amount" , "sells" , "buys_amount" , "buys" , "ret" ) :=
    process_queue_impl_ ( _major_tip3cfg_ ↑ Tip3Config.root_address , 
                          _minor_tip3cfg_ ↑ Tip3Config.root_address , 
                          _notify_addr_ , 
                          _price_ , 
                          _deals_limit_ , 
                          _tons_cfg_ , 
                         !{sell_idx} , 
                         !{buy_idx} , 
                         _sells_amount_ , 
                         _sells_ , 
                         _buys_amount_ , 
                         _buys_ ) ; { _ } }} . 

   refine {{ _sells_ := !{sells} ; { _ } }} .
   refine {{ _buys_ := !{buys} ; { _ } }} . 
   refine {{ _sells_amount_ := !{ sells_amount } ; { _ } }} . 
   refine {{ _buys_amount_ := !{buys_amount} ; { _ } }} . 
   refine {{ if ( ( _sells_ -> empty () ) && ( _buys_ -> empty () ) ) 
                   then { { _:UEf } } ; { _ } }} . 
 	 refine {{ (* suicide ( _flex_ ) *) _buys_ := !{buys} }} . 
 refine {{ if ( !{ret} ) then { { _:UEf } } ; { _ } }} . 
 	 refine {{ return_ (!{ret}) -> get_default () }} . 
 refine {{ return_ [ 1 (* ok *) , 0 , (!{ord}) ^^ OrderInfoXchg.amount ] }} . 
 Defined . 
 
 
 
 
Definition processQueue : UExpression PhantomType false . 
 	 	 refine {{ if ( (_sells_ -> empty ()) \\ (_buys_ -> empty ()) ) 
               then { { _:UEf } }; { _ } }} . 
 	 	 	 refine {{ return_ {} }} . 

 	 	 refine {{ new ( 'sells_amount:uint128 , 
                     'sells:(XQueue OrderInfoXchgLRecord) , 
                     'buys_amount:uint128 , 
                     'buys:(XQueue OrderInfoXchgLRecord) , 
                     'ret: (XMaybe OrderRetLRecord) )
                @ ( "sells_amount" , "sells" , "buys_amount" , "buys" , "ret" ) :=
    process_queue_impl_ ( _major_tip3cfg_ ↑ Tip3Config.root_address , 
                          _minor_tip3cfg_ ↑ Tip3Config.root_address , 
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
                   then { { _:UEf } } }} . 
 	 refine {{ (* suicide ( _flex_ ) *) _buys_ := !{buys} }} . 
Defined . 
 
Definition cancel_order_impl 
( orders : ( XQueue OrderInfoXchgLRecord ) ) 
( client_addr : ( addr_std_fixedLRecord ) ) 
( all_amount : ( uint128 ) ) 
( sell : ( XBool ) ) 
( return_ownership : ( uint (* Grams *) ) ) 
( process_queue : ( uint (* Grams *) ) ) 
( incoming_val : ( uint (* Grams *) ) ) 
: UExpression ((XQueue OrderInfoXchgLRecord) # uint128) false . 

 	 	 refine {{ new 'is_first : ( XBool ) @ "is_first" := TRUE ; { _ } }} . 
(*  	 	 refine {{ for ( auto it = orders ^^ OrderInfoXchgLRecord:begin ( ) ; it != orders ^^ OrderInfoXchgLRecord:end ( ) ; ) { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { auto next_it = std : : next ( it ) ; { _ } }} . 
 	 	 	 refine {{ new 'ord : ( auto ) @ "ord" := {} ; { _ } }} . 
 	 	 	 refine {{ { ord } := *it ; { _ } }} . 
 	 	 	 refine {{ if ( ord ^^ auto:client_addr == !{ client_addr } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 	 refine {{ { unsigned minus_val = process_queue . get ( ) ; { _ } }} . 
 	 	 	 	 refine {{ ITONTokenWalletPtr ( ord . tip3_wallet_provide ) ( return_ownership ) . returnOwnership ( ord . amount ) ; { _ } }} . 
 	 	 	 	 refine {{ minus_val += return_ownership ^^ GramsLRecord:get ( ) ; { _ } }} . 
 	 	 	 	 refine {{ new 'plus_val : ( uint ) @ "plus_val" := {} ; { _ } }} . 
 	 	 	 	 refine {{ { plus_val } := ord ^^ auto:account . get ( ) + ( !{ is_first } ? incoming_val ^^ GramsLRecord:get ( ) : 0 ) ; { _ } }} . 
 	 	 	 	 refine {{ { is_first } := false ; { _ } }} . 
 	 	 	 	 refine {{ if ( !{ plus_val } > minus_val ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 	 	 refine {{ { unsigned ret_val = plus_val - minus_val ; { _ } }} . 
 	 	 	 	 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 	 	 	 	 
 	 	 	 [$ $] ; { _ } }} . 
 	 	 	 	 	 refine {{ IPriceCallbackPtr ( ord . client_addr ) ( Grams ( ret_val ) ) . onOrderFinished ( ret , sell ) }} . 
 	 	 	 refine {{ { all_amount } -= ord ^^ auto:amount ; { _ } }} . 
 	 	 	 refine {{ orders ^^ OrderInfoXchgLRecord:erase ( it ) }} . 
 	 refine {{ it := next_it }} .  *)
 refine {{ return_ [ #{ orders } , #{ all_amount } ] }} . 
Defined . 
 
 Definition cancel_order_impl_right { a1 a2 a3 a4 a5 a6 a7 }  
( orders : URValue ( XQueue OrderInfoXchgLRecord ) a1 ) 
( client_addr : URValue ( addr_std_fixedLRecord ) a2 ) 
( all_amount : URValue ( uint128 ) a3 ) 
( sell : URValue ( XBool ) a4 ) 
( return_ownership : URValue ( uint (* Grams *) ) a5 )
 ( process_queue : URValue ( uint (* Grams *) ) a6 ) 
( incoming_val : URValue ( uint (* Grams *) ) a7 ) 
: URValue ((XQueue OrderInfoXchgLRecord)  # uint128)
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
 	 	 refine {{ new 'client_addr : ( addr_std_fixedLRecord ) @ "client_addr" := {}
                    (* int_sender_ ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'value : ( uint ) @ "value" := 
                             int_value ( ) ; { _ } }} . 
 	 	 refine {{ new ( 'sells:(XQueue OrderInfoXchgLRecord) , 'sells_amount:uint128 )
                      @ ( "sells" , "sells_amount" ) :=
        cancel_order_impl_ ( _sells_ , !{client_addr} , _sells_amount_ , 
                             TRUE , 
                             _tons_cfg_ ↑ TonsConfig.return_ownership , 
                             _tons_cfg_ ↑ TonsConfig.process_queue , 
                             !{value} ) ; { _ } }} . 
 	 	 refine {{ _sells_ := !{ sells } ; { _ } }} . 
 	 	 refine {{ _sells_amount_ := !{sells_amount} ; { _ } }} . 
 	 	 refine {{ { canceled_amount } -= _sells_amount_ ; { _ } }} . 
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onXchgOrderCanceled ( bool_t { true } , major_tip3cfg_ . root_address , minor_tip3cfg_ . root_address , price_ . num , price_ . denum , canceled_amount , sells_amount_ ) ; { _ } }} .  *)
 	 	 refine {{ if ( (_sells_ -> empty ()) && (_buys_ -> empty ()) ) 
               then { { _:UEf } } }} . 
 	 	 	 refine {{ _sells_ := !{ sells } (* suicide ( flex_ ) *) }} . 
Defined . 
 
Definition cancelBuy : UExpression PhantomType false . 
 	 	 refine {{ new 'canceled_amount : ( uint128 ) @ "canceled_amount" := _buys_amount_ ; { _ } }} . 
 	 	 refine {{ new 'client_addr : ( addr_std_fixedLRecord ) @ "client_addr" := {} (* int_sender_ ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'value : ( uint ) @ "value" := int_value ( ) ; { _ } }} . 

 	 	 refine {{ new ( 'buys:(XQueue OrderInfoXchgLRecord) , 'buys_amount:uint128 )
                      @ ( "buys" , "buys_amount" ) :=
        cancel_order_impl_ ( _buys_ , !{client_addr} , _buys_amount_ , 
                             FALSE , 
                             _tons_cfg_ ↑ TonsConfig.return_ownership , 
                             _tons_cfg_ ↑ TonsConfig.process_queue , 
                             !{value} ) ; { _ } }} . 
 	 	 refine {{ _buys_ := !{ buys } ; { _ } }} . 
 	 	 refine {{ _buys_amount_ := !{buys_amount} ; { _ } }} . 
 	 	 refine {{ {canceled_amount} -= _buys_amount_ ; { _ } }} . 
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onXchgOrderCanceled ( bool_t { false } , major_tip3cfg_ . root_address , minor_tip3cfg_ . root_address , price_ . num , price_ . denum , canceled_amount , buys_amount_ ) ; { _ } }} .  *)
 	 	 refine {{ if ( ( _sells_ -> empty () ) && (_buys_ -> empty () ) ) 
             then { { _:UEf } } }} . 
 	 	 	 refine {{ _buys_ := !{ buys } (* suicide ( flex_ ) *) }} . 
Defined . 
 
 Definition getPriceNum : UExpression uint128 false . 
 	 	 refine {{ return_ _price_ ^^ RationalPrice.num }} . 
 Defined . 
 
 Definition getPriceNum_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPriceNum 
 ) . 
 
 Notation " 'getPriceNum_' '(' ')' " := 
 ( getPriceNum_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getPriceDenum : UExpression uint128 false . 
 	 	 refine {{ return_ _price_ ^^ RationalPrice.denum }} . 
Defined . 
 
Definition getPriceDenum_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPriceDenum 
 ) . 
 
 Notation " 'getPriceDenum_' '(' ')' " := 
 ( getPriceDenum_right 
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
 
Definition getSells : UExpression ( XHMap uint OrderInfoXchgLRecord ) false . 
 	 	 refine {{ return_  {} (* dict_array ( sells_ . begin ( ) , sells_ . end ( ) ) *) }} . 
 Defined . 
 
Definition getSells_right  : URValue ( XHMap uint OrderInfoXchgLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSells 
 ) . 
 
 Notation " 'getSells_' '(' ')' " := 
 ( getSells_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getBuys : UExpression ( XHMap uint OrderInfoXchgLRecord ) false . 
 	 	 refine {{ return_ {} (* dict_array ( buys_ . begin ( ) , buys_ . end ( ) ) *) }} . 
 Defined . 
 
Definition getBuys_right  : URValue ( XHMap uint OrderInfoXchgLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuys 
 ) . 
 
 Notation " 'getBuys_' '(' ')' " := 
 ( getBuys_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
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
 
Definition _fallback ( _ : XCell ) ( _ : XSlice ) : UExpression uint false . 
 	 	 refine {{ return_ 0 }} . 
Defined . 
 
Definition prepare_price_xchg_state_init_and_addr 
( price_data : ( ContractLRecord ) ) 
( price_code : ( XCell ) ) 
: UExpression ( StateInitLRecord # uint256 ) false . 
 	 	 refine {{ new 'price_data_cl : ( XCell ) @ "price_data_cl" := 
                         prepare_persistent_data_ ( {} , #{price_data} ) ; { _ } }} . 
 	 	 refine {{ new 'price_init : ( StateInitLRecord ) @ "price_init" := 	
          	 [ {} , {} , (#{price_code}) -> set () , 
              (!{price_data_cl}) -> set () , {} ] ; { _ } }} . 
 	 	 refine {{ new 'price_init_cl : ( XCell ) @ "price_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ {price_init_cl} := {} (* build ( !{ price_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{price_init} , {} (* tvm.hash ( !{price_init_cl} ) *) ] }} . 
 Defined . 

Definition getDetails : UExpression DetailsInfoXchgLRecord false . 
 	 	 refine {{ return_ [ getPriceNum_ ( ) , getPriceDenum_ ( ) , getMinimumAmount_ ( ) , 
                         getSellAmount_ ( ) , getBuyAmount_ ( ) ] }} . 
 Defined .

End FuncsInternal.
End Funcs.

