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

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Require Import Project.CommonConstSig.
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.Price.Ledger.
Require Import Contracts.Price.Functions.FuncSig.
Require Import Contracts.Price.Functions.FuncNotations.
Require Contracts.Price.Interface.

(*this elpi code move to the Ursus lib afterwards*)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.


Elpi Command AddLocalState.

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

Elpi Typecheck.
 
(* Module trainContractSpecModuleForFuncs := trainContractSpec XTypesModule StateMonadModule. *)

Module Type Has_Internal.

Parameter Internal: bool .

End Has_Internal.

Module Funcs (ha : Has_Internal)(dc : ConstsTypesSig XTypesModule StateMonadModule) .

Import ha.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

Export SpecModuleForFuncNotations(* ForFuncs *).tvmNotationsModule.

Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.

Existing Instance xbool_default.

Definition calc_cost ( amount : ( XInteger128 ) ) ( price : ( XInteger128 ) ) : UExpression (XMaybe XInteger128) false . 
 	 	 refine {{ new 'tons_cost : ( XInteger ) @ "tons_cost" := (#{amount}) * (#{price}) ; { _ } }} . 
 	 	 refine {{ if ( !{tons_cost} >> #{128} ) 
                     then { { _:UExpressionP (XMaybe XInteger128) false } } ; { _ } }} . 
 	 	 	 refine {{ return_ {} }} . 
 	 	 refine {{ return_ ( (!{tons_cost}) -> set () ) }} . 
Defined . 

 Definition calc_cost_right { a1 a2 }  ( amount : URValue ( XInteger128 ) a1 ) ( price : URValue ( XInteger128 ) a2 ) : URValue (XMaybe XInteger128) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_cost 
 amount price ) . 
 
 Notation " 'calc_cost_' '(' amount ',' price ')' " := 
 ( calc_cost_right 
 amount price ) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom URValue at level 0 ) : ursus_scope . 

Definition make_deal ( sell : ( OrderInfoLRecord ) ) ( buy : ( OrderInfoLRecord ) ) : UExpression ( XBool * (XBool * XInteger128) ) false . 
 	 	 refine {{ new 'deal_amount : ( XInteger ) @ "deal_amount" := {}  
 	 	        (* std::min ( (#{sell}) ^^ OrderInfoLRecord.amount , (#{buy}) ^^ OrderInfoLRecord.amount ) *) ; { _ } }} . 
 	 	 refine {{ new 'last_tip3_sell : ( XBool ) @ "last_tip3_sell" := 	 	 
                   ( !{deal_amount} == ( ( #{sell} ) ^^ OrderInfo.amount ) ) ; { _ } }} .
(*  	 	 refine {{ ( ( #{sell} ) ^^ OrderInfo.amount ) -= !{deal_amount} ; { _ } }} . 
 	 	 refine {{ ( ( #{buy} ) ^^ OrderInfo.amount ) -= !{deal_amount} ; { _ } }} . *)

 	 	 refine {{ new 'cost : ( XMaybe XInteger ) @ "cost" := calc_cost_ ( !{deal_amount} , _price_ ) ; { _ } }} .
 
 	 	 refine {{ new 'sell_costs : ( XInteger128 ) @ "sell_costs" := 0 ; { _ } }} . 
 	 	 refine {{ new 'buy_costs : ( XInteger128 ) @ "buy_costs" := ((!{cost}) -> get_default ()) ; { _ } }} . 

 	 	 refine {{ if ( !{last_tip3_sell} ) then { { _:UExpressionP (XBool * (XBool * XInteger128)) false } } 
                                          else { { _:UExpressionP (XBool * (XBool * XInteger128)) false } } ; { _ } }} . 
 	 	 	 refine {{ {sell_costs} += ( (_tons_cfg_ ^^ TonsConfig.transfer_tip3) + 
                                   (_tons_cfg_ ^^ TonsConfig.send_notify) ) }} .
 
 	 	 refine {{ {buy_costs} += ( (_tons_cfg_ ^^ TonsConfig.transfer_tip3) +
                                (_tons_cfg_ ^^ TonsConfig.send_notify) ) }} . 

 	 	 refine {{ new 'sell_out_of_tons : ( XBool ) @ "sell_out_of_tons" := 
                  ( ((#{sell}) ^^ OrderInfo.account) < !{sell_costs} ) ; { _ } }} . 
 	 	 refine {{ new 'buy_out_of_tons : ( XBool ) @ "buy_out_of_tons" := 
                 ( ((#{buy}) ^^ OrderInfo.account) < !{buy_costs} ) ; { _ } }} . 

 	 	 refine {{ if ( !{sell_out_of_tons} \\ !{buy_out_of_tons} ) 
                  then { { _ :UExpressionP (XBool * (XBool * XInteger128)) false} } ; { _ } }} . 
 	 	 	 refine {{ return_ [ !{ sell_out_of_tons } , !{ buy_out_of_tons } , 0 ] }} . 
 	 	 (* refine {{ ((#{sell}) ^^ OrderInfo.account) -= !{sell_costs} ; { _ } }} . 
 	 	 refine {{ ((#{buy})  ^^ OrderInfo.account) - = !{buy_costs} ; { _ } }} . *) 
(*  	 	 refine {{ ITONTokenWalletPtr ( sell . tip3_wallet ) ( Grams ( tons_cfg_ . transfer_tip3 . get ( ) ) ) . transfer ( sell . tip3_wallet , buy . tip3_wallet , deal_amount , uint128 ( 0 ) , bool_t { false } ) ; { _ } }} .  *)
(*  	 	 refine {{ tvm.transfer ( sell . client_addr , cost - > get ( ) , true , SENDER_WANTS_TO_PAY_FEES_SEPARATELY ) ; { _ } }} .  *)
(*  	 	 refine {{ notify_addr_ ( Grams ( _tons_cfg_ ^^ TonsConfig.send_notify ) ) . onDealCompleted ( _tip3root_ , _price_ , !{deal_amount} ) ; { _ } }} .  *)
 	 	 refine {{ return_ [ FALSE , FALSE , !{ deal_amount } ] }} . 
Defined .

 Definition make_deal_right { a1 a2 }  
( sell : URValue ( OrderInfoLRecord ) a1 ) 
( buy : URValue ( OrderInfoLRecord ) a2 ) 
: URValue ( XBool * (XBool * XInteger128) ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) make_deal 
 sell buy ) . 
 
 Notation " 'make_deal_' '(' sell ',' buy ')' " := 
 ( make_deal_right 
 sell buy ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , buy custom URValue at level 0 ) : ursus_scope .

Parameter safe_delay_period : XInteger.
Definition is_active_time ( order_finish_time : ( XInteger32 ) ) : UExpression XBool false . 
 	 	 refine {{ return_ ( ( (tvm.now ()) +  (#{safe_delay_period}) ) < (#{order_finish_time} ) ) }} . 
 Defined . 
 
 Definition is_active_time_right { a1 }  ( order_finish_time : URValue ( XInteger32 ) a1 ) : URValue XBool a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) is_active_time 
 order_finish_time ) . 
 
 Notation " 'is_active_time_' '(' order_finish_time ')' " := 
 ( is_active_time_right 
 order_finish_time ) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope .

Definition EAO := UExpression (( XMaybe (XInteger # OrderInfoLRecord) ) # ( ( XQueue OrderInfoLRecord ) # XInteger128 ) ) false .
Definition extract_active_order 
( cur_order : ( XMaybe (XInteger * OrderInfoLRecord) ) ) 
( orders : ( XQueue OrderInfoLRecord ) ) 
( all_amount : ( XInteger128 ) ) ( sell : ( XBool ) ) 
: EAO  . 

 	 	 refine {{ if ( #{ cur_order } ) then { { _: EAO } } ; { _ } }} . 
 	 	 	 refine {{ return_ [ (#{ cur_order }) , (#{ orders }) , (#{ all_amount }) ] }} .
 
 	 	 refine {{ while ( ~ ((#{orders}) -> empty ()) ) do { { _:EAO } } ; { _ } }} . 
(*  	 	 	 refine {{ (#{cur_order}) := (#{orders}) ^^ OrderInfo ->front_with_idx_opt () ; { _ } }} .  *)
 	 	 	 refine {{ new 'ord : ( OrderInfoLRecord ) @ "ord" := 
                               ( second ((#{cur_order}) -> get_default () )) ; { _ } }} . 
 	 	 	 refine {{ if ( ~ ( is_active_time_ ( (!{ord}) ^^ OrderInfo.order_finish_time ) ) )
                                  then { { _:EAO } } ; { _ } }} . 
(*  	 	 	 	 refine {{ (#{all_amount} -= (!{ord}) ^^ OrderInfo.amount ; { _ } }} .  *)
 	 	 	 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 	 	 	 
 	 	 	            [ 1 (*ec::expired*) , (!{ord}) ^^ OrderInfo.original_amount , 0 ] ; { _ } }} . 
(*  	 	 	 	 refine {{ IPriceCallbackPtr ( ord . client_addr ) ( Grams ( ord . account . get ( ) ) ) . onOrderFinished ( ret , sell ) ; { _ } }} .  *)
(*  	 	 	 	 refine {{ (#{orders} -> pop () ; { _ } }} .  *)
(*  	 	 	 	 refine {{ (#{cur_order} -> reset () ; { _ } }} .  *)
(*  	 	 	 	 refine {{ continue }} .  *)
(*  	 	 refine {{ break }} .  *)
    refine {{ return_ [ #{cur_order} , #{orders} , #{all_amount} ] }} . 

refine {{ return_ [ #{cur_order} , #{orders} , #{all_amount} ] }} . 
refine {{ return_ [ #{cur_order} , #{orders} , #{all_amount} ] }} . 
Defined .  

 Definition extract_active_order_right { a1 a2 a3 a4 }  
( cur_order : URValue ( XMaybe (XInteger*OrderInfoLRecord) ) a1 ) 
( orders : URValue ( XQueue OrderInfoLRecord ) a2 ) 
( all_amount : URValue ( XInteger128 ) a3 ) 
( sell : URValue ( XBool ) a4 ) 
: URValue (( XMaybe (XInteger # OrderInfoLRecord) ) # ( ( XQueue OrderInfoLRecord ) # XInteger128 ) )
 ( orb ( orb ( orb a4 a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) extract_active_order 
 cur_order orders all_amount sell ) . 
 
 Notation " 'extract_active_order_' '(' cur_order ',' orders ',' all_amount ',' sell ')' " := 
 ( extract_active_order_right 
 cur_order orders all_amount sell ) 
 (in custom URValue at level 0 , cur_order custom URValue at level 0 
 , orders custom URValue at level 0 
 , all_amount custom URValue at level 0 
 , sell custom URValue at level 0 ) : ursus_scope .
 
Definition process_queue 
( sell_idx : ( XInteger ) ) 
( buy_idx : ( XInteger ) ) 
: UExpression PhantomType false . 
 	 	 refine {{ new 'sell_opt : ( XMaybe (XInteger # OrderInfoLRecord) ) @ "sell_opt" := {} ; { _ } }} . 
 	 	 refine {{ new 'buy_opt : ( XMaybe (XInteger # OrderInfoLRecord) ) @ "buy_opt" := {} ; { _ } }} . 
 	 	 refine {{ new 'deals_count : ( XInteger ) @ "deals_count" := 0 ; { _ } }} . 
 	 	 refine {{ while ( TRUE ) do { { _ : UExpression PhantomType false} } ; { _ } }} . 
 	 	 	 refine {{ [ {sell_opt} , _sells_ , _sells_amount_ ] := 
             extract_active_order_ ( !{sell_opt} , _sells_ , _sells_amount_ , TRUE ) ; { _ } }} . 
 	 	 	 refine {{ [ {buy_opt} , _buys_ , _buys_amount_ ] := 
             extract_active_order_ ( !{buy_opt} , _buys_ , _buys_amount_ , FALSE ) ; { _ } }} . 
 	 	 	 refine {{ if ( (~ (!{ sell_opt })) \\ (~ (!{ buy_opt })) ) 
                    then { { _: UExpression PhantomType false } } }} . 
 	 	 	 	 refine {{ return_ {} (* break *) }} . 
 	 	 refine {{ new ( 'sell_idx_cur : XInteger , 'sell : OrderInfoLRecord ) @
                ( "sell_idx_cur" , "sell" ) := (!{sell_opt}) -> get_default () ; { _ } }} .
 	 	 refine {{ new ( 'buy_idx_cur : XInteger , 'buy : OrderInfoLRecord ) @
                ( "buy_idx_cur" , "buy" ) := (!{buy_opt}) -> get_default () ; { _ } }} .
 	 	 	 refine {{ new 'sell_out_of_tons : ( XBool ) @ "sell_out_of_tons" := FALSE ; { _ } }} . 
 	 	 	 refine {{ new 'buy_out_of_tons : ( XBool ) @ "buy_out_of_tons" := FALSE ; { _ } }} . 
 	 	 	 refine {{ new 'deal_amount : ( XInteger128 ) @ "deal_amount" := 0 ; { _ } }} . 

 	 	 	 refine {{ if ( ++ ({ deals_count }) > _deals_limit_ ) 
                      then { { _: UExpression PhantomType false } } ; { _ } }} . 
 	 	 	 	 refine {{ new 'half_process_queue : XInteger @ "half_process_queue" 
                         := (_tons_cfg_ ^^ TonsConfig.process_queue) / #{2} ; { _ } }} . 
 	 	 	 	 refine {{ new 'safe_extra : ( XInteger ) @ "safe_extra" := 
                        (_tons_cfg_ ^^ TonsConfig.return_ownership) + 
                        (_tons_cfg_ ^^ TonsConfig.order_answer ) ; { _ } }} . 
 	 	 	 	 refine {{ if ( (!{sell} ^^ OrderInfo.account) < 
                     (!{half_process_queue} + !{ safe_extra }) ) 
                            then { { _: UEf } } ; { _ } }} .
 	 	 	 	 	 refine {{ {sell_out_of_tons} := TRUE }} . 
 	 	 	 refine {{ if ( ( (!{buy}) ^^ OrderInfo.account )
                        < !{half_process_queue} + !{ safe_extra } ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ {buy_out_of_tons} := TRUE }} . 
 	 	   refine {{ if ( (~ !{ sell_out_of_tons } ) && (~ !{ buy_out_of_tons } ) ) 
                        then { { _:UEf } } ; { _ } }} . 	 	 	 
         refine {{ ({sell} ^^ OrderInfo.account) -= !{half_process_queue} ; { _ } }} . 
 	 	 	   refine {{ ({buy} ^^ OrderInfo.account) -= !{half_process_queue} ; { _ } }} . 
(*  	 	 	 refine {{ IPricePtr ( address { tvm.address ( ) } ) ( Grams ( tons_cfg_ . process_queue . get ( ) ) ) . processQueue ( ) ; { _ } }} .  *)
 	 	 	     refine {{ if ( (#{sell_idx}) == !{sell_idx_cur} ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 (* refine {{ dealer.ret_ := [ 1 (* ec::deals_limit *) , 
                              ((!{sell}) ^^ OrderInfo.original_amount) - 
                              ((!{sell}) ^^ OrderInfo.amount) , 
                              ((!{sell}) ^^ OrderInfo.amount) ] }} . *)
 	 	 	 refine {{ if ( (#{ buy_idx }) == !{ buy_idx_cur } ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 (* refine {{ dealer.ret_ := [ 1 (* ec::deals_limit *) , 
                              ((!{buy}) ^^ OrderInfo.original_amount) - 
                              ((!{buy}) ^^ OrderInfo.amount) , 
                              ((!{buy}) ^^ OrderInfo.amount) ] }} . *)
 	 	 	 refine {{ {sell} := {} (* break *) }} . 

refine {{ {sell} := {} }} . (* TODO Delete! *)
refine {{ {sell} := {} }} . (* TODO Delete! *)

 refine {{ if ( (~ !{ sell_out_of_tons }) && (~ !{ buy_out_of_tons }) ) then { { _:UEf } } ; { _ } }} . 
 
 	 refine {{ [ {sell_out_of_tons} , {buy_out_of_tons} , {deal_amount} ] := 
                         make_deal_ ( !{sell} , !{buy} ) }} . 
 refine {{ if ( !{ sell_out_of_tons } ) then { { _:UEf } } ; { _ } }} . 
(*  	 refine {{ { sells_ . pop ( ) ; { _ } }} .  *)
 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	                      [ 1 (*ec::out_of_tons*) , 
                              ((!{sell}) ^^ OrderInfo.original_amount) - 
                              ((!{sell}) ^^ OrderInfo.amount) , 
                              ((!{sell}) ^^ OrderInfo.amount) ] ; { _ } }} .
 	 refine {{ if ( (#{ sell_idx }) == !{sell_idx_cur} ) then { { _:UEf } } ; { _ } }} . 
 	 	 refine {{ (* dealer.ret_ *) {ret} := !{ ret } }} . 
 	 refine {{ if ( ((!{sell}) ^^ OrderInfo.account) > 
                (_tons_cfg_ ^^ TonsConfig.return_ownership) ) then { { _:UEf } } ; { _ } }} . 
 	 	 refine {{ (({sell}) ^^ OrderInfo.account) -= (_tons_cfg_ ^^ TonsConfig.return_ownership) (* ; { _ } }} . 
 	 	 refine {{ ITONTokenWalletPtr ( sell . tip3_wallet ) ( Grams ( tons_cfg_ . return_ownership . get ( ) ) ) . returnOwnership ( sell . amount ) ; { _ } }} . 
 	 	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { true } ) *) }} . 
 refine {{ {sell_opt} -> reset () }} . 

 refine {{ if ( !{buy_out_of_tons} ) then { { _:UEf } } ; { _ } }} . 
 	 (* refine {{ { dealer.buys_ -> pop () ; { _ } }} .  *)
 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	                      [ 1 (*ec::out_of_tons*),
                              ((!{buy}) ^^ OrderInfo.original_amount) - 
                              ((!{buy}) ^^ OrderInfo.amount) , 
                              0 ] ; { _ } }} .
 	 refine {{ if ( !{ buy_idx } == !{ buy_idx_cur } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 refine {{ ret_ := !{ ret } }} . 
 	 refine {{ IPriceCallbackPtr ( buy . client_addr ) ( Grams ( buy . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { false } ) ; { _ } }} . 
 	 refine {{ buy_opt ^^ OrderInfoWithIdx:reset ( ) }} . 
 refine {{ if ( !{ sell_out_of_tons } || !{ buy_out_of_tons } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 refine {{ continue }} . 
 refine {{ second({ sell_opt }) = #{sell} ; { _ } }} . 
 refine {{ { buy_opt } - > second = buy ; { _ } }} . 
 refine {{ sells_amount_ -= !{ deal_amount } ; { _ } }} . 
 refine {{ buys_amount_ -= !{ deal_amount } ; { _ } }} . 
 refine {{ if ( ! sell ^^ amount ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 refine {{ { sells_ . pop ( ) ; { _ } }} . 
 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	 [$ $] ; { _ } }} . 
 	 refine {{ if ( !{ sell_idx } == !{ sell_idx_cur } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 refine {{ ret_ := !{ ret } }} . 
 	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { true } ) ; { _ } }} . 
 	 refine {{ sell_opt ^^ OrderInfoWithIdx:reset ( ) }} . 
 refine {{ if ( ! buy ^^ amount ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 refine {{ { buys_ . pop ( ) ; { _ } }} . 
 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 
 	 	 	 [$ $] ; { _ } }} . 
 	 refine {{ if ( !{ buy_idx } == !{ buy_idx_cur } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 refine {{ ret_ := !{ ret } }} . 
 	 refine {{ IPriceCallbackPtr ( buy . client_addr ) ( Grams ( buy . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { false } ) ; { _ } }} . 
 	 refine {{ buy_opt ^^ OrderInfoWithIdx:reset ( ) }} . 
 refine {{ if ( !{ sell_opt } && !{ sell_opt } - > second ^^ amount ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 refine {{ { auto sell = sell_opt - > second ; { _ } }} . 
 	 refine {{ sells_ ^^ change_front ( sell ) ; { _ } }} . 
 	 refine {{ if ( !{ sell_idx } == !{ sell_opt } - > first ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 refine {{ ret_ := OrderRet { ok , sell ^^ original_amount - sell ^^ amount , sell ^^ amount } }} . 
 refine {{ if ( !{ buy_opt } && !{ buy_opt } - > second ^^ amount ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 refine {{ { auto buy = buy_opt - > second ; { _ } }} . 
 	 refine {{ buys_ ^^ change_front ( buy ) ; { _ } }} . 
 	 refine {{ if ( !{ buy_idx } == !{ buy_opt } - > first ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 refine {{ ret_ := OrderRet { ok , buy ^^ original_amount - buy ^^ amount , buy ^^ amount } }} . 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 Defined . 
 
 
 
 
 Definition onTip3LendOwnership ( answer_addr : ( XAddress ) ) ( balance : ( XInteger128 ) ) ( lend_finish_time : ( XInteger32 ) ) ( pubkey : ( XInteger256 ) ) ( internal_owner : ( XAddress ) ) ( payload : ( XCell ) ) : UExpression OrderRetLRecord false . 
 	 	 refine {{ tip3_wallet : ( auto ) @ "tip3_wallet" ; { _ } }} . 
 	 	 refine {{ value : ( auto ) @ "value" ; { _ } }} . 
 	 	 refine {{ [ { tip3_wallet } , { value } ] := int_sender_and_value ( ) ; { _ } }} . 
 	 	 refine {{ ITONTokenWalletPtr wallet_in ( tip3_wallet ) ; { _ } }} . 
 	 	 refine {{ Grams ret_owner_gr ( tons_cfg_ . return_ownership . get ( ) ) ; { _ } }} . 
 	 	 refine {{ set_int_sender ( answer_addr ) ; { _ } }} . 
 	 	 refine {{ set_int_return_value ( tons_cfg_ . order_answer . get ( ) ) ; { _ } }} . 
 	 	 refine {{ new 'min_value : ( auto ) @ "min_value" := {} ; { _ } }} . 
 	 	 refine {{ { min_value } := onTip3LendOwnershipMinValue ( ) ; { _ } }} . 
 	 	 refine {{ new 'args : ( auto ) @ "args" := {} ; { _ } }} . 
 	 	 refine {{ { args } := parse ( payload . ctos ( ) ) ; { _ } }} . 
 	 	 refine {{ new 'amount : ( auto ) @ "amount" := {} ; { _ } }} . 
 	 	 refine {{ { amount } := args ^^ auto:amount ; { _ } }} . 
 	 	 refine {{ new 'err : ( XInteger ) @ "err" := {} ; { _ } }} . 
 	 	 refine {{ { err } := 0 ; { _ } }} . 
 	 	 refine {{ if ( value ^^ get ( ) < !{ min_value } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { err } := ec : : not_enough_tons_to_process }} . 
 	 	 refine {{ if ( ! verify_tip3_addr ( !{ tip3_wallet } , !{ pubkey } , std : : get < addr_std > ( internal_owner ^^ XAddress:val ( ) ) . address ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { err } := ec : : unverified_tip3_wallet }} . 
 	 	 refine {{ if ( !{ amount } < min_amount_ ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { err } := ec : : not_enough_tokens_amount }} . 
 	 	 refine {{ if ( !{ balance } < !{ amount } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { err } := ec : : too_big_tokens_amount }} . 
 	 	 refine {{ if ( ! calc_cost ( !{ amount } , price_ ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { err } := ec : : too_big_tokens_amount }} . 
 	 	 refine {{ if ( ! is_active_time ( !{ lend_finish_time } ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { err } := ec : : expired }} . 
 	 	 refine {{ if ( !{ err } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ return_ on_sell_fail ( !{ err } , wallet_in , !{ amount } ) }} . 
 	 	 refine {{ new 'account : ( XInteger128 ) @ "account" := {} ; { _ } }} . 
 	 	 refine {{ { account } := value . get ( ) - tons_cfg_ ^^ process_queue - tons_cfg_ ^^ order_answer ; { _ } }} . 
 	 	 refine {{ new 'sell : ( OrderInfoLRecord ) @ "sell" := 	 	 
 	 	 	 [$ $] ; { _ } }} . 
 	 	 refine {{ sells_ ^^ push ( sell ) ; { _ } }} . 
 	 	 refine {{ sells_amount_ += sell ^^ OrderInfo:amount ; { _ } }} . 
 	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderAdded ( bool_t { true } , tip3cfg_ . root_address , price_ , sell . amount , sells_amount_ ) ; { _ } }} . 
 	 	 refine {{ sells_amount : ( auto ) @ "sells_amount" ; { _ } }} . 
 	 	 refine {{ sells : ( auto ) @ "sells" ; { _ } }} . 
 	 	 refine {{ buys_amount : ( auto ) @ "buys_amount" ; { _ } }} . 
 	 	 refine {{ buys : ( auto ) @ "buys" ; { _ } }} . 
 	 	 refine {{ ret : ( auto ) @ "ret" ; { _ } }} . 
 	 	 refine {{ [ { sells_amount } , { sells } , { buys_amount } , { buys } , { ret } ] := process_queue_impl ( tip3cfg_ . root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , sells_ . back_with_idx ( ) . first , 0 , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; { _ } }} . 
 	 	 refine {{ sells_ := sells ; { _ } }} . 
 	 	 refine {{ buys_ := buys ; { _ } }} . 
 	 	 refine {{ sells_amount_ := !{ sells_amount } ; { _ } }} . 
 	 	 refine {{ buys_amount_ := buys_amount ; { _ } }} . 
 	 	 refine {{ if ( sells_ ^^ empty ( ) && buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ suicide ( flex_ ) }} . 
 	 	 refine {{ if ( ret ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ return_ *ret }} . 
 	 	 refine {{ return_ [ ok , 0 , sell ^^ OrderInfo:amount ] ; { _ } }} . 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 Defined . 
 
 
 
 
 Definition buyTip3 ( amount : ( XInteger128 ) ) ( receive_tip3_wallet : ( XAddress ) ) ( order_finish_time : ( XInteger32 ) ) : UExpression OrderRetLRecord true . 
 	 	 refine {{ sender : ( auto ) @ "sender" ; { _ } }} . 
 	 	 refine {{ value_gr : ( auto ) @ "value_gr" ; { _ } }} . 
 	 	 refine {{ [ { sender } , { value_gr } ] := int_sender_and_value ( ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( !{ amount } >= min_amount_ ) , ec : : not_enough_tokens_amount ) ; { _ } }} . 
 	 	 refine {{ new 'cost : ( auto ) @ "cost" := {} ; { _ } }} . 
 	 	 refine {{ { cost } := calc_cost ( !{ amount } , price_ ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( ! ! !{ cost } ) , ec : : too_big_tokens_amount ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( value_gr ^^ get ( ) > buyTip3MinValue ( *cost ) ) , ec : : not_enough_tons_to_process ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( is_active_time ( !{ order_finish_time } ) ) , ec : : expired ) ; { _ } }} . 
 	 	 refine {{ set_int_return_value ( tons_cfg_ . order_answer . get ( ) ) ; { _ } }} . 
 	 	 refine {{ new 'account : ( XInteger128 ) @ "account" := {} ; { _ } }} . 
 	 	 refine {{ { account } := value_gr . get ( ) - tons_cfg_ ^^ process_queue - tons_cfg_ ^^ order_answer ; { _ } }} . 
 	 	 refine {{ new 'buy : ( OrderInfoLRecord ) @ "buy" := 	 	 refine {{ { buy } := [ ] amount , amount , account , receive_tip3_wallet , sender , order_finish_time } ; { _ } }} . 
 	 	 refine {{ buys_ ^^ push ( buy ) ; { _ } }} . 
 	 	 refine {{ buys_amount_ += buy ^^ OrderInfo:amount ; { _ } }} . 
 	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderAdded ( bool_t { false } , tip3cfg_ . root_address , price_ , buy . amount , buys_amount_ ) ; { _ } }} . 
 	 	 refine {{ sells_amount : ( auto ) @ "sells_amount" ; { _ } }} . 
 	 	 refine {{ sells : ( auto ) @ "sells" ; { _ } }} . 
 	 	 refine {{ buys_amount : ( auto ) @ "buys_amount" ; { _ } }} . 
 	 	 refine {{ buys : ( auto ) @ "buys" ; { _ } }} . 
 	 	 refine {{ ret : ( auto ) @ "ret" ; { _ } }} . 
 	 	 refine {{ [ { sells_amount } , { sells } , { buys_amount } , { buys } , { ret } ] := process_queue_impl ( tip3cfg_ . root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , 0 , buys_ . back_with_idx ( ) . first , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; { _ } }} . 
 	 	 refine {{ sells_ := sells ; { _ } }} . 
 	 	 refine {{ buys_ := buys ; { _ } }} . 
 	 	 refine {{ sells_amount_ := !{ sells_amount } ; { _ } }} . 
 	 	 refine {{ buys_amount_ := buys_amount ; { _ } }} . 
 	 	 refine {{ if ( sells_ ^^ empty ( ) && buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ suicide ( flex_ ) }} . 
 	 	 refine {{ if ( ret ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ return_ *ret }} . 
 	 	 refine {{ return_ [ ok , 0 , buy ^^ OrderInfo:amount ] ; { _ } }} . 
 
 
 Defined . 
 
 
 
 
 Definition processQueue : UExpression PhantomType false . 
 	 	 refine {{ if ( sells_ ^^ empty ( ) || buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ return_ }} . 
 	 	 refine {{ sells_amount : ( auto ) @ "sells_amount" ; { _ } }} . 
 	 	 refine {{ sells : ( auto ) @ "sells" ; { _ } }} . 
 	 	 refine {{ buys_amount : ( auto ) @ "buys_amount" ; { _ } }} . 
 	 	 refine {{ buys : ( auto ) @ "buys" ; { _ } }} . 
 	 	 refine {{ ret : ( auto ) @ "ret" ; { _ } }} . 
 	 	 refine {{ [ { sells_amount } , { sells } , { buys_amount } , { buys } , { ret } ] := process_queue_impl ( tip3cfg_ . root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , 0 , 0 , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; { _ } }} . 
 	 	 refine {{ sells_ := sells ; { _ } }} . 
 	 	 refine {{ buys_ := buys ; { _ } }} . 
 	 	 refine {{ sells_amount_ := !{ sells_amount } ; { _ } }} . 
 	 	 refine {{ buys_amount_ := buys_amount ; { _ } }} . 
 	 	 refine {{ if ( sells_ ^^ empty ( ) && buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ suicide ( flex_ ) }} . 
 
 
 Defined . 
 
 
 
 
 Definition cancelSell : UExpression PhantomType false . 
 	 	 refine {{ new 'canceled_amount : ( auto ) @ "canceled_amount" := {} ; { _ } }} . 
 	 	 refine {{ { canceled_amount } := sells_amount_ ; { _ } }} . 
 	 	 refine {{ new 'client_addr : ( addr_std_fixedLRecord ) @ "client_addr" := {} ; { _ } }} . 
 	 	 refine {{ { client_addr } := int_sender ( ) ; { _ } }} . 
 	 	 refine {{ new 'value : ( auto ) @ "value" := {} ; { _ } }} . 
 	 	 refine {{ { value } := int_value ( ) ; { _ } }} . 
 	 	 refine {{ sells : ( auto ) @ "sells" ; { _ } }} . 
 	 	 refine {{ sells_amount : ( auto ) @ "sells_amount" ; { _ } }} . 
 	 	 refine {{ [ { sells } , { sells_amount } ] := cancel_order_impl ( sells_ , client_addr , sells_amount_ , bool_t { true } , Grams ( tons_cfg_ . return_ownership . get ( ) ) , Grams ( tons_cfg_ . process_queue . get ( ) ) , value ) ; { _ } }} . 
 	 	 refine {{ sells_ := !{ sells } ; { _ } }} . 
 	 	 refine {{ sells_amount_ := sells_amount ; { _ } }} . 
 	 	 refine {{ { canceled_amount } -= sells_amount ; { _ } }} . 
 	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderCanceled ( bool_t { true } , tip3cfg_ . root_address , price_ , canceled_amount , sells_amount_ ) ; { _ } }} . 
 	 	 refine {{ if ( sells_ ^^ empty ( ) && buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ suicide ( flex_ ) }} . 
 
 Defined . 
 
 
 
 
 Definition cancelBuy : UExpression PhantomType false . 
 	 	 refine {{ new 'canceled_amount : ( auto ) @ "canceled_amount" := {} ; { _ } }} . 
 	 	 refine {{ { canceled_amount } := buys_amount_ ; { _ } }} . 
 	 	 refine {{ new 'client_addr : ( addr_std_fixedLRecord ) @ "client_addr" := {} ; { _ } }} . 
 	 	 refine {{ { client_addr } := int_sender ( ) ; { _ } }} . 
 	 	 refine {{ new 'value : ( auto ) @ "value" := {} ; { _ } }} . 
 	 	 refine {{ { value } := int_value ( ) ; { _ } }} . 
 	 	 refine {{ buys : ( auto ) @ "buys" ; { _ } }} . 
 	 	 refine {{ buys_amount : ( auto ) @ "buys_amount" ; { _ } }} . 
 	 	 refine {{ [ { buys } , { buys_amount } ] := cancel_order_impl ( buys_ , client_addr , buys_amount_ , bool_t { false } , Grams ( tons_cfg_ . return_ownership . get ( ) ) , Grams ( tons_cfg_ . process_queue . get ( ) ) , value ) ; { _ } }} . 
 	 	 refine {{ buys_ := !{ buys } ; { _ } }} . 
 	 	 refine {{ buys_amount_ := buys_amount ; { _ } }} . 
 	 	 refine {{ { canceled_amount } -= buys_amount ; { _ } }} . 
 	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderCanceled ( bool_t { false } , tip3cfg_ . root_address , price_ , canceled_amount , buys_amount_ ) ; { _ } }} . 
 	 	 refine {{ if ( sells_ ^^ empty ( ) && buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ suicide ( flex_ ) }} . 
 
 Defined . 
 
 
 
 
 Definition getDetails : UExpression DetailsInfoLRecord false . 
 	 	 refine {{ return_ [ getPrice ( ) , getMinimumAmount ( ) , getSellAmount ( ) , getBuyAmount ( ) ] ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition getPrice : UExpression XInteger128 false . 
 	 	 refine {{ return_ price_ ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition getMinimumAmount : UExpression XInteger128 false . 
 	 	 refine {{ return_ min_amount_ ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition getTonsCfg : UExpression TonsConfigLRecord false . 
 	 	 refine {{ return_ tons_cfg_ ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition getSells : UExpression ( XHMap XInteger OrderInfoLRecord ) false . 
 	 	 refine {{ return_ dict_array ( sells_ . begin ( ) , sells_ . end ( ) ) ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition getBuys : UExpression ( XHMap XInteger OrderInfoLRecord ) false . 
 	 	 refine {{ return_ dict_array ( buys_ . begin ( ) , buys_ . end ( ) ) ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition getSellAmount : UExpression XInteger128 false . 
 	 	 refine {{ return_ sells_amount_ ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition getBuyAmount : UExpression XInteger128 false . 
 	 	 refine {{ return_ buys_amount_ ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition _fallback ( cell : ( (LRecord ) ) : UExpression XInteger false . 
 	 	 refine {{ return_ 0 ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition onTip3LendOwnershipMinValue : UExpression XInteger128 false . 
 	 	 refine {{ return_ tons_cfg_ ^^ process_queue + tons_cfg_ ^^ transfer_tip3 + tons_cfg_ ^^ send_notify + tons_cfg_ ^^ return_ownership + tons_cfg_ ^^ order_answer ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition buyTip3MinValue ( buy_cost : ( XInteger128 ) ) : UExpression XInteger128 false . 
 	 	 refine {{ return_ !{ buy_cost } + tons_cfg_ ^^ process_queue + tons_cfg_ ^^ transfer_tip3 + tons_cfg_ ^^ send_notify + tons_cfg_ ^^ order_answer ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition verify_tip3_addr ( tip3_wallet : ( XAddress ) ) ( wallet_pubkey : ( XInteger256 ) ) ( internal_owner : ( XInteger256 ) ) : UExpression XBool false . 
 	 	 refine {{ new 'expected_address : ( auto ) @ "expected_address" := {} ; { _ } }} . 
 	 	 refine {{ { expected_address } := expected_wallet_address ( !{ wallet_pubkey } , !{ internal_owner } ) ; { _ } }} . 
 	 	 refine {{ return_ Std :: get < addr_std > ( !{ tip3_wallet } ( ) ) . address == !{ expected_address } ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition expected_wallet_address ( wallet_pubkey : ( XInteger256 ) ) ( internal_owner : ( XInteger256 ) ) : UExpression XInteger256 false . 
 	 	 refine {{ new owner_addr : ( XMaybe XAddress ) @ "owner_addr" ; { _ } }} . 
 	 	 refine {{ if ( !{ internal_owner } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { owner_addr } := Address :: make_std ( workchain_id_ , !{ internal_owner } ) }} . 
 	 	 refine {{ return_ prepare_internal_wallet_state_init_and_addr ( tip3cfg_ ^^ name , tip3cfg_ ^^ symbol , tip3cfg_ ^^ decimals , tip3cfg_ ^^ root_public_key , !{ wallet_pubkey } , tip3cfg_ ^^ root_address , !{ owner_addr } , tip3_code_ , workchain_id_ ) . second ; { _ } }} . 
 
 Defined . 
 
 
 
 
 Definition on_sell_fail ( ec : ( XInteger ) ) ( wallet_in : ( ITONTokenWalletPtrLRecord ) ) ( amount : ( XInteger128 ) ) : UExpression OrderRetLRecord false . 
 	 	 refine {{ { wallet_in } ( Grams ( tons_cfg_ . return_ownership . get ( ) ) ) . returnOwnership ( amount ) ; { _ } }} . 
 	 	 refine {{ if ( sells_ ^^ empty ( ) && buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { set_int_return_flag ( SEND_ALL_GAS | DELETE_ME_IF_I_AM_EMPTY ) }} . 
 	 refine {{ { auto incoming_value = int_value ( ) . get ( ) ; { _ } }} . 
 	 refine {{ tvm.rawreserve ( tvm.balance ( ) - incoming_value , rawreserve_flag : : up_to ) ; { _ } }} . 
 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) }} . 
 refine {{ return_ [ ec , { } , { } ] ; { _ } }} . 
 
 
 Defined . 
 
 
 
 
 Definition prepare_price_state_init_and_addr ( price_data : ( DPriceLRecord ) ) ( price_code : ( XCell ) ) : UExpression ( StateInitLRecord * XInteger256 ) false . 
 	 	 refine {{ new 'price_data_cl : ( XCell ) @ "price_data_cl" := {} ; { _ } }} . 
 	 	 refine {{ { price_data_cl } := prepare_persistent_data ( { } , price_data ) ; { _ } }} . 
 	 	 refine {{ new 'price_init : ( StateInitLRecord ) @ "price_init" := 	 	 refine {{ { price_init } := [ ] { } , { } , price_code , price_data_cl , { } } ; { _ } }} . 
 	 	 refine {{ new 'price_init_cl : ( XCell ) @ "price_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ { price_init_cl } := build ( !{ price_init } ) . make_cell ( ) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ price_init } , tvm.hash ( price_init_cl ) ] ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition is_active_time ( order_finish_time : ( XInteger32 ) ) : UExpression XBool false . 
 	 	 refine {{ return_ tvm_now ( ) + safe_delay_period ( ) ; { _ } }} . 
 Defined . 
 
 
 
 
 
 
 
 
 Definition process_queue_impl ( tip3root : ( XAddress ) ) ( notify_addr : ( IFlexNotifyPtrLRecord ) ) ( price : ( XInteger128 ) ) ( deals_limit : ( XInteger8 ) ) ( tons_cfg : ( TonsConfigLRecord ) ) ( sell_idx : ( XInteger ) ) ( buy_idx : ( XInteger ) ) ( sells_amount : ( XInteger128 ) ) ( sells : ( XQueue OrderInfoLRecord ) ) ( buys_amount : ( XInteger128 ) ) ( buys : ( XQueue OrderInfoLRecord ) ) : UExpression process_retLRecord false . 
 	 	 refine {{ new 'd : ( dealerLRecord ) @ "d" := 	 	 
 	 	 	 [$ $] ; { _ } }} . 
 	 	 refine {{ d ^^ dealer:process_queue ( sell_idx , buy_idx ) ; { _ } }} . 
 	 	 refine {{ return_ [ d ^^ dealer:sells_amount_ , d ^^ dealer:sells_ , d ^^ dealer:buys_amount_ , d ^^ dealer:buys_ , d ^^ dealer:ret_ ] ; { _ } }} . 
 Defined . 
 
 
 
 
 Definition cancel_order_impl ( orders : ( XQueue OrderInfoLRecord ) ) ( client_addr : ( addr_std_fixedLRecord ) ) ( all_amount : ( XInteger128 ) ) ( sell : ( XBool ) ) ( return_ownership : ( GramsLRecord ) ) ( process_queue : ( GramsLRecord ) ) ( incoming_val : ( GramsLRecord ) ) : UExpression XQueue OrderInfoLRecord false . 
 	 	 refine {{ new 'is_first : ( XBool ) @ "is_first" := {} ; { _ } }} . 
 	 	 refine {{ { is_first } := true ; { _ } }} . 
 	 	 refine {{ for ( auto it = orders ^^ OrderInfoLRecord:begin ( ) ; it != orders ^^ OrderInfoLRecord:end ( ) ; ) { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { auto next_it = std : : next ( it ) ; { _ } }} . 
 	 	 	 refine {{ new 'ord : ( auto ) @ "ord" := {} ; { _ } }} . 
 	 	 	 refine {{ { ord } := *it ; { _ } }} . 
 	 	 	 refine {{ if ( ord ^^ auto:client_addr == !{ client_addr } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 	 refine {{ { unsigned minus_val = is_first ? process_queue . get ( ) : 0 ; { _ } }} . 
 	 	 	 	 refine {{ if ( !{ sell } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 	 	 refine {{ { ITONTokenWalletPtr ( ord . tip3_wallet ) ( return_ownership ) . returnOwnership ( ord . amount ) ; { _ } }} . 
 	 	 	 	 	 refine {{ minus_val += return_ownership ^^ GramsLRecord:get ( ) }} . 
 	 	 	 refine {{ new 'plus_val : ( XInteger ) @ "plus_val" := {} ; { _ } }} . 
 	 	 	 refine {{ { plus_val } := ord ^^ auto:account . get ( ) + ( !{ is_first } ? incoming_val ^^ GramsLRecord:get ( ) : 0 ) ; { _ } }} . 
 	 	 	 refine {{ { is_first } := false ; { _ } }} . 
 	 	 	 refine {{ if ( !{ plus_val } > minus_val ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 	 refine {{ { unsigned ret_val = plus_val - minus_val ; { _ } }} . 
 	 	 	 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 	 	 	 
 	 	 	 [$ $] ; { _ } }} . 
 	 	 	 	 refine {{ IPriceCallbackPtr ( ord . client_addr ) ( Grams ( ret_val ) ) . onOrderFinished ( ret , sell ) }} . 
 	 	 refine {{ { all_amount } -= ord ^^ auto:amount ; { _ } }} . 
 	 	 refine {{ orders ^^ OrderInfoLRecord:erase ( it ) }} . 
 refine {{ it := next_it }} . 
 refine {{ return_ [ !{ orders } , !{ all_amount } ] ; { _ } }} . 
 
 
 
 
 Defined . 
 
 
 
 
 .
 

End trainFuncsInternal.
End trainFuncs.








