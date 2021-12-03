Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.
Require Import UrsusTVM.Cpp.tvmTypes.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.
Require Import Project.CommonAxioms.

(*Fully qualified name are mandatory in multi-contract environment*)
Require Import PriceXchg.Ledger.
Require Import PriceXchg.Functions.FuncSig.
Require Import PriceXchg.Functions.FuncNotations.
(* Require Contracts.PriceXchg.Interface. *)

Require Import Contracts.Flex.ClassTypesNotations.
Require Import Contracts.TONTokenWallet.ClassTypesNotations.


Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.

Module Funcs (co : CompilerOptions) (dc : ConstsTypesSig XTypesModule StateMonadModule) .

Import co.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module Import TONTonkenWalletModuleForPriceXchg := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .

Module Import FlexModuleForPriceXchg := Contracts.Flex.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import TONTokenWalletModuleForPriceXchg := Contracts.TONTokenWallet.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module TONTokenWalletClassTypesModule := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .


Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Existing Instance LedgerPruvendoRecord.

Definition minor_cost (amount: uint128) (price: price_t) : UExpression (optional uint128) true . 
	refine {{ new 'cost : ( uint ) @ "cost" := {} 
			(* __builtin_tvm_muldivr ( amount ^^ uint128:get ( ) , price ^^ RationalPriceLRecord:num , price ^^ RationalPriceLRecord:denum ) *) ; { _ } }} . 
	refine {{ if ? ( !{cost} >> #{128} ) \\ 
	             !{cost} == 0 then { exit_ {} } ; { _ } }} . 		
	refine {{ return_ (!{ cost }) -> set () }} . 
Defined . 

Definition minor_cost_right {a1 a2} (amount: URValue uint128 a1) 
     								(price: URValue price_t a2) : URValue (optional uint128) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) minor_cost amount price ) . 

Notation " 'minor_cost_' '(' amount ',' price ')' " := ( minor_cost_right amount price ) 
 (in custom URValue at level 0 , amount custom URValue at level 0 , price custom URValue at level 0 ) : ursus_scope . 

Definition is_active_time ( order_finish_time : ( uint32 ) ) : UExpression boolean false .  
	refine {{ return_ ( tvm_now () + safe_delay_period_ ) 
					   <  #{order_finish_time} }} . 
Defined . 

Definition is_active_time_right { a1 }  ( order_finish_time : URValue uint32 a1 ) : URValue boolean a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) is_active_time order_finish_time ) . 
 
Notation " 'is_active_time_' '(' order_finish_time ')' " := (is_active_time_right order_finish_time) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope .


Section Dealer.

Variable this : ULValue dealerLRecord.

Definition make_deal ( sell : ULValue OrderInfoXchgLRecord ) 
					 ( buy : ULValue OrderInfoXchgLRecord ) 
					 : UExpression ( boolean # (boolean # uint128) ) true . 
	refine {{ new 'deal_amount : uint128 @ "deal_amount" := min ( !{sell} ↑ OrderInfoXchg.amount , !{buy} ↑ OrderInfoXchg.amount )  ; { _ } }} . 
	refine {{ new 'last_tip3_sell : boolean @ "last_tip3_sell" := !{deal_amount} == !{sell} ↑ OrderInfoXchg.amount ; { _ } }} .
	refine {{ new 'last_tip3_buy : boolean @ "last_tip3_buy" := !{deal_amount} == !{buy} ↑ OrderInfoXchg.amount ; { _ } }} .
	refine {{ new 'buy_payment : optional uint128 @ "buy_payment" := minor_cost_ ( !{deal_amount} , !{this} ↑ dealer.price_ ) ; { _ } }} . 
	refine {{ if  ~ !{ buy_payment }  then { { _: UEt } } ; { _ } }} . 
	refine {{ exit_ [ TRUE , TRUE , 0 ] }} . 
	refine {{ new 'sell_ton_costs : uint128 @ "sell_ton_costs" := 0 ; { _ } }} . 
	refine {{ new 'buy_ton_costs : uint128 @ "buy_ton_costs" := 0 ; { _ } }} . 
	refine {{ new 'transaction_costs : uint128 @ "transaction_costs" := (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3 * #{2}) + 
	                                                                    (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ; { _ } }} . 
	refine {{ if  !{ last_tip3_sell } then { { _:UEf } } else { { _:UEf } } ; { _ } }} . 
	refine {{ { sell_ton_costs } += !{ transaction_costs } }} . 
	refine {{ { buy_ton_costs } += !{ transaction_costs } }} . 
	refine {{ new 'sell_out_of_tons : boolean @ "sell_out_of_tons" := !{ sell_ton_costs } > !{sell} ↑ OrderInfoXchg.account ; { _ } }} . 
	refine {{ new 'buy_out_of_tons : boolean @ "buy_out_of_tons" := !{buy} ↑ OrderInfoXchg.account < !{ buy_ton_costs } ; { _ } }} . 
	refine {{ if  !{ sell_out_of_tons } \\ !{ buy_out_of_tons }  then { { _:UEt } } ; { _ } }} . 
	refine {{ exit_ [ !{ sell_out_of_tons } , !{ buy_out_of_tons } , 0 ] }} . 
	refine {{ {sell} ↑ OrderInfoXchg.amount -= !{deal_amount} ; { _ } }} . 
	refine {{ {buy} ↑ OrderInfoXchg.amount -= !{deal_amount} ; { _ } }} . 
	refine {{ {sell} ↑ OrderInfoXchg.account -= !{sell_ton_costs} ; { _ } }} . 
	refine {{ {buy} ↑ OrderInfoXchg.account -= !{buy_ton_costs} ; { _ } }} . 
(*  	 	 refine {{ ITONTokenWalletPtr ( (#{sell}) ↑ OrderInfoXchg.tip3_wallet_provide ) ( Grams ( tons_cfg_ . transfer_tip3 . get ( ) ) ) 
. transfer ( sell . tip3_wallet_provide , buy . tip3_wallet_receive , deal_amount , uint128 ( 0 ) , bool_t { false } ) ; { _ } }} .  *)
refine ( let sell_ptr := {{ ITONTokenWalletPtr [[ (!{sell} ↑ OrderInfoXchg.tip3_wallet_provide)  ]] }} in 
              {{ {sell_ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) ⇒ { Messsage_ι_value }  $] 
                                         ⤳ .transfer ( !{sell} ↑ OrderInfoXchg.tip3_wallet_provide , !{buy} ↑ OrderInfoXchg.tip3_wallet_receive ,
										 				 !{deal_amount} , 0 , FALSE ) ; {_} }} ).  
(*  	 	 refine {{ ITONTokenWalletPtr ( buy . tip3_wallet_provide ) ( Grams ( tons_cfg_ . transfer_tip3 . get ( ) ) ) . 
transfer ( buy . tip3_wallet_provide , sell . tip3_wallet_receive , *buy_payment , uint128 ( 0 ) , bool_t { false } ) ; { _ } }} .  *)
refine ( let buy_ptr := {{ ITONTokenWalletPtr [[ (!{buy} ↑ OrderInfoXchg.tip3_wallet_provide)  ]] }} in 
              {{ {buy_ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) ⇒ { Messsage_ι_value }  $] 
                                         ⤳ .transfer ( !{buy} ↑ OrderInfoXchg.tip3_wallet_provide , !{sell} ↑ OrderInfoXchg.tip3_wallet_receive ,
										 				 !{buy_payment}->get() , 0 , FALSE ) ; {_} }} ).  
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) )
 . onXchgDealCompleted ( tip3root_sell_ , tip3root_buy_ , price_ . num , price_ . denom , deal_amount ) ; { _ } }} .  *)
 refine ( let notify_addr__ptr := {{ IFlexNotifyPtr [[ !{this} ↑ dealer.notify_addr_  ]] }} in 
 {{ {notify_addr__ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ⇒ { Messsage_ι_value }  $] 
							⤳ .onXchgDealCompleted ( !{this} ↑ dealer.tip3root_sell_  , !{this} ↑ dealer.tip3root_buy_  ,
							 !{this} ↑ dealer.price_ ↑ RationalPrice.num , !{this} ↑ dealer.price_ ↑ RationalPrice.denum ,
											 !{deal_amount} ) ; {_} }} ).  
	refine {{ return_ [ FALSE , FALSE , !{ deal_amount } ] }} . 
Defined. 

Check make_deal.

Definition make_deal_right (sell : ULValue OrderInfoXchgLRecord) 
						   (buy : ULValue OrderInfoXchgLRecord) : URValue ( boolean # (boolean # uint128) ) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2LL ) make_deal sell buy ). 
 
Notation " 'make_deal_' '(' sell , buy ')' " := ( make_deal_right sell buy ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 , buy custom URValue at level 0 ) : ursus_scope . 

Definition extract_active_order  ( cur_order : optional OrderInfoXchgWithIdx  ) 
								 ( orders : queue OrderInfoXchgLRecord ) 
								 ( all_amount : uint128 ) 
							     ( sell : boolean ) : 
		  UExpression ( (optional OrderInfoXchgWithIdx ) # ( (queue OrderInfoXchgLRecord) # uint128 ) ) true . 
	vararg cur_order "cur_order".
	vararg orders "orders".
	vararg all_amount "all_amount".
	vararg sell "sell".

	refine {{ if !{ cur_order } then { { _:UEt } } ; { _ } }} . 
	refine {{ exit_ [ !{cur_order} , !{orders} , !{all_amount} ] }} . 

	refine {{ while !{orders} -> empty () do { { _:UEt } } ; { _ } }} . 
	refine {{ {cur_order} := !{orders} ->front_with_idx_opt () ; { _ } }} . 
	refine {{ new 'ord : OrderInfoXchgLRecord @ "ord" := second ( !{cur_order} -> get () ) ; { _ } }} . 
	refine {{ if ~ is_active_time_ ( !{ord} ↑ OrderInfoXchg.order_finish_time ) then { { _:UEt } } ; { _ } }} . 
	refine {{ {all_amount} -= !{ord} ↑ OrderInfoXchg.amount ; { _ } }} . 
	refine {{ new 'ret : OrderRetLRecord @ "ret" := [ ec::expired , 
	           !{ord} ↑ OrderInfoXchg.original_amount - !{ord} ↑ OrderInfoXchg.amount , 0 ] ; { _ } }} . 
	(* refine {{ IPriceCallbackPtr ( ord . client_addr ) ( Grams ( ord . account . get ( ) ) )
	. onOrderFinished ( ret , sell ) ; { _ } }} .  *)
	refine ( let ord_ptr := {{ IPriceCallBackPtr [[ (!{ord} ↑ OrderInfoXchg.client_addr)  ]] }} in 
              {{ {ord_ptr} with [$ (!{ord} ↑ OrderInfoXchg.account) ⇒ { Messsage_ι_value }  $] 
                                         ⤳ PriceXchg.onOrderFinished ( !{ret} , !{sell} ) ; {_} }} ).
	refine {{ {orders} -> pop () ; { _ } }} . 
	refine {{ {cur_order} -> reset () ; { _ } }} . 
	refine {{ continue_ }} . 
	refine {{ break_ }} . 
 	refine {{ return_ [ !{ cur_order } , !{ orders } , !{ all_amount } ] }} . 
Defined . 
 
Definition extract_active_order_right { a1 a2 a3 a4 }  
			( cur_order : URValue ( optional OrderInfoXchgWithIdx ) a1) 
			( orders : URValue ( queue OrderInfoXchgLRecord ) a2) 
			( all_amount : URValue uint128 a3 ) 
			( sell : URValue boolean a4 ) 
			: URValue ( (optional OrderInfoXchgWithIdx) # ( (queue OrderInfoXchgLRecord) # uint128 ) ) true  := 
	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) extract_active_order cur_order orders all_amount sell ) . 
 
Notation " 'extract_active_order_' '(' cur_order ,  orders , all_amount , sell ')' " := 
 ( extract_active_order_right cur_order orders all_amount sell ) 
 (in custom URValue at level 0 , cur_order custom URValue at level 0 , orders custom URValue at level 0 , 
 	all_amount custom URValue at level 0 , sell custom URValue at level 0 ) : ursus_scope .


Definition process_queue (sell_idx : uint) 
						 (buy_idx : uint) : UExpression PhantomType true . 
	refine {{ new 'sell_opt : optional OrderInfoXchgWithIdx @ "sell_opt" := {} ; { _ } }} . 
 	refine {{ new 'buy_opt  : optional OrderInfoXchgWithIdx @ "buy_opt"  := {} ; { _ } }} . 
 	refine {{ new 'deals_count : uint @ "deals_count" := 0 ; { _ } }} . 

 	refine {{ while TRUE do { { _:UEt } } ; { _ } }} . 
	refine {{ [ {sell_opt} , {this} ↑ dealer.sells_ , {this} ↑ dealer.sells_amount_ ] 
              := extract_active_order_ ( !{sell_opt} , !{this} ↑ dealer.sells_ , !{this} ↑ dealer.sells_amount_ , TRUE ) ; { _ } }} . 
	refine {{ if ~ !{sell_opt} \\ ~ !{buy_opt} then { { _:UEt } } ; { _ } }} . 
	refine {{ break_ }} . 
	refine {{ new ( 'sell_idx_cur : uint , 'sell : OrderInfoXchgLRecord ) @ ( "sell_idx_cur" , "sell" ) 
                                 := !{sell_opt} -> get () ; { _ } }} . 
	refine {{ new ( 'buy_idx_cur : uint , 'buy : OrderInfoXchgLRecord ) @ ( "sell_idx_cur" , "sell" ) 
                                 := !{buy_opt} -> get () ; { _ } }} . 
	refine {{ new 'sell_out_of_tons : boolean @ "sell_out_of_tons" := FALSE ; { _ } }} . 
	refine {{ new 'buy_out_of_tons : boolean @ "buy_out_of_tons" := FALSE ; { _ } }} . 
	refine {{ new 'deal_amount : uint128 @ "deal_amount" := 0 ; { _ } }} . 
	refine {{ if (++ {deals_count}) > !{this} ↑ dealer.deals_limit_  then { { _:UEt } } ; { _ } }} . 
	refine {{ new 'half_process_queue : uint @ "" := (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.process_queue) / #{2} ; { _ } }} . 
 	refine {{ new 'safe_extra : uint @ "safe_extra" := 
                (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.return_ownership) + 
				(!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.order_answer) ; { _ } }} . 
	refine {{ if !{sell} ↑ OrderInfoXchg.account < ! {half_process_queue} + !{ safe_extra }  then { { _:UEf } } ; { _ } }} . 
	refine {{ {sell_out_of_tons} := TRUE }} . 
	refine {{ if !{buy} ↑ OrderInfoXchg.account < !{half_process_queue} + !{ safe_extra } then { { _:UEf } } ; { _ } }} . 
	refine {{ { buy_out_of_tons } := TRUE }} . 
	refine {{ if ~ !{ sell_out_of_tons } && ~ !{ buy_out_of_tons } then { { _:UEt } }  }} . 
	refine {{ {sell} ↑ OrderInfoXchg.account -= !{half_process_queue} ; { _ } }} . 
	refine {{ {buy} ↑ OrderInfoXchg.account -= !{half_process_queue} ; { _ } }} . 
 (*	refine {{ IPriceXchgPtr ( address { tvm_myaddr ( ) } )
  ( Grams ( tons_cfg_ . process_queue . get ( ) ) ) . processQueue ( ) ; { _ } }} .  *)
 refine ( let tvm_myaddr_ptr := {{ IPriceXchgPtr [[ tvm_myaddr ()  ]] }} in 
{{ {tvm_myaddr_ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.process_queue) ⇒ { Messsage_ι_value }  $] 
						   ⤳ .processQueue () ; {_} }} ). 
 	refine {{ if #{sell_idx} == !{sell_idx_cur} then { { _:UEf } } ; { _ } }} . 
	refine {{ {this} ↑ dealer.ret_ -> set ( [ ec::deals_limit  , 
                                         !{sell} ↑ OrderInfoXchg.original_amount - 
                                         !{sell} ↑ OrderInfoXchg.amount , 
										 !{sell} ↑ OrderInfoXchg.amount ] )  }} .
	refine {{ if #{ buy_idx } == !{ buy_idx_cur } then { { _:UEf } } ; { _ } }} . 
	refine {{ {this} ↑ dealer.ret_ ->set ( [ ec::deals_limit , 
                                        	!{buy} ↑ OrderInfoXchg.original_amount - 
                                        	!{buy} ↑ OrderInfoXchg.amount , 
                                        	!{buy} ↑ OrderInfoXchg.amount ] ) }} .
	refine {{  break_ }} . 
	refine {{ if ~ !{ sell_out_of_tons } && 
				 ~ !{ buy_out_of_tons } then { { _:UEt } }  ; { _ } }} . 
	refine {{ [ {sell_out_of_tons} , {buy_out_of_tons} , {deal_amount} ] := make_deal_ ( {sell} , {buy} ) }} . 
	refine {{ if  !{sell_out_of_tons} then { { _:UEf } } ; { _ } }} . 
	refine {{ {this} ↑ dealer.sells_ -> pop () ; { _ } }} . 
	refine {{ new 'ret : OrderRetLRecord @ "ret" := [ ec::out_of_tons , 
	                     !{sell} ↑ OrderInfoXchg.original_amount - !{sell} ↑ OrderInfoXchg.amount , 0 ] ; { _ } }} . 
	refine {{ if #{sell_idx} == !{sell_idx_cur} then { { _:UEf } } ; { _ } }} . 
	refine {{ {this} ↑ dealer.ret_  ->set ( !{ ret } ) }} . 
	refine {{ if !{sell} ↑ OrderInfoXchg.account > !{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.return_ownership then { { _:UEf } } ; { _ } }} . 
	refine {{ {sell} ↑ OrderInfoXchg.account -= !{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.return_ownership  ; { _ } }} . (*
         	 	 refine {{ ITONTokenWalletPtr ( sell . tip3_wallet_provide )
				    ( Grams ( tons_cfg_ . return_ownership . get ( ) ) ) . returnOwnership ( sell . amount ) ; { _ } }} . 
         	 	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) 
				   . onOrderFinished ( ret , bool_t { true } )  }} . *)
			refine ( let sell_ptr := {{ ITONTokenWalletPtr [[ (!{sell} ↑ OrderInfoXchg.tip3_wallet_provide)  ]] }} in 
			{{ {sell_ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.return_ownership) ⇒ { Messsage_ι_value }  $] 
										⤳ .returnOwnership ( (!{sell} ↑ OrderInfoXchg.amount) ) ; {_} }} ).  
	
	
				refine ( let sell_ptr := {{ IPriceCallBackPtr [[ (!{sell} ↑ OrderInfoXchg.client_addr)  ]] }} in 
				{{ {sell_ptr} with [$ (!{sell} ↑ OrderInfoXchg.account) ⇒ { Messsage_ι_value }  $] 
											⤳ PriceXchg.onOrderFinished ( !{ret} , TRUE ) }} ).
	refine {{ {sell_opt} -> reset () }} . 
	refine {{ if  !{ buy_out_of_tons } then { { _:UEf } } ; { _ } }} . 
	refine {{ _buys_ -> pop () ; { _ } }} . 
	refine {{ new 'ret : OrderRetLRecord @ "ret" := 	 
     	 	 	 [ ec::out_of_tons , !{buy} ↑ OrderInfoXchg.original_amount - 
                                     !{buy} ↑ OrderInfoXchg.amount, 0 ] ; { _ } }} . 
	refine {{ if #{ buy_idx } == !{buy_idx_cur} then { { _:UEf } } ; { _ } }} . 
	refine {{ {this} ↑ dealer.ret_ ->set ( !{ ret } )}} . 
    refine {{ if !{sell} ↑ OrderInfoXchg.account > !{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.return_ownership then { { _:UEf } } ; { _ } }} . 
(*      	 	 refine {{ { ITONTokenWalletPtr ( buy . tip3_wallet_provide ) 
( Grams ( tons_cfg_ . return_ownership . get ( ) ) ) . returnOwnership ( buy . amount ) ; { _ } }} .  *)
refine ( let buy_ptr := {{ ITONTokenWalletPtr [[ (!{buy} ↑ OrderInfoXchg.tip3_wallet_provide)  ]] }} in 
			{{ {buy_ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.return_ownership) ⇒ { Messsage_ι_value }  $] 
										⤳ .returnOwnership ( (!{buy} ↑ OrderInfoXchg.amount) ) ; {_} }} ).  
     	 	 refine {{ { ret } := !{ ret } (* IPriceCallbackPtr ( buy . client_addr ) 
			   ( Grams ( buy . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { false } ) *) }} . 
			   refine ( let buy_ptr := {{ IPriceCallBackPtr [[ (!{buy} ↑ OrderInfoXchg.client_addr)  ]] }} in 
			   {{ {buy_ptr} with [$ (!{buy} ↑ OrderInfoXchg.account) ⇒ { Messsage_ι_value }  $] 
										  ⤳ PriceXchg.onOrderFinished ( !{ret} , FALSE ) ; {_} }} ).
	refine {{ {buy_opt} -> reset () }} . 
    refine {{ if ( !{ sell_out_of_tons } \\ !{ buy_out_of_tons } ) then { { _:UEt } } ; { _ } }} . 
	refine {{ continue_  }} . 
	       refine {{ second ( * {sell_opt} ) := !{sell} ; { _ } }} . 
					refine {{ second ( * {buy_opt} ) := !{buy} ; { _ } }} . 
	refine {{ {this} ↑ dealer.sells_amount_ -= !{ deal_amount } ; { _ } }} . 
    refine {{ {this} ↑ dealer.buys_amount_ -= !{ deal_amount } ; { _ } }} .
	refine {{ if  ~ !{sell} ↑ OrderInfoXchg.amount then { { _:UEf } } ; { _ } }} . 
	refine {{ {this} ↑ dealer.sells_ -> pop () ; { _ } }} . 
	refine {{ new 'ret : OrderRetLRecord @ "ret" :=[ ok_ , 
                    !{sell} ↑ OrderInfoXchg.original_amount , 0 ] ; { _ } }} . 
	refine {{ if #{ sell_idx } == !{ sell_idx_cur } then { { _:UEf } } ; { _ } }} . 
	refine {{ {this} ↑ dealer.ret_ ->set (!{ ret } ) }} . 
(*  	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) 
. onOrderFinished ( ret , bool_t { true } ) ; { _ } }} .  *)
refine ( let sell_ptr := {{ IPriceCallBackPtr [[ (!{sell} ↑ OrderInfoXchg.client_addr)  ]] }} in 
		   {{ {sell_ptr} with [$ (!{sell} ↑ OrderInfoXchg.account) ⇒ { Messsage_ι_value }  $] 
									  ⤳ PriceXchg.onOrderFinished ( !{ret} , TRUE ) ; {_} }} ).
    refine {{ {sell_opt} -> reset () }} . 
	refine {{ if  ~ !{buy} ↑ OrderInfoXchg.amount then { { _:UEf } } }} . 
    refine {{ {this} ↑ dealer.buys_ -> pop () ; { _ } }} .
	refine {{ new 'ret : OrderRetLRecord  @ "ret" := 	 
 	 	 	           [ ok_ , !{buy} ↑ OrderInfoXchg.original_amount , 0 ] ; { _ } }} . 
	refine {{ if #{ buy_idx } == !{ buy_idx_cur } then { { _:UEf } } ; { _ } }} . 
	refine {{ {this} ↑ dealer.ret_ -> set ( !{ ret } ) }} . 
(*  	       refine {{ IPriceCallbackPtr ( buy . client_addr ) ( Grams ( buy . account . get ( ) ) ) 
. onOrderFinished ( ret , bool_t { false } ) ; { _ } }} .  *)
refine ( let buy_ptr := {{ IPriceCallBackPtr [[ (!{buy} ↑ OrderInfoXchg.client_addr)  ]] }} in 
{{ {buy_ptr} with [$ (!{buy} ↑ OrderInfoXchg.account) ⇒ { Messsage_ι_value }  $] 
						   ⤳ PriceXchg.onOrderFinished ( !{ret} , FALSE ) ; {_} }} ).
	refine {{ {buy_opt} -> reset () }} . 

	refine {{ if ? !{sell_opt} && 
                 ? second ( !{sell_opt} -> get () ) ↑ OrderInfoXchg.amount
                       then { { _:UEt } } ; { _ } }} .
	refine {{ new 'sell : OrderInfoXchgLRecord @ "sell" := second ( !{sell_opt} -> get () ) ; { _ } }} . 
    refine {{ {this} ↑ dealer.sells_ -> change_front ( !{sell} ) ; {_} }} .  
	refine {{ if #{sell_idx} == first ( !{sell_opt} -> get ()) then { { _:UEf } } }} .
	refine {{ {this} ↑ dealer.ret_ -> set ( [ ok_ , 
                     						  !{sell} ↑ OrderInfoXchg.original_amount - 
											  !{sell} ↑ OrderInfoXchg.amount , 
											  !{sell} ↑ OrderInfoXchg.amount ] ) }} . 
    refine {{ if ? !{buy_opt} && 
                 ? second ( !{buy_opt} -> get () ) ↑ OrderInfoXchg.amount then { { _:UEt } } }} .
    refine {{ new 'buy : OrderInfoXchgLRecord @ "sell" := second ( !{buy_opt} -> get () ) ; { _ } }} . 
  	refine {{ {this} ↑ dealer.buys_ -> change_front ( !{buy} ) ; { _ } }} .
 	refine {{ if #{buy_idx} == first ( !{buy_opt} -> get () ) then { { _:UEf } } }} . 
 	refine {{ {this} ↑ dealer.ret_ -> set ( [ 1 , !{buy} ↑ OrderInfoXchg.original_amount - 
	                                        !{buy} ↑ OrderInfoXchg.amount , 
											!{buy} ↑ OrderInfoXchg.amount ] ) ; { _ } }} .
	refine {{ return_ {} }}.
Defined . 

End Dealer.

(***************************************************************************)						   

Definition process_queue_left { R a1 a2 } (dealer: ULValue dealerLRecord) 
										  ( sell_idx : URValue uint a1 ) 
										  ( buy_idx : URValue uint a2 ) : UExpression R true := 
	wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3LRR ) process_queue dealer sell_idx buy_idx ) . 
 
Notation " d -> 'process_queue_' '(' sell_idx ',' buy_idx ')' " := ( process_queue_left d sell_idx buy_idx ) 
 (in custom ULValue at level 0 , d custom ULValue, sell_idx custom URValue at level 0 , buy_idx custom URValue at level 0 ) : ursus_scope . 
 
(* Definition int_sender_and_value : UExpression ( address # Grams ) false . 
	refine {{ new 'sender : ( address ) @ "sender" :=  int_sender () ; { _ } }} . 
	refine {{ return_ [ !{ sender } , int_value () ] }} . 
Defined .  *)

(* Definition int_sender_and_value_right : URValue ( address #  Grams ) false := 
	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) int_sender_and_value ) . 
 
Notation " 'int_sender_and_value_' '(' ')' " :=  ( int_sender_and_value_right ) 
 												 (in custom URValue at level 0 ) : ursus_scope . 
 *)
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

Parameter set_int_sender_ : UExpression OrderRetLRecord false .

Notation " 'set_int_sender__' '(' ')' " := ( set_int_sender_ ) 
 										  ( in custom ULValue at level 0 ) : ursus_scope . 

(* void set_int_return_value(unsigned val) { int_return_value_ = val; }  *)
Parameter set_int_return_value_ : UExpression PhantomType false .
Notation " 'set_int_return_value__' '(' ')' " := ( set_int_sender_ ) 
 												( in custom ULValue at level 0 ) : ursus_scope .

Definition onTip3LendOwnershipMinValue : UExpression uint128 false . 
	refine {{ return_  ( _tons_cfg_ ↑ TonsConfig.process_queue )+ 
					( _tons_cfg_ ↑ TonsConfig.transfer_tip3 )+ 
					( _tons_cfg_ ↑ TonsConfig.send_notify )+ 
					( _tons_cfg_ ↑ TonsConfig.return_ownership) + 
					( _tons_cfg_ ↑ TonsConfig.order_answer) }} . 
Defined . 
 
Definition onTip3LendOwnershipMinValue_right  : URValue uint128 false := 
 	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) onTip3LendOwnershipMinValue ) . 
 
 Notation " 'onTip3LendOwnershipMinValue_' '(' ')' " := 
 ( onTip3LendOwnershipMinValue_right ) (in custom URValue at level 0 ) : ursus_scope .
  
Definition prepare_internal_wallet_state_init_and_addr 
											( name:  String ) 
											( symbol : String )
											( decimals : uint8 )
											( root_public_key : uint256 )
											( wallet_public_key : uint256 ) 
											( root_address : address) 
											( owner_address : optional address ) 
											( code : cell ) 
											( workchain_id : int ) : UExpression ( StateInitLRecord # uint256 ) false .
	refine {{ new 'wallet_data : DTONTokenWalletInternalLRecord @ "wallet_data" := 
			[ #{name} , #{symbol} , #{decimals} , 0 , #{root_public_key} , 
			#{wallet_public_key} , #{root_address} , #{owner_address} , 
			{} , #{code} , #{workchain_id} ] ; { _ } }} . 
	refine {{ new 'wallet_data_cl : cell @ "wallet_data_cl" := 
		prepare_persistent_data_ ( {} , !{wallet_data} ) ; { _ } }} . 
	refine {{ new 'wallet_init : StateInitLRecord @ "wallet_init" := 
		[ {} , {} , (#{code}) -> set () , (!{wallet_data_cl}) -> set () , {} ] ; { _ } }} . 
	refine {{ new 'wallet_init_cl : cell @ "wallet_init_cl" := {}  
			(*  build ( !{ wallet_init } ) . make_cell ( ) *) ; { _ } }} . 
	refine {{ return_ [ !{ wallet_init } , tvm_hash ( !{wallet_init_cl} ) ] }} . 
Defined .

Definition prepare_internal_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  
 							( name : URValue String a1 ) 
							( symbol : URValue String a2) 
							( decimals : URValue uint8 a3 ) 
							( root_public_key : URValue uint256 a4 ) 
							( wallet_public_key : URValue uint256 a5 ) 
							( root_address : URValue address a6 ) 
							( owner_address : URValue ( optional address ) a7 ) 
							( code : URValue cell a8 ) 
							( workchain_id : URValue int a9 ) : URValue ( StateInitLRecord * uint256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 							
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_internal_wallet_state_init_and_addr 
 						name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_internal_wallet_state_init_and_addr_' '(' name ',' symbol ',' decimals ',' root_public_key ',' wallet_public_key ',' root_address ',' owner_address ',' code ',' workchain_id ')' " := 
 ( prepare_internal_wallet_state_init_and_addr_right name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 , symbol custom URValue at level 0 , 
 	 decimals custom URValue at level 0 , root_public_key custom URValue at level 0 , wallet_public_key custom URValue at level 0 , 
	 root_address custom URValue at level 0 , owner_address custom URValue at level 0 , code custom URValue at level 0 , 
	 workchain_id custom URValue at level 0 ) : ursus_scope . 

Definition expected_wallet_address ( cfg : Tip3ConfigLRecord ) 
								   ( wallet_pubkey : uint256 ) 
								   ( internal_owner : uint256 ) : UExpression uint256 false . 
	refine {{ new 'owner_addr : optional address @ "owner_addr" := {} ; { _ } }} . 
	refine {{ if ( ? (#{internal_owner}) ) then { { _:UEf } } ; { _ } }} . 
		refine {{ {owner_addr} := {} (* Address :: make_std ( workchain_id_ , !{ internal_owner } ) *) }} . 
	refine {{ return_ 
	                  second ( prepare_internal_wallet_state_init_and_addr_ 
					                  ( (#{cfg}) ↑ Tip3Config.name , 
					                    (#{cfg}) ↑ Tip3Config.symbol , 
					                    (#{cfg}) ↑ Tip3Config.decimals , 
					                    (#{cfg}) ↑ Tip3Config.root_public_key , 
					                    #{ wallet_pubkey } , 
					                    (#{cfg}) ↑ Tip3Config.root_address , 
					                    !{ owner_addr } , 
					                    _tip3_code_ , 
					                    _workchain_id_ ) ) }} . 
Defined . 

Definition expected_wallet_address_right { a1 a2 a3 } ( cfg : URValue Tip3ConfigLRecord a1 ) 
													  ( wallet_pubkey : URValue uint256 a2 ) 
													  ( internal_owner : URValue uint256 a3 ) : URValue uint256 ( orb ( orb a3 a2 ) a1 ) := 
	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) expected_wallet_address cfg wallet_pubkey internal_owner ) . 
 
Notation " 'expected_wallet_address_' '(' cfg ',' wallet_pubkey ',' internal_owner ')' " := 
 ( expected_wallet_address_right  cfg wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 , wallet_pubkey custom URValue at level 0 , internal_owner custom URValue at level 0 ) : ursus_scope .

Definition verify_tip3_addr ( cfg : Tip3ConfigLRecord ) 
							( tip3_wallet : address ) 
							( wallet_pubkey : uint256 ) 
							( internal_owner : uint256 ) : UExpression boolean false . 
 refine {{ new 'expected_address : ( uint256 ) @ "expected_address" := 
             expected_wallet_address_ ( #{ cfg } , #{ wallet_pubkey } , #{ internal_owner } ) ; { _ } }} . 
 refine {{ return_ ( (#{tip3_wallet}) ↑ address.address ) == !{ expected_address } }} .
Defined . 

Definition verify_tip3_addr_right { a1 a2 a3 a4 } ( cfg : URValue Tip3ConfigLRecord a1 ) 
 												  ( tip3_wallet : URValue address a2 ) 
												  ( wallet_pubkey : URValue uint256 a3 ) 
												  ( internal_owner : URValue uint256 a4 ) : URValue boolean ( orb ( orb ( orb a4 a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) verify_tip3_addr  cfg tip3_wallet wallet_pubkey internal_owner ) . 
 
Notation " 'verify_tip3_addr_' '(' cfg ',' tip3_wallet ',' wallet_pubkey ',' internal_owner ')' " := 
 ( verify_tip3_addr_right cfg tip3_wallet wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 , tip3_wallet custom URValue at level 0 , 
 	wallet_pubkey custom URValue at level 0 , internal_owner custom URValue at level 0 ) : ursus_scope . 

Parameter set_int_return_flag_ :UExpression OrderRetLRecord false .
Notation " 'set_int_return_flag__' '(' ')' " := 
 ( set_int_return_flag_ ) 
 (in custom ULValue at level 0 ) : ursus_scope .

Parameter int_value__ : URValue uint false .

Notation " 'int_value' '(' ')' " := 
 ( int_value__ ) 
 (in custom URValue at level 0 ) : ursus_scope .

Definition on_ord_fail (ec: uint) (wallet_in : address (* ITONTokenWalletPtrLRecord *)) (amount: uint128) : UExpression OrderRetLRecord false . 
(*  	 	 refine {{ wallet_in(Grams(tons_cfg_.return_ownership.get())).returnOwnership(amount) ; { _ } }} .  *)
refine ( let wallet_in_ptr := {{ ITONTokenWalletPtr [[ #{wallet_in}  ]] }} in 
	  {{ {wallet_in_ptr} with [$ (_tons_cfg_ ↑ TonsConfig.return_ownership) ⇒ { Messsage_ι_value }  $] 
								  ⤳ .returnOwnership ( #{amount} ) ; {_} }} ).  
	refine {{ if ( ( _sells_ -> empty () ) && ( _buys_ -> empty () ) ) then { { _:UEf } } else { { _:UEf } } ; { _ } }} . 
		refine {{ set_int_return_flag ( #{SEND_ALL_GAS} \\ #{DELETE_ME_IF_I_AM_EMPTY} ) }} .
	refine {{ new 'incoming_value : uint @ "incoming_value" := int_value ( ) ; { _ } }} . 
	refine {{ tvm_rawreserve (tvm_balance () - !{incoming_value} , rawreserve_flag::up_to ) ; { _ } }} . 
	refine {{ set_int_return_flag ( #{SEND_ALL_GAS} ) }} . 
	refine {{ return_ [ ec_ , {} , {} ] }} .
Defined . 

Definition on_ord_fail_right { a1 a2 a3 }  ( ec : URValue uint a1 ) 
                                           ( wallet_in : URValue address (* ITONTokenWalletPtrLRecord *) a2 ) 
										   ( amount : URValue uint128 a3 ) : URValue OrderRetLRecord ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) on_ord_fail ec wallet_in amount ) . 
 
Notation " 'on_ord_fail_' '(' ec ',' wallet_in ',' amount ')' " := 
 ( on_ord_fail_right ec wallet_in amount ) 
 (in custom URValue at level 0 , ec custom URValue at level 0 , wallet_in custom URValue at level 0 , amount custom URValue at level 0 ) : ursus_scope . 

Definition process_queue_impl ( tip3root_sell : address ) 
							  ( tip3root_buy : address ) 
							  ( notify_addr : address (* IFlexNotifyPtr *) ) 
							  ( price : price_t ) 
							  ( deals_limit : uint8 ) 
							  ( tons_cfg : TonsConfigLRecord ) 
							  ( sell_idx : uint ) 
							  ( buy_idx : uint ) 
							  ( sells_amount : uint128 ) 
							  ( sells : queue OrderInfoXchgLRecord ) 
							  ( buys_amount : uint128 ) 
							  ( buys : queue OrderInfoXchgLRecord ) : UExpression process_retLRecord true . 
	refine {{ new 'd : ( dealerLRecord ) @ "d" := 	 	 
		[ #{tip3root_sell}, #{tip3root_buy}, #{notify_addr}, #{price}, #{deals_limit}, #{tons_cfg},
	#{sells_amount}, #{sells}, #{buys_amount}, #{buys}, {} ] ; { _ } }} . 
 	refine {{ {d} -> process_queue_ ( #{sell_idx} , #{buy_idx} ) ; { _ } }} .  
	refine {{ return_ [ (!{d}) ↑ dealer.sells_amount_ , 
						          (!{d}) ↑ dealer.sells_ , 
						          (!{d}) ↑ dealer.buys_amount_ , 
						          (!{d}) ↑ dealer.buys_ , 
						          (!{d}) ↑ dealer.ret_ ] }} .
Defined . 

Definition process_queue_impl_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 }  
									( tip3root_sell : URValue address a1 ) 
									( tip3root_buy : URValue address a2 ) 
									( notify_addr : URValue address (* IFlexNotifyPtrLRecord *) a3 ) 
									( price : URValue price_t a4 ) 
									( deals_limit : URValue uint8 a5 ) 
									( tons_cfg : URValue TonsConfigLRecord a6 ) 
									( sell_idx : URValue uint a7 ) 
									( buy_idx : URValue uint a8 ) 
									( sells_amount : URValue uint128 a9 ) 
									( sells : URValue ( queue OrderInfoXchgLRecord ) a10 ) 
									( buys_amount : URValue uint128 a11 ) 
									( buys : URValue ( queue OrderInfoXchgLRecord ) a12 ) 
									: URValue process_retLRecord true := 
	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ12 ) process_queue_impl tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) . 
 
Notation " 'process_queue_impl_' '(' tip3root_sell ',' tip3root_buy ',' notify_addr ',' price ',' deals_limit ',' tons_cfg ',' sell_idx ',' buy_idx ',' sells_amount ',' sells ',' buys_amount ',' buys ')' " := 
 ( process_queue_impl_right tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) 
 (in custom URValue at level 0 , tip3root_sell custom URValue at level 0 , tip3root_buy custom URValue at level 0 , 
  notify_addr custom URValue at level 0 , price custom URValue at level 0 , deals_limit custom URValue at level 0 , 
  tons_cfg custom URValue at level 0 , sell_idx custom URValue at level 0 , buy_idx custom URValue at level 0 , 
  sells_amount custom URValue at level 0 , sells custom URValue at level 0 , buys_amount custom URValue at level 0 , 
  buys custom URValue at level 0 ) : ursus_scope . 

Parameter int_sender_and_value_ : URValue (address # uint) false .
Notation " 'int_sender_and_value__' '(' ')' " := 
 ( int_sender_and_value_ ) 
 (in custom URValue at level 0 ) : ursus_scope .

Definition onTip3LendOwnership ( answer_addr : address ) 
							   ( balance : uint128 ) 
							   ( lend_finish_time : uint32 )
							   ( pubkey : uint256 )
							   ( internal_owner : address ) 
							   ( payload : cell ) : UExpression OrderRetLRecord true . 
 	 	 refine {{ new ( 'tip3_wallet : address , 'value : uint (* Grams *) ) @ 
                 ( "tip3_wallet" , "value" ) := int_sender_and_value__ ( ) ; { _ } }} . 
  	 refine {{ new 'wallet_in : address @ "wallet_in" (* ITONTokenWalletPtr *) := !{tip3_wallet} ; { _ } }} . 
 	 	 refine {{new 'ret_owner_gr : uint (* Grams *)@ "ret_owner_gr" :=
                  ( _tons_cfg_ ↑ TonsConfig.return_ownership ) ; { _ } }} . 
 	 	 refine {{ set_int_sender ( #{answer_addr} ) ; { _ } }} . 
 	 	 refine {{ set_int_return_value ( _tons_cfg_ ↑ TonsConfig.order_answer ) ; { _ } }} . 
 	 	 refine {{ new 'min_value : uint128 @ "min_value" := 
                    onTip3LendOwnershipMinValue_ ( ) ; { _ } }} . 
  	 	 refine {{ new 'args : PayloadArgsLRecord @ "args" := {} (* parse ( payload . ctos ( ) ) *) ; { _ } }} .

 	 	 refine {{ new 'is_sell : boolean @ "is_sell" := (!{args}) ↑ PayloadArgs.sell ; { _ } }} . 
 	 	 refine {{ new 'amount : uint128 @ "amount" := (!{args}) ↑ PayloadArgs.amount ; { _ } }} . 
 	 	 refine {{ new 'minor_amount : optional uint128 @ "minor_amount" := 
                             minor_cost_ ( !{ amount } , _price_ ) ; { _ } }} . 
 	 	 refine {{ new 'err : uint @ "err" := 0 ; { _ } }} . 
 	 	 refine {{ new 'internal_owner_std : uint @ "internal_owner_std" := 
                         (#{internal_owner}) ↑ address.address ; { _ } }} . 

 	 	 refine {{ if ( (!{value}) < !{min_value} ) then { { _:UEf } } else { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ {err} := ec::not_enough_tons_to_process }} . 
 	 	   refine {{ if ( (!{is_sell}) 
                       ? (~( verify_tip3_addr_ ( _major_tip3cfg_ , !{ tip3_wallet } , #{ pubkey } , !{ internal_owner_std } ) ) ) 
                       : (~( verify_tip3_addr_ ( _minor_tip3cfg_ , !{ tip3_wallet } , #{ pubkey } , !{ internal_owner_std } ) ) ) )
                  then { { _:UEf } } else { { _:UEf } } }} . 
         	 	 	 refine {{ { err } :=  ec::unverified_tip3_wallet }} . 
         	 	   refine {{ if ( ~ (?(!{ minor_amount })) ) 
                         then { { _:UEf } } else { { _:UEf } } }} . 
         	 	 	 refine {{ {err} :=  ec::too_big_tokens_amount  }} . 
         	 	   refine {{ if ( !{amount} < _min_amount_ ) then { { _:UEf } } else { { _:UEf } } }} . 
         	 	 	 refine {{ { err } := ec::not_enough_tokens_amount }} .
         	 	 refine {{ if ( (#{balance}) <                  
                   ( !{ is_sell } ? !{ amount } : ((!{minor_amount}) -> get_default () ) ) ) 
                          then { { _:UEf } } else { { _:UEf } } }} . 
         	 	 	 refine {{ { err } := ec::too_big_tokens_amount  }} . 
         	 	   refine {{ if ( ~ (is_active_time_ ( #{ lend_finish_time } )) ) then { { _:UEf } } }} . 
         	 	 	 refine {{ { err } :=  ec::expired  }} . 

 	 	 refine {{ if ( !{ err } ) then { { _:UEt } } ; { _ } }} . 
 	 	 	 refine {{ exit_ on_ord_fail_ ( !{err} , !{wallet_in} , !{amount} ) }} . 
 	 	 refine {{ new 'account : uint128 @ "account" := 
                (!{value}) - (_tons_cfg_ ↑ TonsConfig.process_queue) - 
                             (_tons_cfg_ ↑ TonsConfig.order_answer) ; { _ } }} . 
 	 	 refine {{ new 'ord : ( OrderInfoXchgLRecord ) @ "ord" := 	 	 
 	 	 	 [ !{amount} , !{amount} , !{account} , !{tip3_wallet} , 
        (!{args}) ↑  PayloadArgs.receive_tip3_wallet , (!{args}) ↑ PayloadArgs.client_addr  , #{lend_finish_time} ] ; { _ } }} .
    
 	 	 refine {{ new 'sell_idx : uint @ "sell_idx" := 0 ; { _ } }} . 
 	 	 refine {{ new 'buy_idx : uint @ "buy_idx" := 0 ; { _ } }} . 
 	 	 refine {{ new 'notify_amount : uint128 @ "notify_amount" := {}  ; { _ } }} . 
 	 	 refine {{ if ( !{ is_sell } ) then { { _:UEt } } else { { _:UEt } } ; { _ } }} . 
 	 	 	 refine {{ _sells_ -> push ( !{ord} ) ; { _ } }} . 
 	 	 	 refine {{ _sells_amount_ += ((!{ord}) ↑ OrderInfoXchg.amount) ; { _ } }} . 
 	 	 	 refine {{ { sell_idx } :=  first ( _sells_ ->back_with_idx() ); { _ } }} . 
 	 	 	 refine {{ {notify_amount} := _sells_amount_ }} . 

     	 refine {{ _buys_ -> push ( !{ord} ) ; { _ } }} . 
     	 refine {{ _buys_amount_ += !{ord} ↑ OrderInfoXchg.amount ; { _ } }} . 
     	 refine {{ { buy_idx } := first ( _buys_ -> back_with_idx () ) ; { _ } }} . 
     	 refine {{ {notify_amount} := _buys_amount_ }} . 
(*  refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) 
. onXchgOrderAdded ( is_sell , major_tip3cfg_ . root_address , minor_tip3cfg_ . root_address ,
 price_ . num , price_ . denum , ord . amount , notify_amount ) ; { _ } }} .  *)
 refine ( let notify_addr__ptr := {{ IFlexNotifyPtr [[ _notify_addr_  ]] }} in 
	  {{ {notify_addr__ptr} with [$ (_tons_cfg_ ↑ TonsConfig.send_notify) ⇒ { Messsage_ι_value }  $] 
								  ⤳ .onXchgOrderAdded (!{is_sell} ,  _major_tip3cfg_ ↑ Tip3Config.root_address ,
								  _minor_tip3cfg_ ↑ Tip3Config.root_address ,
								  _price_ ↑ RationalPrice.num , 
								  _price_ ↑ RationalPrice.denum ,
								  !{ord} ↑ OrderInfoXchg.amount , 
								  !{notify_amount}) ; {_} }} ). 

 	 	 refine {{ new ( 'sells_amount : uint128 , 'sells : queue OrderInfoXchgLRecord , 
                         'buys_amount : uint128 , 'buys: queue OrderInfoXchgLRecord , 
                         'ret: optional OrderRetLRecord )
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
 refine {{ if ( !{ret} ) then { { _:UEt } } ; { _ } }} . 
 	 refine {{ exit_ (!{ret}) -> get () }} . 
 refine {{ return_ [ ok_ , 0 , (!{ord}) ↑ OrderInfoXchg.amount ] }} . 
 Defined . 
 

Definition processQueue : UExpression PhantomType true . 
 	 	 refine {{ if ( (_sells_ -> empty ()) \\ (_buys_ -> empty ()) ) 
               then { { _:UEt } }; { _ } }} . 
 	 	 	 refine {{ exit_ {} }} . 

 	 	 refine {{ new ( 'sells_amount : uint128 , 
                         'sells: queue OrderInfoXchgLRecord , 
                         'buys_amount : uint128 , 
                         'buys : queue OrderInfoXchgLRecord , 
                         'ret : optional OrderRetLRecord )
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
 	 refine {{ (* suicide ( _flex_ ) *) _buys_ := !{buys} ; {_} }} .
refine {{ return_ {} }} . 
Defined . 
 
Definition cancel_order_impl ( orders : queue OrderInfoXchgLRecord ) 
							 ( client_addr : addr_std_fixed ) 
							 ( all_amount : uint128 ) 
							 ( sell : boolean ) 
							 ( return_ownership : uint (* Grams *) ) 
               ( process_queue : uint (* Grams *) ) 
               ( incoming_val : uint (* Grams *) )  : UExpression ((queue OrderInfoXchgLRecord) # uint128) false . 
 	 	 refine {{ new 'is_first : ( boolean ) @ "is_first" := TRUE ; { _ } }} . 
	refine {{ new 'it : OrderInfoXchgLRecord @ "it" := second ( (#{orders}) -> begin () -> get_default () )  ; { _ } }} . 

  refine {{ while ~ (!{it} != second ( (#{orders}) -> end () -> get_default () )) 
             do { { _:UEf } } ; { _ } }} . 
 	 	 	 refine {{ new 'next_it : OrderInfoXchgLRecord @ "next_it" := 
         second ( (#{orders}) -> next ( first ( (#{orders}) -> end () -> get_default () ) ) -> get_default () ) ; { _ } }} . 
 	 	 	 refine {{ new 'ord : ( OrderInfoXchgLRecord ) @ "ord" := !{it} ; { _ } }} . 
 	 	 	 refine {{ if ( (!{ord} ↑ OrderInfoXchg.client_addr) == #{client_addr} ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ new 'minus_val : XUInteger @ "minus_val" := 
                       !{is_first} ? #{process_queue} : 0 ; { _ } }} . 
 	 	 	 	 refine {{ if ( #{sell} ) then { { _:UEf } } ; { _ } }} . 
(*  	 	 	 refine {{ { ITONTokenWalletPtr ( ord . tip3_wallet ) ( return_ownership ) . returnOwnership ( ord . amount ) ; { _ } }} .  *)
						refine ( let tip3_wallet_ptr := {{ ITONTokenWalletPtr [[ !{ord} ↑ OrderInfoXchg.tip3_wallet_provide ]] }} in 
						{{ {tip3_wallet_ptr} with [$ #{return_ownership} ⇒ { Messsage_ι_value }  $] 
													⤳ .returnOwnership ( !{ord} ↑ OrderInfoXchg.amount ) ; {_} }} ). 
 	 	 	 	 	 refine {{ {minus_val} += (#{return_ownership}) }} . 
 	 	 	 refine {{ new 'plus_val : ( XUInteger ) @ "plus_val" := 
                      (((!{ord}) ↑ OrderInfoXchg.account) + ( !{is_first} ? (#{incoming_val}) : 0 )) ; { _ } }} . 
 	 	 	 refine {{ {is_first} := FALSE ; { _ } }} . 
 	 	 	 refine {{ if ( !{plus_val} > !{minus_val} ) then { { _:UEf } } ; { _ } }} . 
 	 	 	 	 refine {{ new 'ret_val : XUInteger @ "ret_val" := (!{plus_val} - !{minus_val}) ; { _ } }} . 
 	 	 	 	 refine {{ new 'ret : ( OrderRetLRecord ) @ "ret" := 	 	 	 	 
 	 	 	                          [ ec::canceled , !{ord} ↑ OrderInfoXchg.original_amount 
                                                - !{ord} ↑ OrderInfoXchg.amount , 0 ] ; { _ } }} . 
					refine ( let ord_ptr := {{ IPriceCallBackPtr [[ (!{ord} ↑ OrderInfoXchg.client_addr)  ]] }} in 
              				{{ {ord_ptr} with [$ !{ret_val} ⇒ { Messsage_ι_value }  $] 
                                         ⤳ PriceXchg.onOrderFinished ( !{ret} , #{sell} ) }} ).
     refine {{ new 'all_amount_ : uint128 @ "all_amount_" := #{all_amount} ; {_} }} .
 	 	 refine {{ {all_amount_} -= !{ord} ↑ OrderInfoXchg.amount ; { _ } }} .
     refine {{ new 'orders_ : queue OrderInfoXchgLRecord @ "orders_" := #{orders} ; {_} }} .
 	 	 refine {{ {orders_} -> erase ( first ( (!{orders_}) -> end () -> get_default () ) ) }} . 
   refine {{ {it} := !{next_it} }} .     (* end of while *)

 refine {{ return_ [ #{ orders } , #{ all_amount } ] }} . 
Defined . 
 
Definition cancel_order_impl_right { a1 a2 a3 a4 a5 a6 a7 }  
 			( orders : URValue ( queue OrderInfoXchgLRecord ) a1 ) 
			( client_addr : URValue addr_std_fixed a2 ) 
			( all_amount : URValue uint128 a3 ) 
			( sell : URValue boolean a4 ) 
			( return_ownership : URValue Grams a5 )
            ( process_queue : URValue Grams a6 ) 
			( incoming_val : URValue Grams a7 ) : URValue ((queue OrderInfoXchgLRecord) # uint128) ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancel_order_impl orders client_addr all_amount sell return_ownership process_queue incoming_val ) . 
 
Notation " 'cancel_order_impl_' '(' orders ',' client_addr ',' all_amount ',' sell ',' return_ownership ',' process_queue ',' incoming_val ')' " := 
 ( cancel_order_impl_right orders client_addr all_amount sell return_ownership process_queue incoming_val ) 
 (in custom URValue at level 0 , orders custom URValue at level 0 , client_addr custom URValue at level 0 , 
 all_amount custom URValue at level 0 , sell custom URValue at level 0 , return_ownership custom URValue at level 0 , 
 process_queue custom URValue at level 0 , incoming_val custom URValue at level 0 ) : ursus_scope .

Definition cancelSell : UExpression PhantomType false . 
	refine {{ new 'canceled_amount : ( uint128 ) @ "canceled_amount" := _sells_amount_ ; { _ } }} . 
	refine {{ new 'client_addr : ( addr_std_fixed ) @ "client_addr" := int_sender () ; { _ } }} . 
	refine {{ new 'value : ( uint ) @ "value" := 
						int_value ( ) ; { _ } }} . 
	refine {{ new ( 'sells:(XQueue OrderInfoXchgLRecord) , 'sells_amount:uint128 )
				@ ( "sells" , "sells_amount" ) := cancel_order_impl_ ( _sells_ , !{client_addr} , _sells_amount_ , 
																		TRUE , 
																		_tons_cfg_ ↑ TonsConfig.return_ownership , 
																		_tons_cfg_ ↑ TonsConfig.process_queue , 
																		!{value} ) ; { _ } }} . 
	refine {{ _sells_ := !{ sells } ; { _ } }} . 
	refine {{ _sells_amount_ := !{sells_amount} ; { _ } }} . 
	refine {{ { canceled_amount } -= _sells_amount_ ; { _ } }} . 
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) 
. onXchgOrderCanceled ( bool_t { true } , major_tip3cfg_ . root_address , minor_tip3cfg_ . root_address , 
price_ . num , price_ . denum , canceled_amount , sells_amount_ ) ; { _ } }} .  *)
refine ( let notify_addr__ptr := {{ IFlexNotifyPtr [[ _notify_addr_  ]] }} in 
	  {{ {notify_addr__ptr} with [$ (_tons_cfg_ ↑ TonsConfig.send_notify) ⇒ { Messsage_ι_value }  $] 
								  ⤳ .onXchgOrderCanceled ( TRUE , _major_tip3cfg_ ↑ Tip3Config.root_address ,
								  _minor_tip3cfg_ ↑ Tip3Config.root_address ,
								  _price_ ↑ RationalPrice.num , 
								  _price_ ↑ RationalPrice.denum ,
									 !{canceled_amount} , 
								  _sells_amount_) ; {_} }} ). 
	refine {{ if ( (_sells_ -> empty ()) && (_buys_ -> empty ()) ) then { { _:UEf } } }} . 
	refine {{ return_ {} (* suicide ( flex_ ) *) }} . 
Defined . 
 
Definition cancelBuy : UExpression PhantomType false . 
	refine {{ new 'canceled_amount : uint128 @ "canceled_amount" := _buys_amount_ ; { _ } }} . 
	refine {{ new 'client_addr : addr_std_fixed @ "client_addr" := int_sender ()  ; { _ } }} . 
	refine {{ new 'value : uint @ "value" := int_value ( ) ; { _ } }} . 
	refine {{ new ( 'buys: queue OrderInfoXchgLRecord , 'buys_amount : uint128 ) @ ( "buys" , "buys_amount" ) :=
	cancel_order_impl_ ( _buys_ , !{client_addr} , _buys_amount_ , 
						FALSE , 
						_tons_cfg_ ↑ TonsConfig.return_ownership , 
						_tons_cfg_ ↑ TonsConfig.process_queue , 
						!{value} ) ; { _ } }} . 
	refine {{ _buys_ := !{ buys } ; { _ } }} . 
	refine {{ _buys_amount_ := !{buys_amount} ; { _ } }} . 
	refine {{ {canceled_amount} -= _buys_amount_ ; { _ } }} . 
(*  	 	 refine {{ notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) 
. onXchgOrderCanceled ( bool_t { false } , major_tip3cfg_ . root_address , minor_tip3cfg_ . root_address , 
price_ . num , price_ . denum , canceled_amount , buys_amount_ ) ; { _ } }} .  *)
refine ( let notify_addr__ptr := {{ IFlexNotifyPtr [[ _notify_addr_  ]] }} in 
	  {{ {notify_addr__ptr} with [$ (_tons_cfg_ ↑ TonsConfig.send_notify) ⇒ { Messsage_ι_value }  $] 
								  ⤳ .onXchgOrderCanceled ( FALSE , _major_tip3cfg_ ↑ Tip3Config.root_address ,
								  _minor_tip3cfg_ ↑ Tip3Config.root_address ,
								  _price_ ↑ RationalPrice.num , 
								  _price_ ↑ RationalPrice.denum ,
									 !{canceled_amount} , 
									 _buys_amount_) ; {_} }} ). 
	refine {{ if ( ( _sells_ -> empty () ) && (_buys_ -> empty () ) ) then { { _:UEf } } }} . 
		refine {{ return_ {} (* suicide ( flex_ ) *) }} . 
Defined . 
 
 Definition getPriceNum : UExpression uint128 false . 
 	refine {{ return_ _price_ ↑ RationalPrice.num }} . 
 Defined . 
 
Definition getPriceNum_right : URValue uint128 false := 
 	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPriceNum ) . 
 
 Notation " 'getPriceNum_' '(' ')' " := ( getPriceNum_right ) (in custom URValue at level 0 ) : ursus_scope . 

Definition getPriceDenum : UExpression uint128 false . 
 	refine {{ return_ _price_ ↑ RationalPrice.denum }} . 
Defined. 
 
Definition getPriceDenum_right: URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPriceDenum ) . 
 
Notation " 'getPriceDenum_' '(' ')' " := ( getPriceDenum_right ) (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getMinimumAmount : UExpression uint128 false . 
 	refine {{ return_ _min_amount_ }} . 
Defined . 
 
Definition getMinimumAmount_right  : URValue uint128 false := 
	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getMinimumAmount ) . 
 
Notation " 'getMinimumAmount_' '(' ')' " := ( getMinimumAmount_right ) (in custom URValue at level 0 ) : ursus_scope . 

Definition getTonsCfg : UExpression TonsConfigLRecord false . 
 	refine {{ return_ _tons_cfg_ }} . 
Defined . 
 
Definition getTonsCfg_right: URValue TonsConfigLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTonsCfg ) . 
 
Notation " 'getTonsCfg_' '(' ')' " := ( getTonsCfg_right ) (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getSells : UExpression ( mapping uint OrderInfoXchgLRecord ) false . 
 	refine {{ return_  {} (* dict_array ( sells_ . begin ( ) , sells_ . end ( ) ) *) }} . 
Defined . 
 
Definition getSells_right  : URValue ( mapping uint OrderInfoXchgLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSells ) . 
 
Notation " 'getSells_' '(' ')' " := ( getSells_right ) (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getBuys : UExpression ( mapping uint OrderInfoXchgLRecord ) false . 
 	refine {{ return_ {} (* dict_array ( buys_ . begin ( ) , buys_ . end ( ) ) *) }} . 
Defined . 
 
Definition getBuys_right: URValue ( mapping uint OrderInfoXchgLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuys ) . 
 
Notation " 'getBuys_' '(' ')' " := ( getBuys_right ) (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getSellAmount : UExpression uint128 false . 
 	refine {{ return_ _sells_amount_ }} . 
Defined . 
 
Definition getSellAmount_right  : URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSellAmount ) . 
 
Notation " 'getSellAmount_' '(' ')' " := ( getSellAmount_right ) (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getBuyAmount : UExpression uint128 false . 
	refine {{ return_ _buys_amount_ }} . 
Defined . 
 
Definition getBuyAmount_right: URValue uint128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuyAmount ) . 
 
Notation " 'getBuyAmount_' '(' ')' " := ( getBuyAmount_right ) (in custom URValue at level 0 ) : ursus_scope .
 
Definition _fallback ( _ : cell ) ( _ : slice ) : UExpression uint false . 
	refine {{ return_ 0 }} . 
Defined . 
 
Definition prepare_price_xchg_state_init_and_addr ( price_data : ContractLRecord )
												  ( price_code : cell )
												  : UExpression ( StateInitLRecord # uint256 ) false . 
	refine {{ new 'price_data_cl : cell @ "price_data_cl" := 
					prepare_persistent_data_ ( {} , #{price_data} ) ; { _ } }} . 
	refine {{ new 'price_init : StateInitLRecord @ "price_init" := 	
		[ {} , {} , (#{price_code}) -> set () , (!{price_data_cl}) -> set () , {} ] ; { _ } }} . 
	refine {{ new 'price_init_cl : cell @ "price_init_cl" := {} ; { _ } }} . 
	refine {{ {price_init_cl} := {} (* build ( !{ price_init } ) . make_cell ( ) *) ; { _ } }} . 
	refine {{ return_ [ !{price_init} , tvm_hash ( !{price_init_cl} ) ] }} . 
Defined . 

Definition getDetails : UExpression DetailsInfoXchgLRecord false . 
 	refine {{ return_ [ getPriceNum_ ( ) , getPriceDenum_ ( ) , getMinimumAmount_ ( ) , 
                        getSellAmount_ ( ) , getBuyAmount_ ( ) ] }} . 
Defined .

End FuncsInternal.
End Funcs.


