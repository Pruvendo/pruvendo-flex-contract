

Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import List.
Import ListNotations.

Local Open Scope program_scope. 

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.StateMonad21. 
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.ProofEnvironment2.

Require Import FLeXContractTypes.

Require Import PriceClass.

Require Import FLeXContractConsts.  
Require Import FLeXConstSig.
Require Import ZArith.

Require Import PriceFuncsNotations.
Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.

Require Import UrsusStdLib.stdNotations.
Require Import UrsusStdLib.stdUFunc.
Require Import UrsusStdLib.stdFuncNotations.
Require Import UrsusTVM.tvmNotations.

Module PriceFuncs (dc : FLeXConstsTypesSig XTypesModule StateMonadModule ).

Module Export PriceFuncNotationsModule := PriceFuncNotations XTypesModule StateMonadModule dc. 

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.


Existing Instance xbool_default.
Instance TvmCell_default : XDefault (TvmCell) := {
default := xStrNull}.
Existing Instance TvmCell_default.
Existing Instance phantom_default .


Check || Ф_is_active_time_ref_ ( {} ) || .



Definition Ф_calc_cost ( amount : XInteger128 ) ( price : XInteger128 ) : UExpression ( XMaybe XInteger128 ) false . 
 	 	 refine {{ amount : ( XInteger128 ) @ "amount" ; { _ } }} . 
 	 	 refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
 	 	 refine {{ new 'tons_cost : ( XInteger ) @ "tons_cost" := !{amount} * !{price} ; { _ } }} . 
 	 	 refine {{ if ( TRUE (* !{ tons_cost } >> 128 *) ) then { { _ :UExpression ( XMaybe XInteger128 ) false } } ; { _ } }} . 
 	 	 	 refine {{ return_ {} }} . 
 	 	 refine {{ return_ {} (* ->set !{tons_cost} *) }} . 
 Defined . 
 
 
 
 Definition dealer_Ф_make_deal ( sell : OrderInfo ) ( buy : OrderInfo ) : UExpression ( XBool # XBool # XInteger128 )%sol false . 
 	 	 refine {{ sell : ( OrderInfo ) @ "sell" ; { _ } }} . 
 	 	 refine {{ buy : ( OrderInfo ) @ "buy" ; { _ } }} . 
 	 	 refine {{ new 'deal_amount : ( auto ) @ "deal_amount" := {} ; { _ } }} . 
(*  	 	  std : : min ( sell ^^ OrderInfo:amount , buy ^^ OrderInfo:amount ) ; { _ } }} .  *)
 	 	 refine {{ new 'last_tip3_sell : ( XBool ) @ "last_tip3_sell" := {} ; { _ } }} . 
(*  	 	  NEW { sell . amount == deal_amount } ; { _ } }} .  *)
refine {{ {deal_amount}:= {} (* sell ^^ OrderInfo:amount -= !{deal_amount} *) ; { _ } }} . 
refine {{ {deal_amount}:= {}(* buy ^^ OrderInfo:amount -= !{deal_amount} *) ; { _ } }} . 
  	 refine {{ new 'cost : ( ( XMaybe XInteger128 ) ) @ "cost" := {} (* Ф_calc_cost_ref_ ( !{ deal_amount } dealer.price_ ) *)  ; { _ } }} .
 	 	 refine {{ new 'sell_costs : ( XInteger128 ) @ "sell_costs" := 0 ; { _ } }} . 
 	 	 refine {{ new 'buy_costs : ( XInteger128 ) @ "buy_costs" := {} (* ->get !{cost} *) ; { _ } }} . 
 	 	 refine {{ if ( !{ last_tip3_sell } ) then { { _: UExpression ( XBool # XBool # XInteger128 )%sol false } } 
                                          else { { _: UExpression ( XBool # XBool # XInteger128 )%sol false } } ; { _ } }} . 
 	 	 	 refine {{ { sell_costs } += {} (* ( dealer.tons_cfg_ ^^ transfer_tip3 + dealer.tons_cfg_ ^^ send_notify ) *) }} . 
 	 	   refine {{ { buy_costs } += {} (* ( dealer.tons_cfg_ ^^ transfer_tip3 + dealer.tons_cfg_ ^^ send_notify ) *) }} . 
 	 	 refine {{ new 'sell_out_of_tons : ( XBool ) @ "sell_out_of_tons" := {} (* ( sell ^^ OrderInfo:account < !{ sell_costs } ) *); { _ } }} . 
 	 	 refine {{ new 'buy_out_of_tons : ( XBool ) @ "buy_out_of_tons" := {} (* ( buy ^^ OrderInfo:account < !{ buy_costs } ) *) ; { _ } }} . 
 	 	 refine {{ if ( !{ sell_out_of_tons } \\ !{ buy_out_of_tons } ) then { { _: UExpression ( XBool # XBool # XInteger128 )%sol false } } ; { _ } }} . 
 	 	 	 refine {{ return_ {} (* [ !{ sell_out_of_tons } , !{ buy_out_of_tons } , 0 ] *) }} . 
refine {{ {deal_amount}:= {} (* sell ^^ OrderInfo:account - = sell_costs *) ; { _ } }} . 
refine {{{deal_amount}:= {} (*  buy ^^ OrderInfo:account - = buy_costs *) ; { _ } }} . 
(*  	 	 refine {{ ITONTokenWalletPtr ( sell . tip3_wallet ) ( Grams ( tons_cfg_ . transfer_tip3 . get ( ) ) ) . transfer ( sell . tip3_wallet , buy . tip3_wallet , deal_amount , uint128 ( 0 ) , last_tip3_sell ) ; { _ } }} . 
 	 	 refine {{ tvm_transfer ( sell . client_addr , cost - > get ( ) , true ) ; { _ } }} . 
 	 	 refine {{ dealer.notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onDealCompleted ( tip3root_ , price_ , deal_amount ) ; { _ } }} . 
 *) 	 	 
     refine {{ return_ {} (* [ false , false , !{ deal_amount } ] *) }} . 
 Defined . 
 
 
 
 Definition Ф_is_active_time ( order_finish_time : XInteger32 ) : UExpression XBool false . 
 	 	 refine {{ order_finish_time : ( XInteger32 ) @ "order_finish_time" ; { _ } }} . 
 	 	 refine {{ return_ tvm.now () (* + safe_delay_period *) < !{order_finish_time} }} . 
 Defined . 
 
Definition dealer_Ф_extract_active_order ( cur_order : ( XMaybe (XInteger # OrderInfo)%sol ) ) 
( orders : ( XList OrderInfo ) ) ( all_amount : XInteger128 ) ( sell : XBool ) 
: UExpression ( ( XMaybe (XInteger # OrderInfo)%sol ) # (XList OrderInfo) # XInteger128 )%sol false . 
 	 	 refine {{ cur_order : ( ( XMaybe (XInteger # OrderInfo)%sol ) ) @ "cur_order" ; { _ } }} . 
 	 	 refine {{ orders : ( ( XList OrderInfo ) ) @ "orders" ; { _ } }} . 
 	 	 refine {{ all_amount : ( XInteger128 ) @ "all_amount" ; { _ } }} . 
 	 	 refine {{ sell : ( XBool ) @ "sell" ; { _ } }} . 
 	 	 refine {{ if ( TRUE (* !{ cur_order } *) ) then { { _ : UExpression ( ( XMaybe (XInteger # OrderInfo)%sol ) # (XList OrderInfo) # XInteger128 )%sol false } } ; { _ } }} . 
 	 	 	 refine {{ return_ {} (* [ !{ cur_order } , !{ orders } , !{ all_amount } ] *) }} . 
 	 	 refine {{ while ( ~ (!{orders} ->empty) ) do { { _: UExpression ( ( XMaybe (XInteger # OrderInfo)%sol ) # (XList OrderInfo) # XInteger128 )%sol false } } ; { _ } }} . 
 	 	 	 refine {{ { cur_order } := {} (* orders . front_with_idx_opt ( ) *) ; { _ } }} . 
(*  	 	 	 refine {{ new 'ord : ( OrderInfo ) @ "ord" := !{ cur_order } ->second ; { _ } }} .  *)
 	 	 	 refine {{ if ( ~ Ф_is_active_time_ref_ ( {} (* ord ^^ OrderInfo:order_finish_time *) ) ) 
                 then { { _ : UExpression ( ( XMaybe (XInteger # OrderInfo)%sol ) # (XList OrderInfo) # XInteger128 )%sol false} } ; { _ } }} . 
 	 	 	 	 refine {{ { all_amount } -= {} (* ord ^^ OrderInfo:amount *) ; { _ } }} . 
 	 	 	 	 refine {{ new 'ret : ( OrderRet ) @ "ret" := {} ; { _ } }} . 
(*  	 	 	 	     := NEW { uint32 ( ec : : expired ) , ord . original_amount - ord . amount , uint128 { 0 } } ; { _ } }} .  *)
(*  	 	 	 	 refine {{ IPriceCallbackPtr ( ord . client_addr ) ( Grams ( ord . account . get ( ) ) ) . onOrderFinished ( ret , sell ) ; { _ } }} .  *)
(*  	 	 	 	 refine {{ orders ^^ ):pop ( ) ; { _ } }} .  *)
 	 	 	 	 refine {{ { cur_order } ->reset ; { _ } }} . 
(*  	 	 	 	 refine {{ continue }} .  *) refine {{ {orders}:= {} }} .
(*  	 	 refine {{ break }} .  *)        refine {{ {orders}:= {} }} .
 refine {{ return_ {} (* [ !{ cur_order } , !{ orders } , !{ all_amount } ] *) }} . 
Defined . 
 
 
 
 Definition Ф_process_queue_impl ( tip3root : XAddress )
 ( notify_addr : XAddress (* IFlexNotifyPtr *) ) ( price : XInteger128 ) 
( deals_limit : XInteger8 ) ( tons_cfg : TonsConfig ) ( sell_idx : XInteger )
 ( buy_idx : XInteger ) ( sells_amount : XInteger128 ) ( sells : ( XList OrderInfo ) ) 
( buys_amount : XInteger128 ) ( buys : ( XList OrderInfo ) ) : UExpression process_ret false . 

 	 	 refine {{ tip3root : ( XAddress ) @ "tip3root" ; { _ } }} . 
 	 	 refine {{ notify_addr : ( XAddress (* IFlexNotifyPtr *) ) @ "notify_addr" ; { _ } }} . 
 	 	 refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ tons_cfg : ( TonsConfig ) @ "tons_cfg" ; { _ } }} . 
 	 	 refine {{ sell_idx : ( XInteger ) @ "sell_idx" ; { _ } }} . 
 	 	 refine {{ buy_idx : ( XInteger ) @ "buy_idx" ; { _ } }} . 
 	 	 refine {{ sells_amount : ( XInteger128 ) @ "sells_amount" ; { _ } }} . 
 	 	 refine {{ sells : ( ( XList OrderInfo ) ) @ "sells" ; { _ } }} . 
 	 	 refine {{ buys_amount : ( XInteger128 ) @ "buys_amount" ; { _ } }} . 
 	 	 refine {{ buys : ( ( XList OrderInfo ) ) @ "buys" ; { _ } }} . 
 	 	 refine {{ new 'd : ( dealer ) @ "d" := {} ; { _ } }} . 
(*  	 	       NEW { tip3root , notify_addr , price , deals_limit . get ( ) , tons_cfg , sells_amount , sells , buys_amount , buys , { } } ; { _ } }} .  *)
(*  	 	 refine {{ d ^^ dealer:process_queue ( sell_idx , buy_idx ) ; { _ } }} .  *)
 	 	 refine {{ return_ {} (* [ d ^^ dealer:sells_amount_ , d ^^ dealer:sells_ , d ^^ dealer:buys_amount_ , d ^^ dealer:buys_ , d ^^ dealer:ret_ ] *) }} . 
 Defined . 
 
 
 
 Definition Price_Ф_processQueue : UExpression PhantomType false . 
 	 	 refine {{ if ( TRUE (* (Price.sells_ ->empty) \\ (Price.buys_ ->empty) *) ) 
               then { { _ : UExpression PhantomType false } } ; { _ } }} . 
 	 	 	 refine {{ return_ {} }} . 
 	 	 refine {{ new 'sells_amount : ( XInteger128 ) @ "sells_amount" := {} ; { _ } }} . 
 	 	 refine {{ new 'sells : ( XList OrderInfo ) @ "sells" := {} ; { _ } }} . 
 	 	 refine {{ new 'buys_amount : ( XInteger128 ) @ "buys_amount" := {} ; { _ } }} . 
 	 	 refine {{ new 'buys : ( XList OrderInfo ) @ "buys" := {}; { _ } }} . 
 	 	 refine {{ new 'ret : ( XMaybe OrderRet ) @ "ret" := {} ; { _ } }} . 
(*  	 	     [ { sells_amount } , { sells } , { buys_amount } , { buys } , { ret } ] := process_queue_impl ( tip3cfg_ . root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , 0 , 0 , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; { _ } }} .  *)
 	 	 refine {{ Price.sells_ := !{sells} ; { _ } }} . 
 	 	 refine {{ Price.buys_ := !{buys} ; { _ } }} . 
 	 	 refine {{ Price.sells_amount_ := !{ sells_amount } ; { _ } }} . 
 	 	 refine {{ Price.buys_amount_ := !{buys_amount} ; { _ } }} . 
 	 	 refine {{ if ( TRUE (* Price.sells_ ->empty \\ Price.buys_ ->empty *) ) then { { _: UExpression PhantomType false } } }} . 
 	 	 	 refine {{ return_ {} (* suicide ( flex_ ) *) }} .  
 Defined . 
 
 
 Definition dealer_Ф_process_queue ( sell_idx : XInteger ) ( buy_idx : XInteger ) 
: UExpression PhantomType false . 
 	 	 refine {{ sell_idx : ( XInteger ) @ "sell_idx" ; { _ } }} . 
 	 	 refine {{ buy_idx : ( XInteger ) @ "buy_idx" ; { _ } }} . 
 	 	 refine {{ new 'sell_opt : ( XMaybe (XInteger # OrderInfo)%sol ) @ "sell_opt" := {} ; { _ } }} . 
 	 	 refine {{ new 'buy_opt : ( XMaybe (XInteger # OrderInfo)%sol ) @ "buy_opt" := {} ; { _ } }} . 
 	 	 refine {{ new 'deals_count : ( XInteger ) @ "deals_count" := 0 ; { _ } }} . 
 	 	 refine {{ while ( TRUE ) do { { _ : UExpression PhantomType false } } ; { _ } }} . 
(*  	 	 	 refine {{ std : : tie ( sell_opt , sells_ , sells_amount_ ) 
           := dealer_Ф_extract_active_order_ref ( !{sell_opt} dealer.sells_ dealer.sells_amount_ , TRUE ) ; { _ } }} .  *)
 (* 	 	 	 refine {{ tie ( buy_opt , buys_ , buys_amount_ ) :
           := dealer_Ф_extract_active_order_ref ( !{buy_opt} dealer.buys_ dealer.buys_amount_ TRUE ) ; { _ } }} . *) 
 	 	 	 refine {{ if ( ~ !{ sell_opt } \\ ~ !{ buy_opt } ) then { { _: UExpression PhantomType false  } } ; { _ } }} . 
 	 	 	 	 refine {{ { sell_opt } := !{ sell_opt } (* break *) }} . 
 	 	 	 refine {{ new 'sell_idx_cur : ( XInteger ) @ "sell_idx_cur"  := {} ; { _ } }} . 
 	 	   refine {{ new 'sell : ( OrderInfo ) @ "sell" := {} ; { _ } }} . 
(*  	 	         [ { sell_idx_cur } , { sell } ] := *sell_opt ; { _ } }} .  *)
 	 	 	 refine {{ new 'buy_idx_cur : ( XInteger ) @ "buy_idx_cur" := {} ; { _ } }} . 
 	 	   refine {{ new 'buy : ( OrderInfo ) @ "buy" := {} ; { _ } }} . 
(*  	 	         [ { buy_idx_cur } , { buy } ] := *buy_opt ; { _ } }} .  *)
 	 	 	 refine {{ new 'sell_out_of_tons : ( XBool ) @ "sell_out_of_tons" := FALSE ; { _ } }} . 
	 	 	 refine {{ new 'buy_out_of_tons : ( XBool ) @ "buy_out_of_tons" := FALSE ; { _ } }} . 
 	 	 	 refine {{ new 'deal_amount : ( XInteger128 ) @ "deal_amount" := 0 ; { _ } }} . 
 	 	 	 refine {{ if ( TRUE (* ++ !{ deals_count } > dealer.deals_limit_ *) ) then { { _ : UExpression PhantomType false} } ; { _ } }} . 
 	 	 	 	 refine {{ new 'half_process_queue: (XInteger) @ "half_process_queue" := 1 (* TonsConfig.tons_cfg_ . process_queue  / 2 *) ; { _ } }} . 
 	 	 	 	 refine {{ new 'safe_extra : ( XInteger ) @ "safe_extra" := {} ; { _ } }} . 
(*  	 	 	 	          { safe_extra } := dealer.tons_cfg_ ^^ return_ownership + dealer.tons_cfg_ ^^ order_answer ; { _ } }} .  *)
 	 	 	 	 refine {{ if ( (* sell ^^ OrderInfo.account *) 0 < !{half_process_queue} + !{ safe_extra } ) 
                   then { { _ : UExpression PhantomType false } } ; { _ } }} . 
 	 	 	 	 	 refine {{ { sell_out_of_tons } := TRUE }} . 
 	 	 	 refine {{ if ( (* buy OrderInfo.account *) 0 < !{half_process_queue} + !{ safe_extra } ) 
                 then { { _: UExpression PhantomType false } } ; { _ } }} . 
 	 	 	 	 refine {{ { buy_out_of_tons } := TRUE }} . 
 	 	 refine {{ if ( ~ !{ sell_out_of_tons } && ~ !{ buy_out_of_tons } ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
(*  	 	 	 refine {{ { sell OrderInfo.account -= !{half_process_queue} ; { _ } }} . 
 	 	 	 refine {{ buy OrderInfo.account -= !{half_process_queue} ; { _ } }} . 
 	 	 	 refine {{ IPricePtr ( address { tvm_myaddr ( ) } ) ( Grams ( tons_cfg_ . process_queue . get ( ) ) ) . processQueue ( ) ; { _ } }} . *) 	 	 	 
     refine {{ if ( !{ sell_idx } == !{ sell_idx_cur } ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
refine {{ { sell_idx } := !{ sell_idx } (* dealer.ret_ ->set { ec : : deals_limit , sell ^^ original_amount - sell ^^ amount , sell ^^ amount } *) }} . 
 	 	 	 refine {{ if ( !{ buy_idx } == !{ buy_idx_cur } ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
refine {{ { sell_idx } := !{ sell_idx } (* dealer.ret_ ->set { ec : : deals_limit , buy ^^ original_amount - buy ^^ amount , buy ^^ amount }*) }} . 
refine {{ { sell_idx } := !{ sell_idx } (* break *) }} . 

 refine {{ if ( ~ !{ sell_out_of_tons } && ~ !{ buy_out_of_tons } ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
refine {{ { sell_idx } := !{ sell_idx } (* std : : tie ( sell_out_of_tons , buy_out_of_tons , deal_amount ) := dealer_Ф_make_deal_ref ( !{sell} !{buy} ) *) }} . 
 refine {{ if ( !{ sell_out_of_tons } ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
refine {{ { sell_idx } := !{ sell_idx } (* dealer.sells_ . pop ( ) *) ; { _ } }} . 
 	 refine {{ new 'ret : ( OrderRet ) @ "ret" := {} ; { _ } }} . 
(*  	           NEW { uint32 ( ec : : out_of_tons ) , sell . original_amount - sell . amount , uint128 { 0 } } ; { _ } }} .  *)
 	 refine {{ if ( !{ sell_idx } == !{ sell_idx_cur } ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
 	 	 refine {{ (* dealer.ret_ *) { ret } := !{ ret } }} . 
 	 refine {{ if ( (* sell ^^ OrderInfo:account *) 1 > 1 (* dealer.tons_cfg_ ^^ TonsConfig:return_ownership *) ) 
             then { { _ : UExpression PhantomType false } } ; { _ } }} . 
refine {{ { sell_idx_cur } := !{ sell_idx_cur } (* sell ^^ OrderInfo:account -= dealer.tons_cfg_ ^^ TonsConfig:return_ownership *) (* ; { _ }  *)}} . 
(*  	 	 refine {{ ITONTokenWalletPtr ( sell . tip3_wallet ) ( Grams ( tons_cfg_ . return_ownership . get ( ) ) ) . returnOwnership ( ) ; { _ } }} . 
 	 	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { true } ) }} . *) 
refine {{ { sell_idx_cur } := !{ sell_idx_cur } (* sell_opt ^^ OrderInfoWithIdx ->reset *) }} . 

 refine {{ if ( !{ buy_out_of_tons } ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
(*  	 refine {{ { buys_ . pop ( ) ; { _ } }} .  *)
 	 refine {{ new 'ret : ( OrderRet ) @ "ret" := {} ; { _ } }} . 
(*  	          { ret } := NEW { uint32 ( ec : : out_of_tons ) , buy . original_amount - buy . amount , uint128 { 0 } } ; { _ } }} .  *)
 	 refine {{ if ( !{ buy_idx } == !{ buy_idx_cur } ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
 	 	 refine {{ (* dealer.ret_ *) { ret } := !{ ret } }} . 
(*  	 refine {{ IPriceCallbackPtr ( buy . client_addr ) ( Grams ( buy . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { false } ) ; { _ } }} . 
 	 refine {{ buy_opt ^^ OrderInfoWithIdx ->reset }} . *) 
refine {{ { buy_idx } := !{ buy_idx } }} .

 refine {{ if ( !{ sell_out_of_tons } \\ !{ buy_out_of_tons } ) then { { _ : UExpression PhantomType false} } ; { _ } }} . 
 	 refine {{ { buy_idx } := !{ buy_idx } (* continue *) }} . 
(*  refine {{ { sell_opt } ->second = !{sell} ; { _ } }} . 
 refine {{ { buy_opt } ->second = !{buy} ; { _ } }} . *) 
(*  refine {{ dealer.sells_amount_ -= !{ deal_amount } ; { _ } }} . 
 refine {{ dealer.buys_amount_ -= !{ deal_amount } ; { _ } }} . *) 
   refine {{ if ( ~ TRUE (* sell ^^ OrderInfo:amount *) ) then { { _ : UExpression PhantomType false} } ; { _ } }} . 
(*  	 refine {{ { dealer.sells_ . pop ( ) ; { _ } }} .  *)
 	 refine {{ new 'ret : ( OrderRet ) @ "ret" := {} ; { _ } }} . 
(*  	        NEW { uint32 ( ok ) , sell . original_amount , uint128 { 0 } } ; { _ } }} .  *)
 	 refine {{ if ( !{ sell_idx } == !{ sell_idx_cur } ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
refine {{ { buy_idx } := !{ buy_idx } (* dealer.ret_ := !{ ret } *) }} . 
(*  	 refine {{ IPriceCallbackPtr ( sell . client_addr ) ( Grams ( sell . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { true } ) ; { _ } }} .  *)
    refine {{ {sell_opt} ->reset }} . 
 refine {{ if ( ~ TRUE (* {buy} ^^ OrderInfo:amount *) ) then { { _: UExpression PhantomType false } }  }} . 
(*  	 refine {{ { buys_ . pop ( ) ; { _ } }} .  *)
 	 refine {{ new 'ret : ( OrderRet ) @ "ret" := {} ; { _ } }} . 
(*  	          { ret } := NEW { uint32 ( ok ) , buy . original_amount , uint128 { 0 } } ; { _ } }} .  *)
 	 refine {{ if ( !{ buy_idx } == !{ buy_idx_cur } ) then { { _: UExpression PhantomType false } }  ; { _ } }} . 
 	 	 refine {{ { buy_idx } := !{ buy_idx } (* dealer.ret_ := !{ ret } *) }} .
 
(*  	 refine {{ IPriceCallbackPtr ( buy . client_addr ) ( Grams ( buy . account . get ( ) ) ) . onOrderFinished ( ret , bool_t { false } ) ; { _ } }} .  *)
 	 refine {{ {buy_opt} ->reset }} . 
 refine {{ if ( !{ sell_opt } (* && !{ sell_opt } ->second ^^ amount *) ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
 	 refine {{ new 'sell : OrderInfo @ "sell" := {} (* (!{sell_opt} ->second) ->get *) ; { _ } }} . 
refine {{ { buy_idx } := !{ buy_idx } (* dealer.sells_ ^^ change_front ( sell ) *) ; { _ } }} . 
 	 refine {{ if ( TRUE (* !{ sell_idx } == !{ sell_opt } ->first *) ) then { { _: UExpression PhantomType false } } ; { _ } }} . 
refine {{ { buy_idx } := !{ buy_idx } (* dealer.ret_ := OrderRet { ok , sell ^^ original_amount - sell ^^ amount , sell ^^ amount } *) }} . 
 refine {{ if ( !{ buy_opt } (* && !{ buy_opt } ->second ^^ amount *) ) then { { _ : UExpression PhantomType false } } }} . 
 	 refine {{ new 'buy : OrderInfo @ "buy" := {} (* buy_opt - > second  *); { _ } }} . 
(*  	 refine {{ dealer.buys_ ^^ change_front ( buy ) ; { _ } }} .  *)
 	 refine {{ if ( TRUE (* !{ buy_idx } == !{ buy_opt } ->first *) ) then { { _: UExpression PhantomType false } } }} . 
 	 	 refine {{ { buy_idx } := !{ buy_idx } (* dealer.ret_ := OrderRet { ok , buy ^^ original_amount - buy ^^ amount , buy ^^ amount } *) }} . 

refine {{ { buy_idx } := !{ buy_idx } }}.
refine {{ { buy_idx } := !{ buy_idx } }}.

 Defined . 
 
 
 Definition Price_Ф_onTip3LendOwnershipMinValue : UExpression XInteger128 false . 
 	 	 refine {{ return_ {} (* Price.tons_cfg_ ^^ TonsConfig:process_queue + Price.tons_cfg_ ^^ TonsConfig:transfer_tip3 + 
                       Price.tons_cfg_ ^^ TonsConfig:send_notify + Price.tons_cfg_ ^^ TonsConfig:return_ownership + 
                       Price.tons_cfg_ ^^ TonsConfig:order_answer *) }} . 
 Defined . 
 
(* inline
std::pair<StateInit, uint256> prepare_internal_wallet_state_init_and_addr(
  string name, string symbol, uint8 decimals, uint256 root_public_key,
  uint256 wallet_public_key, address root_address, std::optional<address> owner_address,
  cell code, int8 workchain_id
) {
  DTONTokenWalletInternal wallet_data {
    name, symbol, decimals,
    uint128(0), root_public_key, wallet_public_key,
    root_address, owner_address,
    {}, code, workchain_id
  };
  cell wallet_data_cl =
    prepare_persistent_data<ITONTokenWallet, void, DTONTokenWalletInternal>({}, wallet_data);
  StateInit wallet_init {
    /*split_depth*/{}, /*special*/{},
    code, wallet_data_cl, /*library*/{}
  };
  cell wallet_init_cl = build(wallet_init).make_cell();
  return { wallet_init, uint256(tvm_hash(wallet_init_cl)) };
} *)

 
 Definition Price_Ф_expected_wallet_address ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : UExpression XInteger256 false . 
 	 	 refine {{ wallet_pubkey : ( XInteger256 ) @ "wallet_pubkey" ; { _ } }} . 
 	 	 refine {{ internal_owner : ( XInteger256 ) @ "internal_owner" ; { _ } }} . 
 	 	 refine {{ new 'owner_addr : ( XMaybe XAddress ) @ "owner_addr" := {} ; { _ } }} . 
 	 	 refine {{ if ( !{ internal_owner } ) then { { _: UExpression XInteger256 false } } ; { _ } }} . 
 	 	 	 refine {{ { owner_addr } := {} (* Address :: make_std ( Price.workchain_id_ , !{ internal_owner } )  *) }} . 
 	 	 refine {{ return_ {} (* prepare_internal_wallet_state_init_and_addr ( Price.tip3cfg_ ^^ name , Price.tip3cfg_ ^^ symbol , Price.tip3cfg_ ^^ decimals , Price.tip3cfg_ ^^ root_public_key , !{ wallet_pubkey } , Price.tip3cfg_ ^^ root_address , !{ owner_addr } , Price.tip3_code_ , Price.workchain_id_ ) . second *) }} . 
 
 Defined . 
 
 
 
 Definition Price_Ф_verify_tip3_addr ( tip3_wallet : XAddress ) ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) : UExpression XBool false . 
 	 	 refine {{ tip3_wallet : ( XAddress ) @ "tip3_wallet" ; { _ } }} . 
 	 	 refine {{ wallet_pubkey : ( XInteger256 ) @ "wallet_pubkey" ; { _ } }} . 
 	 	 refine {{ internal_owner : ( XInteger256 ) @ "internal_owner" ; { _ } }} . 
 	 	 refine {{ new 'expected_address : ( auto ) @ "expected_address" := {} ; { _ } }} . 
(*  	 	      { expected_address } := expected_wallet_address ( !{ wallet_pubkey } , !{ internal_owner } ) ; { _ } }} .  *)
 	 	 refine {{ return_ (* Std :: get < addr_std > ( !{ tip3_wallet } ( ) ) . address *) 0 == !{ expected_address } }} . 
 Defined . 
 
 
 
 Definition Price_Ф_on_sell_fail ( ec : XInteger ) ( wallet_in : ITONTokenWalletPtr ) : UExpression OrderRet false . 
 	 	 refine {{ ec : ( XInteger ) @ "ec" ; { _ } }} . 
 	 	 refine {{ wallet_in : ( ITONTokenWalletPtr ) @ "wallet_in" ; { _ } }} . 
(*  	 	 refine {{ wallet_in ( Grams ( tons_cfg_ . return_ownership . get ( ) ) ) . returnOwnership ( ) ; { _ } }} .  *)
 	 	 refine {{ if ( TRUE (* Price.sells_ ->empty && Price.buys_ ->empty *) ) 
               then { { _: UExpression OrderRet false } } 
               else { { _: UExpression OrderRet false } } ; { _ } }} . 
 	 	 	 refine {{ { ec } := !{ ec } (* set_int_return_flag ( SEND_ALL_GAS | DELETE_ME_IF_I_AM_EMPTY ) *) }} .
 	 refine {{ new 'incoming_value : XInteger @ "incoming_value" := {} (* int_value ( ) . get ( ) *) ; { _ } }} . 
(*  	 refine {{ tvm_rawreserve ( tvm_balance ( ) - incoming_value , rawreserve_flag : : up_to ) ; { _ } }} .  *)
 	 refine {{ { ec } := !{ ec } (* Set_int_return_flag ( SEND_ALL_GAS ) *) }} . 
 refine {{ return_ {} (* [ ec , { } , { } ]  *) }} . 
Defined . 
 
 
 Definition t1 := UExpression OrderRet false .
 Definition Price_Ф_onTip3LendOwnership ( answer_addr : XAddress ) ( balance : XInteger128 )
( lend_finish_time : XInteger32 ) ( pubkey : XInteger256 ) ( internal_owner : XAddress )
 ( payload : TvmCell ) : UExpression OrderRet false . 
 	 	 refine {{ answer_addr : ( XAddress ) @ "answer_addr" ; { _ } }} . 
 	 	 refine {{ balance : ( XInteger128 ) @ "balance" ; { _ } }} . 
 	 	 refine {{ lend_finish_time : ( XInteger32 ) @ "lend_finish_time" ; { _ } }} . 
 	 	 refine {{ pubkey : ( XInteger256 ) @ "pubkey" ; { _ } }} . 
 	 	 refine {{ internal_owner : ( XAddress ) @ "internal_owner" ; { _ } }} . 
 	 	 refine {{ payload : ( TvmCell ) @ "payload" ; { _ } }} . 
 	 	 refine {{ tip3_wallet : ( XAddress ) @ "tip3_wallet" ; { _ } }} . 
 	 	 refine {{ value : ( Grams ) @ "value" ; { _ } }} . 
 	 	 refine {{ [ { tip3_wallet } , { value } ] := {} (* int_sender_and_value ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'wallet_in : ITONTokenWalletPtr @ "wallet" := !{ tip3_wallet } ; { _ } }} . 
 	 	 refine {{ new 'ret_owner_gr : Grams @ "ret_owner_gr" := {} (* tons_cfg_ . TonsConfig:return_ownership *) ; { _ } }} . 
(*  	 	 refine {{ set_int_sender ( answer_addr ) ; { _ } }} . 
 	 	 refine {{ set_int_return_value ( tons_cfg_ . order_answer . get ( ) ) ; { _ } }} . *) 	 	 
     refine {{ new 'min_value : ( XInteger128 ) @ "min_value" := Price_Ф_onTip3LendOwnershipMinValue_ref_ ( ) ; { _ } }} . 
 	 	 refine {{ new 'args : ( auto ) @ "args" := {} ; { _ } }} . 
(*  	 	         { args } := parse ( payload . ctos ( ) ) ; { _ } }} .  *)
 	 	 refine {{ new 'amount : ( auto ) @ "amount" := {} ; { _ } }} . 
(*  	 	            { amount } := args ^^ auto:amount ; { _ } }} .  *)
 	 	 refine {{ new 'err : ( XInteger ) @ "err" := 0 ; { _ } }} . 
 	 	 refine {{ if ( !{value}  < !{ min_value } ) then { { _:t1 } } else { { _:t1 } } }} . 
 	 	 	 refine {{ { err } := {} (* ec::not_enough_tons_to_process *) }} . 
 	 	 refine {{ if ( ~ TRUE (* Price_Ф_verify_tip3_addr_ref_ ( !{ tip3_wallet }  !{ pubkey } 1 (* (std : : get < addr_std > ( internal_owner ^^ XAddress:val ( ) ) . address ) *) ) *) )
               then { { _:t1 } } else { { _:t1 } } }} . 
 	 	 	 refine {{ { err } := {} (* ec::unverified_tip3_wallet *) }} . 
 	 	 refine {{ if ( TRUE (* !{ amount } < Price.min_amount_ *) ) then { { _:t1 } } else { { _:t1 } } }} . 
 	 	 	 refine {{ { err } := {} (* ec::not_enough_tokens_amount *) }} . 
 	 	 refine {{ if ( !{ balance } < !{ amount } ) then { { _:t1 } } else { { _:t1 } } }} . 
 	 	 	 refine {{ { err } := {} (* ec::too_big_tokens_amount *) }} . 
 	 	 refine {{ if ( ~ TRUE (* Ф_calc_cost_ref_ ( !{ amount } (* Price.price_ *) ) *) ) 
               then { { _:t1 } } else { { _:t1 } } }} . 
 	 	 	 refine {{ { err } := {} (* ec::too_big_tokens_amount *) }} . 
 	 	 refine {{ if ( ~ Ф_is_active_time_ref_ ( !{ lend_finish_time } ) ) 
               then { { _:t1 } } ; { _ } }}. 
 	 	 	 refine {{ { err } := {} (* ec::expired *) }} . 

 	 	 refine {{ if ( !{ err } ) then { { _ :t1 } } ; { _ } }} . 
 	 	 	 refine {{ return_ {} (* Price_Ф_on_sell_fail_ref_ ( !{ err } !{wallet_in} ) *) }} . 

 	 	 refine {{ new 'account : ( XInteger128 ) @ "account" := {} ; { _ } }} . 
(*  	 	      { account } := value . get ( ) - Price.tons_cfg_ ^^ process_queue - Price.tons_cfg_ ^^ order_answer ; { _ } }} .  *)
 	 	 refine {{ new 'sell : ( OrderInfo ) @ "sell" := {} ; { _ } }} . 
(*  	 	      { sell } := NEW { amount , amount , account , tip3_wallet , args . receive_wallet , lend_finish_time } ; { _ } }} .  *)
(*  	 	 refine {{ Price.sells_ . push ( sell ) ; { _ } }} .  *)
(*  	 	 refine {{ Price.sells_amount_ += 1 (* sell ^^ OrderInfo:amount *) ; { _ } }} . 
 	 	 refine {{ Price.notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderAdded ( bool_t { true } , tip3cfg_ . root_address , price_ , sell . amount , sells_amount_ ) ; { _ } }} . 
 	 	 refine {{ sells_amount : ( auto ) @ "sells_amount" ; { _ } }} . 
 	 	 refine {{ sells : ( auto ) @ "sells" ; { _ } }} . 
 	 	 refine {{ buys_amount : ( auto ) @ "buys_amount" ; { _ } }} . 
 	 	 refine {{ buys : ( auto ) @ "buys" ; { _ } }} . 
 	 	 refine {{ ret : ( auto ) @ "ret" ; { _ } }} . 
 	 	 refine {{ [ { sells_amount } , { sells } , { buys_amount } , { buys } , { ret } ] := process_queue_impl ( tip3cfg_ . root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , sells_ . back_with_idx ( ) . first , 0 , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; { _ } }} . 
 	 	 refine {{ Price.sells_ := sells ; { _ } }} . 
 	 	 refine {{ Price.buys_ := buys ; { _ } }} . 
 	 	 refine {{ Price.sells_amount_ := !{ sells_amount } ; { _ } }} . 
 	 	 refine {{ Price.buys_amount_ := buys_amount ; { _ } }} . 
 	 	 refine {{ if ( Price.sells_ ^^ empty ( ) && Price.buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ suicide ( flex_ ) }} . 
 	 	 refine {{ if ( ret ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ return_ *ret }} . 
 *) 	 	 refine {{ return_ {} (* [ ok , 0 , sell ^^ OrderInfo:amount ] *)  }} . 
 Defined . 
 
 (**********************************************************************
 
 Definition Price_Ф_buyTip3MinValue ( buy_cost : XInteger128 ) : UExpression XInteger128 false . 
 	 	 refine {{ buy_cost : ( XInteger128 ) @ "buy_cost" ; { _ } }} . 
 	 	 refine {{ return_ !{ buy_cost } + Price.tons_cfg_ ^^ process_queue + Price.tons_cfg_ ^^ transfer_tip3 + Price.tons_cfg_ ^^ send_notify + Price.tons_cfg_ ^^ order_answer ; { _ } }} . 
 Defined . 
 
 
 
 Definition Price_Ф_buyTip3 ( amount : XInteger128 ) ( receive_tip3_wallet : XAddress ) ( order_finish_time : XInteger32 ) : UExpression OrderRet true . 
 	 	 refine {{ amount : ( XInteger128 ) @ "amount" ; { _ } }} . 
 	 	 refine {{ receive_tip3_wallet : ( XAddress ) @ "receive_tip3_wallet" ; { _ } }} . 
 	 	 refine {{ order_finish_time : ( XInteger32 ) @ "order_finish_time" ; { _ } }} . 
 	 	 refine {{ sender : ( auto ) @ "sender" ; { _ } }} . 
 	 	 refine {{ value_gr : ( auto ) @ "value_gr" ; { _ } }} . 
 	 	 refine {{ [ { sender } , { value_gr } ] := int_sender_and_value ( ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( !{ amount } >= Price.min_amount_ ) , ec : : not_enough_tokens_amount ) ; { _ } }} . 
 	 	 refine {{ new 'cost : ( auto ) @ "cost" ; { _ } }} . 
 	 	 refine {{ { cost } := calc_cost ( !{ amount } , Price.price_ ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( ! ! !{ cost } ) , ec : : too_big_tokens_amount ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( value_gr ^^ get ( ) > buyTip3MinValue ( *cost ) ) , ec : : not_enough_tons_to_process ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( is_active_time ( !{ order_finish_time } ) ) , ec : : expired ) ; { _ } }} . 
 	 	 refine {{ set_int_return_value ( tons_cfg_ . order_answer . get ( ) ) ; { _ } }} . 
 	 	 refine {{ new 'account : ( XInteger128 ) @ "account" ; { _ } }} . 
 	 	 refine {{ { account } := value_gr . get ( ) - Price.tons_cfg_ ^^ process_queue - Price.tons_cfg_ ^^ order_answer ; { _ } }} . 
 	 	 refine {{ new 'buy : ( OrderInfoP ) @ "buy" ; { _ } }} . 
 	 	 refine {{ { buy } := NEW { amount , amount , account , receive_tip3_wallet , sender , order_finish_time } ; { _ } }} . 
 	 	 refine {{ Price.buys_ ^^ push ( buy ) ; { _ } }} . 
 	 	 refine {{ Price.buys_amount_ += buy ^^ OrderInfo:amount ; { _ } }} . 
 	 	 refine {{ Price.notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderAdded ( bool_t { false } , tip3cfg_ . root_address , price_ , buy . amount , buys_amount_ ) ; { _ } }} . 
 	 	 refine {{ sells_amount : ( auto ) @ "sells_amount" ; { _ } }} . 
 	 	 refine {{ sells : ( auto ) @ "sells" ; { _ } }} . 
 	 	 refine {{ buys_amount : ( auto ) @ "buys_amount" ; { _ } }} . 
 	 	 refine {{ buys : ( auto ) @ "buys" ; { _ } }} . 
 	 	 refine {{ ret : ( auto ) @ "ret" ; { _ } }} . 
 	 	 refine {{ [ { sells_amount } , { sells } , { buys_amount } , { buys } , { ret } ] := process_queue_impl ( tip3cfg_ . root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , 0 , buys_ . back_with_idx ( ) . first , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; { _ } }} . 
 	 	 refine {{ Price.sells_ := sells ; { _ } }} . 
 	 	 refine {{ Price.buys_ := buys ; { _ } }} . 
 	 	 refine {{ Price.sells_amount_ := !{ sells_amount } ; { _ } }} . 
 	 	 refine {{ Price.buys_amount_ := buys_amount ; { _ } }} . 
 	 	 refine {{ if ( Price.sells_ ^^ empty ( ) && Price.buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ suicide ( flex_ ) }} . 
 	 	 refine {{ if ( ret ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ return_ *ret }} . 
 	 	 refine {{ return_ [ ok , 0 , buy ^^ OrderInfo:amount ] ; { _ } }} . 
 
 
 Defined . 
 
 
 
 Definition Ф_cancel_order_impl ( orders : ( XList OrderInfo ) ) ( client_addr : addr_std_fixed ) ( all_amount : XInteger128 ) ( sell : XBool ) ( return_ownership : Grams ) ( process_queue : Grams ) ( incoming_val : Grams ) : UExpression ( XList OrderInfo ) false . 
 	 	 refine {{ orders : ( ( XList OrderInfo ) ) @ "orders" ; { _ } }} . 
 	 	 refine {{ client_addr : ( addr_std_fixed ) @ "client_addr" ; { _ } }} . 
 	 	 refine {{ all_amount : ( XInteger128 ) @ "all_amount" ; { _ } }} . 
 	 	 refine {{ sell : ( XBool ) @ "sell" ; { _ } }} . 
 	 	 refine {{ return_ownership : ( Grams ) @ "return_ownership" ; { _ } }} . 
 	 	 refine {{ process_queue : ( Grams ) @ "process_queue" ; { _ } }} . 
 	 	 refine {{ incoming_val : ( Grams ) @ "incoming_val" ; { _ } }} . 
 	 	 refine {{ new 'is_first : ( XBool ) @ "is_first" ; { _ } }} . 
 	 	 refine {{ { is_first } := true ; { _ } }} . 
 	 	 refine {{ for ( auto it = orders ^^ ):begin ( ) ; it != orders ^^ ):end ( ) ; ) { { _ } } ; { _ } }} . 
 	 	 	 refine {{ { auto next_it = std : : next ( it ) ; { _ } }} . 
 	 	 	 refine {{ new 'ord : ( auto ) @ "ord" ; { _ } }} . 
 	 	 	 refine {{ { ord } := *it ; { _ } }} . 
 	 	 	 refine {{ if ( ord ^^ auto:client_addr == !{ client_addr } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 	 refine {{ { unsigned minus_val = is_first ? process_queue . get ( ) : 0 ; { _ } }} . 
 	 	 	 	 refine {{ if ( !{ sell } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 	 	 refine {{ { ITONTokenWalletPtr ( ord . tip3_wallet ) ( return_ownership ) . returnOwnership ( ) ; { _ } }} . 
 	 	 	 	 	 refine {{ minus_val += return_ownership ^^ Grams:get ( ) }} . 
 	 	 	 refine {{ new 'plus_val : ( XInteger ) @ "plus_val" ; { _ } }} . 
 	 	 	 refine {{ { plus_val } := ord ^^ auto:account . get ( ) + ( !{ is_first } ? incoming_val ^^ Grams:get ( ) : 0 ) ; { _ } }} . 
 	 	 	 refine {{ { is_first } := false ; { _ } }} . 
 	 	 	 refine {{ if ( !{ plus_val } > minus_val ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 	 refine {{ { unsigned ret_val = plus_val - minus_val ; { _ } }} . 
 	 	 	 	 refine {{ new 'ret : ( OrderRetP ) @ "ret" ; { _ } }} . 
 	 	 	 	 refine {{ { ret } := NEW { uint32 ( ec : : canceled ) , ord . original_amount - ord . amount , uint128 { 0 } } ; { _ } }} . 
 	 	 	 	 refine {{ IPriceCallbackPtr ( ord . client_addr ) ( Grams ( ret_val ) ) . onOrderFinished ( ret , sell ) }} . 
 	 	 refine {{ { all_amount } -= ord ^^ auto:amount ; { _ } }} . 
 	 	 refine {{ orders ^^ ):erase ( it ) }} . 
 refine {{ it := next_it }} . 
 refine {{ return_ [ !{ orders } , !{ all_amount } ] ; { _ } }} . 
 
 
 
 
 Defined . 
 
 
 
 Definition Price_Ф_cancelSell : UExpression PhantomType false . 
 	 	 refine {{ new 'canceled_amount : ( auto ) @ "canceled_amount" ; { _ } }} . 
 	 	 refine {{ { canceled_amount } := Price.sells_amount_ ; { _ } }} . 
 	 	 refine {{ new 'client_addr : ( addr_std_fixedP ) @ "client_addr" ; { _ } }} . 
 	 	 refine {{ { client_addr } := int_sender ( ) ; { _ } }} . 
 	 	 refine {{ new 'value : ( auto ) @ "value" ; { _ } }} . 
 	 	 refine {{ { value } := int_value ( ) ; { _ } }} . 
 	 	 refine {{ sells : ( auto ) @ "sells" ; { _ } }} . 
 	 	 refine {{ sells_amount : ( auto ) @ "sells_amount" ; { _ } }} . 
 	 	 refine {{ [ { sells } , { sells_amount } ] := cancel_order_impl ( sells_ , client_addr , sells_amount_ , bool_t { true } , Grams ( tons_cfg_ . return_ownership . get ( ) ) , Grams ( tons_cfg_ . process_queue . get ( ) ) , value ) ; { _ } }} . 
 	 	 refine {{ Price.sells_ := !{ sells } ; { _ } }} . 
 	 	 refine {{ Price.sells_amount_ := sells_amount ; { _ } }} . 
 	 	 refine {{ { canceled_amount } -= sells_amount ; { _ } }} . 
 	 	 refine {{ Price.notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderCanceled ( bool_t { true } , tip3cfg_ . root_address , price_ , canceled_amount , sells_amount_ ) ; { _ } }} . 
 	 	 refine {{ if ( Price.sells_ ^^ empty ( ) && Price.buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ suicide ( flex_ ) }} . 
 
 Defined . 
 
 
 Definition Price_Ф_cancelBuy : UExpression PhantomType false . 
 	 	 refine {{ new 'canceled_amount : ( auto ) @ "canceled_amount" ; { _ } }} . 
 	 	 refine {{ { canceled_amount } := Price.buys_amount_ ; { _ } }} . 
 	 	 refine {{ new 'client_addr : ( addr_std_fixedP ) @ "client_addr" ; { _ } }} . 
 	 	 refine {{ { client_addr } := int_sender ( ) ; { _ } }} . 
 	 	 refine {{ new 'value : ( auto ) @ "value" ; { _ } }} . 
 	 	 refine {{ { value } := int_value ( ) ; { _ } }} . 
 	 	 refine {{ buys : ( auto ) @ "buys" ; { _ } }} . 
 	 	 refine {{ buys_amount : ( auto ) @ "buys_amount" ; { _ } }} . 
 	 	 refine {{ [ { buys } , { buys_amount } ] := cancel_order_impl ( buys_ , client_addr , buys_amount_ , bool_t { false } , Grams ( tons_cfg_ . return_ownership . get ( ) ) , Grams ( tons_cfg_ . process_queue . get ( ) ) , value ) ; { _ } }} . 
 	 	 refine {{ Price.buys_ := !{ buys } ; { _ } }} . 
 	 	 refine {{ Price.buys_amount_ := buys_amount ; { _ } }} . 
 	 	 refine {{ { canceled_amount } -= buys_amount ; { _ } }} . 
 	 	 refine {{ Price.notify_addr_ ( Grams ( tons_cfg_ . send_notify . get ( ) ) ) . onOrderCanceled ( bool_t { false } , tip3cfg_ . root_address , price_ , canceled_amount , buys_amount_ ) ; { _ } }} . 
 	 	 refine {{ if ( Price.sells_ ^^ empty ( ) && Price.buys_ ^^ empty ( ) ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ suicide ( flex_ ) }} . 
 
 Defined . 
 
 
 Definition Price_Ф_getPrice : UExpression XInteger128 false . 
 	 	 refine {{ return_ Price.price_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Price_Ф_getMinimumAmount : UExpression XInteger128 false . 
 	 	 refine {{ return_ Price.min_amount_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Price_Ф_getSellAmount : UExpression XInteger128 false . 
 	 	 refine {{ return_ Price.sells_amount_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Price_Ф_getBuyAmount : UExpression XInteger128 false . 
 	 	 refine {{ return_ Price.buys_amount_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Price_Ф_getDetails : UExpression DetailsInfo false . 
 	 	 refine {{ return_ [ getPrice ( ) , getMinimumAmount ( ) , getSellAmount ( ) , getBuyAmount ( ) ] ; { _ } }} . 
 Defined . 
 
 
 
 Definition Price_Ф_getTonsCfg : UExpression TonsConfig false . 
 	 	 refine {{ return_ Price.tons_cfg_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Price_Ф_getSells : UExpression ( XHMap XInteger ) false . 
 	 	 refine {{ return_ dict_array ( sells_ . begin ( ) , sells_ . end ( ) ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition Price_Ф_getBuys : UExpression ( XHMap XInteger ) false . 
 	 	 refine {{ return_ dict_array ( buys_ . begin ( ) , buys_ . end ( ) ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition Price_Ф__fallback ( cell : ( ) : UExpression XInteger false . 
 	 	 refine {{ cell : ( ( ) @ "cell" ; { _ } }} . 
 	 	 refine {{ return_ 0 ; { _ } }} . 
 Defined . 
 
 *****************************************)

End PriceFuncs .
 
