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

Require Import FLeXClientClass.

Require Import FLeXContractConsts.  
Require Import FLeXConstSig.
Require Import ZArith.

Require Import FLeXClientFuncsNotations.
Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG26.

Require Import UrsusStdLib.stdNotations.
Require Import UrsusStdLib.stdUFunc.
Require Import UrsusStdLib.stdFuncNotations.
Require Import UrsusTVM.tvmNotations.

Module FLeXClientFuncs (dc : FLeXConstsTypesSig XTypesModule StateMonadModule ).

Module Export FLeXClientFuncNotationsModule := FLeXClientFuncNotations XTypesModule StateMonadModule dc. 

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.


Existing Instance xbool_default.
Instance TvmCell_default : XDefault (TvmCell) := {
default := xStrNull}.
Existing Instance TvmCell_default.
Existing Instance phantom_default .


Definition FLeXClient_Ф_constructor ( pubkey : XInteger256 ) ( trading_pair_code : TvmCell ) ( xchg_pair_code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ pubkey : ( XInteger256 ) @ "pubkey" ; { _ } }} . 
 	 	 refine {{ trading_pair_code : ( TvmCell ) @ "trading_pair_code" ; { _ } }} . 
 	 	 refine {{ xchg_pair_code : ( TvmCell ) @ "xchg_pair_code" ; { _ } }} . 
 	 	 refine {{ require_ ( ( !{ pubkey } != 0 ) , error_code::zero_owner_pubkey ) ; { _ } }} . 
 	 	 refine {{ FLeXClient.owner_ := !{ pubkey } ; { _ } }} . 
 	 	 refine {{ FLeXClient.trading_pair_code_ := !{ trading_pair_code } ; { _ } }} . 
 	 	 refine {{ FLeXClient.xchg_pair_code_ := !{ xchg_pair_code } ; { _ } }} . 
 	 	 refine {{ FLeXClient.workchain_id_ := {} (*Std :: get < addr_std > ( Address { tvm_myaddr ( ) } . val ( ) ) . workchain_id *) ; { _ } }} . 
 	 	 refine {{ FLeXClient.flex_ := {} (* Address :: make_std ( 0 , 0 ) *) ; { _ } }} . 
 	 	 refine {{ FLeXClient.notify_addr_ := {} (* Address :: make_std ( 0 , 0 ) *) }} . 
 Defined . 
 
 
 Definition FLeXClient_Ф_setFlexCfg ( tons_cfg : TonsConfig ) ( flex : addr_std_compact ) ( notify_addr : addr_std_compact ) : UExpression PhantomType true . 
 	 	 refine {{ tons_cfg : ( TonsConfig ) @ "tons_cfg" ; { _ } }} . 
 	 	 refine {{ flex : ( addr_std_compact ) @ "flex" ; { _ } }} . 
 	 	 refine {{ notify_addr : ( addr_std_compact ) @ "notify_addr" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
 	 	 refine {{ FLeXClient.tons_cfg_ := !{ tons_cfg } ; { _ } }} . 
 	 	 refine {{ FLeXClient.flex_ := !{ flex } ; { _ } }} . 
 	 	 refine {{ FLeXClient.notify_addr_ := !{ notify_addr } }} . 
 Defined . 
 
 (*
 Definition FLeXClient_Ф_setExtWalletCode ( ext_wallet_code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ ext_wallet_code : ( TvmCell ) @ "ext_wallet_code" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
(*  	 	 refine {{ tvm.accept () ; { _ } }} .  *)
 	 	 refine {{ FLeXClient.ext_wallet_code_ ->set !{ ext_wallet_code }  }} . 
 Defined . 
 
 
 Definition FLeXClient_Ф_setFlexWalletCode ( flex_wallet_code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ flex_wallet_code : ( TvmCell ) @ "flex_wallet_code" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ FLeXClient.flex_wallet_code_ := !{ flex_wallet_code } ; { _ } }} . 
 Defined . 
 
 
 Definition FLeXClient_Ф_setFlexWrapperCode ( flex_wrapper_code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ flex_wrapper_code : ( TvmCell ) @ "flex_wrapper_code" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ FLeXClient.flex_wrapper_code_ := !{ flex_wrapper_code } ; { _ } }} . 
 Defined . 
 
 
 Definition FLeXClient_Ф_deployTradingPair ( tip3_root : addr_std_compact ) ( deploy_min_value : XInteger128 ) ( deploy_value : XInteger128 ) ( min_trade_amount : XInteger128 ) : UExpression XAddress true . 
 	 	 refine {{ tip3_root : ( addr_std_compact ) @ "tip3_root" ; { _ } }} . 
 	 	 refine {{ deploy_min_value : ( XInteger128 ) @ "deploy_min_value" ; { _ } }} . 
 	 	 refine {{ deploy_value : ( XInteger128 ) @ "deploy_value" ; { _ } }} . 
 	 	 refine {{ min_trade_amount : ( XInteger128 ) @ "min_trade_amount" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ new pair_data : ( DTradingPairP ) @ "pair_data" ; { _ } }} . 
 	 	 refine {{ { pair_data } := NEW { . flex_addr_ = flex_ , . tip3_root_ = tip3_root } ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := prepare_trading_pair_state_init_and_addr ( pair_data , trading_pair_code_ ) ; { _ } }} . 
 	 	 refine {{ new trade_pair : ( auto ) @ "trade_pair" ; { _ } }} . 
 	 	 refine {{ { trade_pair } := ITradingPairPtr ( Address :: make_std ( FLeXClient.workchain_id_ , std_addr ) ) ; { _ } }} . 
 	 	 refine {{ trade_pair ^^ auto:deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( min_trade_amount , deploy_min_value ) ; { _ } }} . 
 	 	 refine {{ return_ trade_pair ^^ auto:get ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_deployXchgPair ( tip3_major_root : addr_std_compact ) ( tip3_minor_root : addr_std_compact ) ( deploy_min_value : XInteger128 ) ( deploy_value : XInteger128 ) ( min_trade_amount : XInteger128 ) : UExpression XAddress true . 
 	 	 refine {{ tip3_major_root : ( addr_std_compact ) @ "tip3_major_root" ; { _ } }} . 
 	 	 refine {{ tip3_minor_root : ( addr_std_compact ) @ "tip3_minor_root" ; { _ } }} . 
 	 	 refine {{ deploy_min_value : ( XInteger128 ) @ "deploy_min_value" ; { _ } }} . 
 	 	 refine {{ deploy_value : ( XInteger128 ) @ "deploy_value" ; { _ } }} . 
 	 	 refine {{ min_trade_amount : ( XInteger128 ) @ "min_trade_amount" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ new pair_data : ( DXchgPairP ) @ "pair_data" ; { _ } }} . 
 	 	 refine {{ { pair_data } := NEW { . flex_addr_ = flex_ , . tip3_major_root_ = tip3_major_root , . tip3_minor_root_ = tip3_minor_root } ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := prepare_xchg_pair_state_init_and_addr ( pair_data , xchg_pair_code_ ) ; { _ } }} . 
 	 	 refine {{ new trade_pair : ( auto ) @ "trade_pair" ; { _ } }} . 
 	 	 refine {{ { trade_pair } := IXchgPairPtr ( Address :: make_std ( FLeXClient.workchain_id_ , std_addr ) ) ; { _ } }} . 
 	 	 refine {{ trade_pair ^^ auto:deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( min_trade_amount , deploy_min_value ) ; { _ } }} . 
 	 	 refine {{ return_ trade_pair ^^ auto:get ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_preparePrice ( price : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tip3_code : TvmCell ) ( tip3cfg : Tip3Config ) ( price_code : TvmCell ) : UExpression ( StateInit # XAddress # XInteger256 ) false . 
 	 	 refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
 	 	 refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ tip3_code : ( TvmCell ) @ "tip3_code" ; { _ } }} . 
 	 	 refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
 	 	 refine {{ price_code : ( TvmCell ) @ "price_code" ; { _ } }} . 
 	 	 refine {{ new price_data : ( DPriceP ) @ "price_data" ; { _ } }} . 
 	 	 refine {{ { price_data } := NEW { . price_ = price , . sells_amount_ = uint128 ( 0 ) , . buys_amount_ = uint128 ( 0 ) , . flex_ = flex_ , . min_amount_ = min_amount , . deals_limit_ = deals_limit , . notify_addr_ = IFlexNotifyPtr ( notify_addr_ ) , . workchain_id_ = workchain_id_ , . tons_cfg_ = tons_cfg_ , . tip3_code_ = tip3_code , . tip3cfg_ = tip3cfg , . sells_ = { } , . buys_ = { } } ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := prepare_price_state_init_and_addr ( price_data , price_code ) ; { _ } }} . 
 	 	 refine {{ new addr : ( auto ) @ "addr" ; { _ } }} . 
 	 	 refine {{ { addr } := Address :: make_std ( FLeXClient.workchain_id_ , std_addr ) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ state_init } , !{ addr } , std_addr ] ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_deployPriceWithSell ( price : XInteger128 ) ( amount : XInteger128 ) ( lend_finish_time : XInteger32 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tons_value : XInteger128 ) ( price_code : TvmCell ) ( my_tip3_addr : addr_std_compact ) ( receive_wallet : addr_std_compact ) ( tip3cfg : Tip3Config ) : UExpression XAddress true . 
 	 	 refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
 	 	 refine {{ amount : ( XInteger128 ) @ "amount" ; { _ } }} . 
 	 	 refine {{ lend_finish_time : ( XInteger32 ) @ "lend_finish_time" ; { _ } }} . 
 	 	 refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ tons_value : ( XInteger128 ) @ "tons_value" ; { _ } }} . 
 	 	 refine {{ price_code : ( TvmCell ) @ "price_code" ; { _ } }} . 
 	 	 refine {{ my_tip3_addr : ( addr_std_compact ) @ "my_tip3_addr" ; { _ } }} . 
 	 	 refine {{ receive_wallet : ( addr_std_compact ) @ "receive_wallet" ; { _ } }} . 
 	 	 refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ addr : ( auto ) @ "addr" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code ) ; { _ } }} . 
 	 	 refine {{ new price_addr : ( auto ) @ "price_addr" ; { _ } }} . 
 	 	 refine {{ { price_addr } := IPricePtr ( addr ) ; { _ } }} . 
 	 	 refine {{ new deploy_init_cl : ( TvmCell ) @ "deploy_init_cl" ; { _ } }} . 
 	 	 refine {{ { deploy_init_cl } := build ( !{ state_init } ) . endc ( ) ; { _ } }} . 
 	 	 refine {{ new sell_args : ( SellArgsP ) @ "sell_args" ; { _ } }} . 
 	 	 refine {{ { sell_args } := { . amount = !{ amount } , . receive_wallet = !{ receive_wallet } } ; { _ } }} . 
 	 	 refine {{ new payload : ( TvmCell ) @ "payload" ; { _ } }} . 
 	 	 refine {{ { payload } := build ( !{ sell_args } ) . endc ( ) ; { _ } }} . 
 	 	 refine {{ ITONTokenWalletPtr my_tip3 ( my_tip3_addr ) ; { _ } }} . 
 	 	 refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . lendOwnership ( address { tvm_myaddr ( ) } , uint128 ( 0 ) , std_addr , amount , lend_finish_time , deploy_init_cl , payload ) ; { _ } }} . 
 	 	 refine {{ return_ price_addr ^^ auto:get ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_deployPriceWithBuy ( price : XInteger128 ) ( amount : XInteger128 ) ( order_finish_time : XInteger32 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( deploy_value : XInteger128 ) ( price_code : TvmCell ) ( my_tip3_addr : addr_std_compact ) ( tip3cfg : Tip3Config ) : UExpression XAddress true . 
 	 	 refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
 	 	 refine {{ amount : ( XInteger128 ) @ "amount" ; { _ } }} . 
 	 	 refine {{ order_finish_time : ( XInteger32 ) @ "order_finish_time" ; { _ } }} . 
 	 	 refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ deploy_value : ( XInteger128 ) @ "deploy_value" ; { _ } }} . 
 	 	 refine {{ price_code : ( TvmCell ) @ "price_code" ; { _ } }} . 
 	 	 refine {{ my_tip3_addr : ( addr_std_compact ) @ "my_tip3_addr" ; { _ } }} . 
 	 	 refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ addr : ( auto ) @ "addr" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code ) ; { _ } }} . 
 	 	 refine {{ IPricePtr price_addr ( addr ) ; { _ } }} . 
 	 	 refine {{ price_addr ^^ deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . buyTip3 ( amount , my_tip3_addr , order_finish_time ) ; { _ } }} . 
 	 	 refine {{ return_ price_addr ^^ get ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_cancelSellOrder ( price : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( value : XInteger128 ) ( price_code : TvmCell ) ( tip3cfg : Tip3Config ) : UExpression PhantomType true . 
 	 	 refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
 	 	 refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ value : ( XInteger128 ) @ "value" ; { _ } }} . 
 	 	 refine {{ price_code : ( TvmCell ) @ "price_code" ; { _ } }} . 
 	 	 refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ addr : ( auto ) @ "addr" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code ) ; { _ } }} . 
 	 	 refine {{ IPricePtr price_addr ( addr ) ; { _ } }} . 
 	 	 refine {{ price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelSell ( ) ; { _ } }} . 
 Defined . 
 
 
 Definition FLeXClient_Ф_cancelBuyOrder ( price : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( value : XInteger128 ) ( price_code : TvmCell ) ( tip3cfg : Tip3Config ) : UExpression PhantomType true . 
 	 	 refine {{ price : ( XInteger128 ) @ "price" ; { _ } }} . 
 	 	 refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ value : ( XInteger128 ) @ "value" ; { _ } }} . 
 	 	 refine {{ price_code : ( TvmCell ) @ "price_code" ; { _ } }} . 
 	 	 refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ addr : ( auto ) @ "addr" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := preparePrice ( price , min_amount , deals_limit , flex_wallet_code_ . get ( ) , tip3cfg , price_code ) ; { _ } }} . 
 	 	 refine {{ IPricePtr price_addr ( addr ) ; { _ } }} . 
 	 	 refine {{ price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelBuy ( ) ; { _ } }} . 
 Defined . 
 
 
 Definition FLeXClient_Ф_preparePriceXchg ( price_num : XInteger128 ) ( price_denum : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( major_tip3cfg : Tip3Config ) ( minor_tip3cfg : Tip3Config ) ( price_code : TvmCell ) : UExpression ( StateInit # XAddress # XInteger256 ) false . 
 	 	 refine {{ price_num : ( XInteger128 ) @ "price_num" ; { _ } }} . 
 	 	 refine {{ price_denum : ( XInteger128 ) @ "price_denum" ; { _ } }} . 
 	 	 refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ major_tip3cfg : ( Tip3Config ) @ "major_tip3cfg" ; { _ } }} . 
 	 	 refine {{ minor_tip3cfg : ( Tip3Config ) @ "minor_tip3cfg" ; { _ } }} . 
 	 	 refine {{ price_code : ( TvmCell ) @ "price_code" ; { _ } }} . 
 	 	 refine {{ new price_data : ( DPriceXchgP ) @ "price_data" ; { _ } }} . 
 	 	 refine {{ { price_data } := NEW { . price_ = { price_num , price_denum } , . sells_amount_ = uint128 ( 0 ) , . buys_amount_ = uint128 ( 0 ) , . flex_ = flex_ , . min_amount_ = min_amount , . deals_limit_ = deals_limit , . notify_addr_ = IFlexNotifyPtr ( notify_addr_ ) , . workchain_id_ = workchain_id_ , . tons_cfg_ = tons_cfg_ , . tip3_code_ = flex_wallet_code_ . get ( ) , . major_tip3cfg_ = major_tip3cfg , . minor_tip3cfg_ = minor_tip3cfg , . sells_ = { } , . buys_ = { } } ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { std_addr } ] := prepare_price_xchg_state_init_and_addr ( price_data , price_code ) ; { _ } }} . 
 	 	 refine {{ new addr : ( auto ) @ "addr" ; { _ } }} . 
 	 	 refine {{ { addr } := Address :: make_std ( FLeXClient.workchain_id_ , std_addr ) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ state_init } , !{ addr } , std_addr ] ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_cancelXchgOrder ( sell : XBool ) ( price_num : XInteger128 ) ( price_denum : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( value : XInteger128 ) ( xchg_price_code : TvmCell ) ( major_tip3cfg : Tip3Config ) ( minor_tip3cfg : Tip3Config ) : UExpression PhantomType true . 
 	 	 refine {{ sell : ( XBool ) @ "sell" ; { _ } }} . 
 	 	 refine {{ price_num : ( XInteger128 ) @ "price_num" ; { _ } }} . 
 	 	 refine {{ price_denum : ( XInteger128 ) @ "price_denum" ; { _ } }} . 
 	 	 refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ value : ( XInteger128 ) @ "value" ; { _ } }} . 
 	 	 refine {{ xchg_price_code : ( TvmCell ) @ "xchg_price_code" ; { _ } }} . 
 	 	 refine {{ major_tip3cfg : ( Tip3Config ) @ "major_tip3cfg" ; { _ } }} . 
 	 	 refine {{ minor_tip3cfg : ( Tip3Config ) @ "minor_tip3cfg" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ addr : ( auto ) @ "addr" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := preparePriceXchg ( price_num , price_denum , min_amount , deals_limit , major_tip3cfg , minor_tip3cfg , xchg_price_code ) ; { _ } }} . 
 	 	 refine {{ IPriceXchgPtr price_addr ( addr ) ; { _ } }} . 
 	 	 refine {{ if ( !{ sell } ) then { { _ } } else { { _ } } ; { _ } }} . 
 	 	 	 refine {{ price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelSell ( ) }} . 
 	 	 refine {{ price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelBuy ( ) ; { _ } }} . 
 
 
 Defined . 
 
 
 Definition FLeXClient_Ф_transfer ( dest : addr_std_compact ) ( value : XInteger128 ) ( bounce : XBool ) : UExpression PhantomType true . 
 	 	 refine {{ dest : ( addr_std_compact ) @ "dest" ; { _ } }} . 
 	 	 refine {{ value : ( XInteger128 ) @ "value" ; { _ } }} . 
 	 	 refine {{ bounce : ( XBool ) @ "bounce" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ tvm_transfer ( dest , value . get ( ) , bounce . get ( ) ) ; { _ } }} . 
 Defined . 
 
 
 Definition FLeXClient_Ф_deployPriceXchg ( sell : XBool ) ( price_num : XInteger128 ) ( price_denum : XInteger128 ) ( amount : XInteger128 ) ( lend_amount : XInteger128 ) ( lend_finish_time : XInteger32 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tons_value : XInteger128 ) ( xchg_price_code : TvmCell ) ( my_tip3_addr : addr_std_compact ) ( receive_wallet : addr_std_compact ) ( major_tip3cfg : Tip3Config ) ( minor_tip3cfg : Tip3Config ) : UExpression XAddress true . 
 	 	 refine {{ sell : ( XBool ) @ "sell" ; { _ } }} . 
 	 	 refine {{ price_num : ( XInteger128 ) @ "price_num" ; { _ } }} . 
 	 	 refine {{ price_denum : ( XInteger128 ) @ "price_denum" ; { _ } }} . 
 	 	 refine {{ amount : ( XInteger128 ) @ "amount" ; { _ } }} . 
 	 	 refine {{ lend_amount : ( XInteger128 ) @ "lend_amount" ; { _ } }} . 
 	 	 refine {{ lend_finish_time : ( XInteger32 ) @ "lend_finish_time" ; { _ } }} . 
 	 	 refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ tons_value : ( XInteger128 ) @ "tons_value" ; { _ } }} . 
 	 	 refine {{ xchg_price_code : ( TvmCell ) @ "xchg_price_code" ; { _ } }} . 
 	 	 refine {{ my_tip3_addr : ( addr_std_compact ) @ "my_tip3_addr" ; { _ } }} . 
 	 	 refine {{ receive_wallet : ( addr_std_compact ) @ "receive_wallet" ; { _ } }} . 
 	 	 refine {{ major_tip3cfg : ( Tip3Config ) @ "major_tip3cfg" ; { _ } }} . 
 	 	 refine {{ minor_tip3cfg : ( Tip3Config ) @ "minor_tip3cfg" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ state_init : ( auto ) @ "state_init" ; { _ } }} . 
 	 	 refine {{ addr : ( auto ) @ "addr" ; { _ } }} . 
 	 	 refine {{ std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ [ { state_init } , { addr } , { std_addr } ] := preparePriceXchg ( price_num , price_denum , min_amount , deals_limit , major_tip3cfg , minor_tip3cfg , xchg_price_code ) ; { _ } }} . 
 	 	 refine {{ new price_addr : ( auto ) @ "price_addr" ; { _ } }} . 
 	 	 refine {{ { price_addr } := IPriceXchgPtr ( addr ) ; { _ } }} . 
 	 	 refine {{ new deploy_init_cl : ( TvmCell ) @ "deploy_init_cl" ; { _ } }} . 
 	 	 refine {{ { deploy_init_cl } := build ( !{ state_init } ) . endc ( ) ; { _ } }} . 
 	 	 refine {{ new payload_args : ( PayloadArgsP ) @ "payload_args" ; { _ } }} . 
 	 	 refine {{ { payload_args } := { . sell = !{ sell } , . amount = !{ amount } , . receive_tip3_wallet = !{ receive_wallet } , . client_addr = Address { tvm_myaddr ( ) } } ; { _ } }} . 
 	 	 refine {{ new payload : ( TvmCell ) @ "payload" ; { _ } }} . 
 	 	 refine {{ { payload } := build ( !{ payload_args } ) . endc ( ) ; { _ } }} . 
 	 	 refine {{ ITONTokenWalletPtr my_tip3 ( my_tip3_addr ) ; { _ } }} . 
 	 	 refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . lendOwnership ( address { tvm_myaddr ( ) } , uint128 ( 0 ) , std_addr , lend_amount , lend_finish_time , deploy_init_cl , payload ) ; { _ } }} . 
 	 	 refine {{ return_ price_addr ^^ auto:get ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_deployWrapperWithWallet ( wrapper_pubkey : XInteger256 ) ( wrapper_deploy_value : XInteger128 ) ( wrapper_keep_balance : XInteger128 ) ( ext_wallet_balance : XInteger128 ) ( set_internal_wallet_value : XInteger128 ) ( tip3cfg : Tip3Config ) : UExpression XAddress true . 
 	 	 refine {{ wrapper_pubkey : ( XInteger256 ) @ "wrapper_pubkey" ; { _ } }} . 
 	 	 refine {{ wrapper_deploy_value : ( XInteger128 ) @ "wrapper_deploy_value" ; { _ } }} . 
 	 	 refine {{ wrapper_keep_balance : ( XInteger128 ) @ "wrapper_keep_balance" ; { _ } }} . 
 	 	 refine {{ ext_wallet_balance : ( XInteger128 ) @ "ext_wallet_balance" ; { _ } }} . 
 	 	 refine {{ set_internal_wallet_value : ( XInteger128 ) @ "set_internal_wallet_value" ; { _ } }} . 
 	 	 refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.ext_wallet_code_ ) , error_code::missed_ext_wallet_code ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.flex_wrapper_code_ ) , error_code::missed_flex_wrapper_code ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ new wrapper_data : ( WrapperP ) @ "wrapper_data" ; { _ } }} . 
 	 	 refine {{ { wrapper_data } := NEW { . name_ = tip3cfg . name , . symbol_ = tip3cfg . symbol , . decimals_ = tip3cfg . decimals , . workchain_id_ = workchain_id_ , . root_public_key_ = wrapper_pubkey , . total_granted_ = { } , . internal_wallet_code_ = { } , . owner_address_ = address { tvm_myaddr ( ) } , . start_balance_ = Grams ( wrapper_keep_balance . get ( ) ) , . external_wallet_ = { } } ; { _ } }} . 
 	 	 refine {{ wrapper_init : ( auto ) @ "wrapper_init" ; { _ } }} . 
 	 	 refine {{ wrapper_hash_addr : ( auto ) @ "wrapper_hash_addr" ; { _ } }} . 
 	 	 refine {{ [ { wrapper_init } , { wrapper_hash_addr } ] := prepare_wrapper_state_init_and_addr ( flex_wrapper_code_ . get ( ) , wrapper_data ) ; { _ } }} . 
 	 	 refine {{ IWrapperPtr wrapper_addr ( address : : make_std ( workchain_id_ , wrapper_hash_addr ) ) ; { _ } }} . 
 	 	 refine {{ wallet_init : ( auto ) @ "wallet_init" ; { _ } }} . 
 	 	 refine {{ wallet_hash_addr : ( auto ) @ "wallet_hash_addr" ; { _ } }} . 
 	 	 refine {{ [ { wallet_init } , { wallet_hash_addr } ] := prepare_external_wallet_state_init_and_addr ( tip3cfg . name , tip3cfg . symbol , tip3cfg . decimals , tip3cfg . root_public_key , wrapper_pubkey , tip3cfg . root_address , wrapper_addr . get ( ) , ext_wallet_code_ . get ( ) , workchain_id_ ) ; { _ } }} . 
 	 	 refine {{ ITONTokenWalletPtr wallet_addr ( address : : make_std ( workchain_id_ , wallet_hash_addr ) ) ; { _ } }} . 
 	 	 refine {{ wallet_addr ^^ deploy_noop ( wallet_init , Grams ( ext_wallet_balance . get ( ) ) ) ; { _ } }} . 
 	 	 refine {{ wrapper_addr ^^ deploy ( wrapper_init , Grams ( wrapper_deploy_value . get ( ) ) ) . init ( wallet_addr . get ( ) ) ; { _ } }} . 
 	 	 refine {{ wrapper_addr ( Grams ( set_internal_wallet_value . get ( ) ) ) . setInternalWalletCode ( flex_wallet_code_ . get ( ) ) ; { _ } }} . 
 	 	 refine {{ return_ wrapper_addr ^^ get ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_deployEmptyFlexWallet ( pubkey : XInteger256 ) ( tons_to_wallet : XInteger128 ) ( tip3cfg : Tip3Config ) : UExpression XAddress true . 
 	 	 refine {{ pubkey : ( XInteger256 ) @ "pubkey" ; { _ } }} . 
 	 	 refine {{ tons_to_wallet : ( XInteger128 ) @ "tons_to_wallet" ; { _ } }} . 
 	 	 refine {{ tip3cfg : ( Tip3Config ) @ "tip3cfg" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( FLeXClient.flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ init : ( auto ) @ "init" ; { _ } }} . 
 	 	 refine {{ hash_addr : ( auto ) @ "hash_addr" ; { _ } }} . 
 	 	 refine {{ [ { init } , { hash_addr } ] := prepare_internal_wallet_state_init_and_addr ( tip3cfg . name , tip3cfg . symbol , tip3cfg . decimals , tip3cfg . root_public_key , pubkey , tip3cfg . root_address , address { tvm_myaddr ( ) } , flex_wallet_code_ . get ( ) , workchain_id_ ) ; { _ } }} . 
 	 	 refine {{ ITONTokenWalletPtr new_wallet ( address : : make_std ( workchain_id_ , hash_addr ) ) ; { _ } }} . 
 	 	 refine {{ new_wallet ^^ deploy_noop ( init , Grams ( tons_to_wallet . get ( ) ) ) ; { _ } }} . 
 	 	 refine {{ return_ new_wallet ^^ get ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_burnWallet ( tons_value : XInteger128 ) ( out_pubkey : XInteger256 ) ( out_internal_owner : addr_std_compact ) ( my_tip3_addr : addr_std_compact ) : UExpression PhantomType true . 
 	 	 refine {{ tons_value : ( XInteger128 ) @ "tons_value" ; { _ } }} . 
 	 	 refine {{ out_pubkey : ( XInteger256 ) @ "out_pubkey" ; { _ } }} . 
 	 	 refine {{ out_internal_owner : ( addr_std_compact ) @ "out_internal_owner" ; { _ } }} . 
 	 	 refine {{ my_tip3_addr : ( addr_std_compact ) @ "my_tip3_addr" ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey ( ) == FLeXClient.owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ ITONTokenWalletPtr my_tip3 ( my_tip3_addr ) ; { _ } }} . 
 	 	 refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) ) . burn ( out_pubkey , out_internal_owner ) ; { _ } }} . 
 Defined . 
 
 
 Definition FLeXClient_Ф_getOwner : UExpression XInteger256 false . 
 	 	 refine {{ return_ FLeXClient.owner_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_getFlex : UExpression XAddress false . 
 	 	 refine {{ return_ FLeXClient.flex_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_hasExtWalletCode : UExpression XBool false . 
 	 	 refine {{ return bool_t { ! ! ext_wallet_code_ } ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_hasFlexWalletCode : UExpression XBool false . 
 	 	 refine {{ return bool_t { ! ! flex_wallet_code_ } ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_hasFlexWrapperCode : UExpression XBool false . 
 	 	 refine {{ return bool_t { ! ! flex_wrapper_code_ } ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф_getPayloadForDeployInternalWallet ( owner_pubkey : XInteger256 ) ( owner_addr : addr_std_compact ) ( tons : XInteger128 ) : UExpression TvmCell false . 
 	 	 refine {{ owner_pubkey : ( XInteger256 ) @ "owner_pubkey" ; { _ } }} . 
 	 	 refine {{ owner_addr : ( addr_std_compact ) @ "owner_addr" ; { _ } }} . 
 	 	 refine {{ tons : ( XInteger128 ) @ "tons" ; { _ } }} . 
 	 	 refine {{ return_ build ( FlexDeployWalletArgs { !{ owner_pubkey } , !{ owner_addr } , !{ tons } } ) . endc ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition FLeXClient_Ф__fallback ( cell : ( ) : UExpression XInteger false . 
 	 	 refine {{ cell : ( ( ) @ "cell" ; { _ } }} . 
 	 	 refine {{ return_ 0 ; { _ } }} . 
 Defined . 
 
 *)
End FLeXClientFuncs .
