Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Require Import Project.CommonConstSig.

Require Import Contracts.PriceXchg.Ledger.
Require Import Contracts.PriceXchg.Functions.FuncSig.

(* здесь инмпортируем все внешние интерфейсы *)
Require Import Contracts.PriceXchg.Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module PriceXchgPublicInterface := PublicInterface xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.

Import xt.

Fail Check OutgoingMessage_default.

Import UrsusNotations.

Local Open Scope ursus_scope.

Notation " 'Tip3Config.name' " := ( Tip3Config_ι_name ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.name' " := ( Tip3Config_ι_name ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.symbol' " := ( Tip3Config_ι_symbol ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.symbol' " := ( Tip3Config_ι_symbol ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.decimals' " := ( Tip3Config_ι_decimals ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.decimals' " := ( Tip3Config_ι_decimals ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.root_public_key' " := ( Tip3Config_ι_root_public_key ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.root_public_key' " := ( Tip3Config_ι_root_public_key ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.root_address' " := ( Tip3Config_ι_root_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'Tip3Config.root_address' " := ( Tip3Config_ι_root_address ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.num' " := ( RationalPrice_ι_num ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.num' " := ( RationalPrice_ι_num ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.denum' " := ( RationalPrice_ι_denum ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'RationalPrice.denum' " := ( RationalPrice_ι_denum ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.workchain_id' " := ( addr_std_fixed_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std_fixed.address' " := ( addr_std_fixed_ι_address ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.sell' " := ( PayloadArgs_ι_sell ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.sell' " := ( PayloadArgs_ι_sell ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.amount' " := ( PayloadArgs_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.amount' " := ( PayloadArgs_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_ι_receive_tip3_wallet ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.receive_tip3_wallet' " := ( PayloadArgs_ι_receive_tip3_wallet ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( PayloadArgs_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'PayloadArgs.client_addr' " := ( PayloadArgs_ι_client_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.original_amount' " := ( OrderInfoXchg_ι_original_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.original_amount' " := ( OrderInfoXchg_ι_original_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.amount' " := ( OrderInfoXchg_ι_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.amount' " := ( OrderInfoXchg_ι_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.account' " := ( OrderInfoXchg_ι_account ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.account' " := ( OrderInfoXchg_ι_account ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( OrderInfoXchg_ι_tip3_wallet_provide ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_provide' " := ( OrderInfoXchg_ι_tip3_wallet_provide ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( OrderInfoXchg_ι_tip3_wallet_receive ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.tip3_wallet_receive' " := ( OrderInfoXchg_ι_tip3_wallet_receive ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.client_addr' " := ( OrderInfoXchg_ι_client_addr ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.client_addr' " := ( OrderInfoXchg_ι_client_addr ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.order_finish_time' " := ( OrderInfoXchg_ι_order_finish_time ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderInfoXchg.order_finish_time' " := ( OrderInfoXchg_ι_order_finish_time ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.price_num' " := ( DetailsInfoXchg_ι_price_num ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.price_num' " := ( DetailsInfoXchg_ι_price_num ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.price_denum' " := ( DetailsInfoXchg_ι_price_denum ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.price_denum' " := ( DetailsInfoXchg_ι_price_denum ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.min_amount' " := ( DetailsInfoXchg_ι_min_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.min_amount' " := ( DetailsInfoXchg_ι_min_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.sell_amount' " := ( DetailsInfoXchg_ι_sell_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.sell_amount' " := ( DetailsInfoXchg_ι_sell_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.buy_amount' " := ( DetailsInfoXchg_ι_buy_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DetailsInfoXchg.buy_amount' " := ( DetailsInfoXchg_ι_buy_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.transfer_tip3' " := ( TonsConfig_ι_transfer_tip3 ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.transfer_tip3' " := ( TonsConfig_ι_transfer_tip3 ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( TonsConfig_ι_return_ownership ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( TonsConfig_ι_return_ownership ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( TonsConfig_ι_trading_pair_deploy ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( TonsConfig_ι_trading_pair_deploy ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.order_answer' " := ( TonsConfig_ι_order_answer ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.order_answer' " := ( TonsConfig_ι_order_answer ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.process_queue' " := ( TonsConfig_ι_process_queue ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.process_queue' " := ( TonsConfig_ι_process_queue ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.send_notify' " := ( TonsConfig_ι_send_notify ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.send_notify' " := ( TonsConfig_ι_send_notify ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition price__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType price_ ) : ULValue RationalPriceLRecord ) . 
 Definition price__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType price_ ) : URValue RationalPriceLRecord false ) . 
 Notation " '_price_' " := ( price__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_price_' " := ( price__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition sells_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType sells_amount_ ) : ULValue XInteger128 ) . 
 Definition sells_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType sells_amount_ ) : URValue XInteger128 false ) . 
 Notation " '_sells_amount_' " := ( sells_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_sells_amount_' " := ( sells_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition buys_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType buys_amount_ ) : ULValue XInteger128 ) . 
 Definition buys_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType buys_amount_ ) : URValue XInteger128 false ) . 
 Notation " '_buys_amount_' " := ( buys_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_buys_amount_' " := ( buys_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : ULValue addr_std_fixedLRecord ) . 
 Definition flex__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType flex_ ) : URValue addr_std_fixedLRecord false ) . 
 Notation " '_flex_' " := ( flex__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_' " := ( flex__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition min_amount__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType min_amount_ ) : ULValue XInteger128 ) . 
 Definition min_amount__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType min_amount_ ) : URValue XInteger128 false ) . 
 Notation " '_min_amount_' " := ( min_amount__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_min_amount_' " := ( min_amount__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition deals_limit__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : ULValue XInteger8 ) . 
 Definition deals_limit__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : URValue XInteger8 false ) . 
 Notation " '_deals_limit_' " := ( deals_limit__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_deals_limit_' " := ( deals_limit__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition notify_addr__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType notify_addr_ ) : ULValue XAddress (* IFlexNotifyPtrLRecord *) ) . 
 Definition notify_addr__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType notify_addr_ ) : URValue XAddress (* IFlexNotifyPtrLRecord *) false ) . 
 Notation " '_notify_addr_' " := ( notify_addr__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_notify_addr_' " := ( notify_addr__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : ULValue XInteger8 ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType workchain_id_ ) : URValue XInteger8 false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tons_cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : ULValue TonsConfigLRecord ) . 
 Definition tons_cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : URValue TonsConfigLRecord false ) . 
 Notation " '_tons_cfg_' " := ( tons_cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tons_cfg_' " := ( tons_cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tip3_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tip3_code_ ) : ULValue XCell ) . 
 Definition tip3_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tip3_code_ ) : URValue XCell false ) . 
 Notation " '_tip3_code_' " := ( tip3_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tip3_code_' " := ( tip3_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition major_tip3cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType major_tip3cfg_ ) : ULValue Tip3ConfigLRecord ) . 
 Definition major_tip3cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType major_tip3cfg_ ) : URValue Tip3ConfigLRecord false ) . 
 Notation " '_major_tip3cfg_' " := ( major_tip3cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_major_tip3cfg_' " := ( major_tip3cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition minor_tip3cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType minor_tip3cfg_ ) : ULValue Tip3ConfigLRecord ) . 
 Definition minor_tip3cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType minor_tip3cfg_ ) : URValue Tip3ConfigLRecord false ) . 
 Notation " '_minor_tip3cfg_' " := ( minor_tip3cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_minor_tip3cfg_' " := ( minor_tip3cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition sells__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType sells_ ) : ULValue ( XQueue OrderInfoXchgLRecord ) ) . 
 Definition sells__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType sells_ ) : URValue ( XQueue OrderInfoXchgLRecord ) false ) . 
 Notation " '_sells_' " := ( sells__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_sells_' " := ( sells__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition buys__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType buys_ ) : ULValue ( XQueue OrderInfoXchgLRecord ) ) . 
 Definition buys__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType buys_ ) : URValue ( XQueue OrderInfoXchgLRecord ) false ) . 
 Notation " '_buys_' " := ( buys__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_buys_' " := ( buys__right ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.tip3root_sell_' " := ( dealer_ι_tip3root_sell_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.tip3root_sell_' " := ( dealer_ι_tip3root_sell_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.tip3root_buy_' " := ( dealer_ι_tip3root_buy_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.tip3root_buy_' " := ( dealer_ι_tip3root_buy_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.notify_addr_' " := ( dealer_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.notify_addr_' " := ( dealer_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.price_' " := ( dealer_ι_price_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.price_' " := ( dealer_ι_price_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.deals_limit_' " := ( dealer_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.deals_limit_' " := ( dealer_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.tons_cfg_' " := ( dealer_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.tons_cfg_' " := ( dealer_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.sells_amount_' " := ( dealer_ι_sells_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.sells_amount_' " := ( dealer_ι_sells_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.sells_' " := ( dealer_ι_sells_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.sells_' " := ( dealer_ι_sells_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.buys_amount_' " := ( dealer_ι_buys_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.buys_amount_' " := ( dealer_ι_buys_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.buys_' " := ( dealer_ι_buys_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.buys_' " := ( dealer_ι_buys_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'dealer.ret_' " := ( dealer_ι_ret_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'dealer.ret_' " := ( dealer_ι_ret_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.err_code' " := ( OrderRet_ι_err_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.err_code' " := ( OrderRet_ι_err_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.processed' " := ( OrderRet_ι_processed ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.processed' " := ( OrderRet_ι_processed ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.enqueued' " := ( OrderRet_ι_enqueued ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'OrderRet.enqueued' " := ( OrderRet_ι_enqueued ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.sells_amount' " := ( process_ret_ι_sells_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.sells_amount' " := ( process_ret_ι_sells_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.sells_' " := ( process_ret_ι_sells_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.sells_' " := ( process_ret_ι_sells_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.buys_amount' " := ( process_ret_ι_buys_amount ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.buys_amount' " := ( process_ret_ι_buys_amount ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.buys_' " := ( process_ret_ι_buys_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.buys_' " := ( process_ret_ι_buys_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'process_ret.ret_' " := ( process_ret_ι_ret_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'process_ret.ret_' " := ( process_ret_ι_ret_ ) (in custom URValue at level 0) : ursus_scope. 

Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

(**************************************************************************************************)
Notation "'λ2LL'" := (@UExpression_Next_LedgerableWithLArgs _ _ _ _ _( @UExpression_Next_LedgerableWithLArgs _ _ _ _ _ λ0)) (at level 0) : ursus_scope.

Definition make_deal_right  
( sell : ULValue ( OrderInfoXchgLRecord ) ) 
( buy : ULValue ( OrderInfoXchgLRecord ) ) 
: URValue ( XBool # (XBool # XInteger128) ) 
false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2LL ) make_deal 
 sell buy ) . 
 
 Notation " 'make_deal_' '(' sell buy ')' " := 
 ( make_deal_right 
 sell buy ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , buy custom URValue at level 0 ) : ursus_scope . 

 (* Definition extract_active_order_right { a2 a3 a4 a5 }  
( cur_order : URValue ( XMaybe (XInteger # OrderInfoXchgLRecord ) ) a2 ) 
( orders : URValue ( XQueue OrderInfoXchgLRecord ) a3 ) 
( all_amount : URValue ( XInteger128 ) a4 ) 
( sell : URValue ( XBool ) a5 ) 
: URValue ( (XMaybe ( XInteger # OrderInfoXchgLRecord )) # ( (XQueue OrderInfoXchgLRecord) # XInteger128 ) ) false . 
 ( orb ( orb ( orb a5 a4 ) a3 ) a2 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) extract_active_order 
 unsigned cur_order orders all_amount sell ) . 
 
 Notation " 'extract_active_order_' '(' unsigned cur_order orders all_amount sell ')' " := 
 ( extract_active_order_right 
 unsigned cur_order orders all_amount sell ) 
 (in custom URValue at level 0 , unsigned custom URValue at level 0 
 , cur_order custom URValue at level 0 
 , orders custom URValue at level 0 
 , all_amount custom URValue at level 0 
 , sell custom URValue at level 0 ) : ursus_scope .  *)
 
 Definition process_queue_left { R a1 a2 }  ( sell_idx : URValue ( XInteger ) a1 ) ( buy_idx : URValue ( XInteger ) a2 ) : UExpression R ( orb a2 a1 ) := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) process_queue 
 sell_idx buy_idx ) . 
 
 Notation " 'process_queue_' '(' sell_idx buy_idx ')' " := 
 ( process_queue_left 
 sell_idx buy_idx ) 
 (in custom ULValue at level 0 , sell_idx custom URValue at level 0 
 , buy_idx custom URValue at level 0 ) : ursus_scope . 
 Definition onTip3LendOwnership_right { a1 a2 a3 a4 a5 a6 }  ( answer_addr : URValue ( XAddress ) a1 ) ( balance : URValue ( XInteger128 ) a2 ) ( lend_finish_time : URValue ( XInteger32 ) a3 ) ( pubkey : URValue ( XInteger256 ) a4 ) ( internal_owner : URValue ( XAddress ) a5 ) ( payload : URValue ( XCell ) a6 ) : URValue OrderRetLRecord ( orb ( orb ( orb ( orb ( orb a6 a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) onTip3LendOwnership 
 answer_addr balance lend_finish_time pubkey internal_owner payload ) . 
 
 Notation " 'onTip3LendOwnership_' '(' answer_addr balance lend_finish_time pubkey internal_owner payload ')' " := 
 ( onTip3LendOwnership_right 
 answer_addr balance lend_finish_time pubkey internal_owner payload ) 
 (in custom URValue at level 0 , answer_addr custom URValue at level 0 
 , balance custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope .
 
 Definition processQueue_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) processQueue 
 ) . 
 
 Notation " 'processQueue_' '(' ')' " := 
 ( processQueue_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition cancelSell_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) cancelSell 
 ) . 
 
 Notation " 'cancelSell_' '(' ')' " := 
 ( cancelSell_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
 Definition cancelBuy_left { R }  : UExpression R false := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) cancelBuy 
 ) . 
 
 Notation " 'cancelBuy_' '(' ')' " := 
 ( cancelBuy_left 
 ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 Definition getDetails_right  : URValue DetailsInfoXchgLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDetails 
 ) . 
 
 Notation " 'getDetails_' '(' ')' " := 
 ( getDetails_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getPriceNum_right  : URValue XInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPriceNum 
 ) . 
 
 Notation " 'getPriceNum_' '(' ')' " := 
 ( getPriceNum_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getPriceDenum_right  : URValue XInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getPriceDenum 
 ) . 
 
 Notation " 'getPriceDenum_' '(' ')' " := 
 ( getPriceDenum_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getMinimumAmount_right  : URValue XInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getMinimumAmount 
 ) . 
 
 Notation " 'getMinimumAmount_' '(' ')' " := 
 ( getMinimumAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getTonsCfg_right  : URValue TonsConfigLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTonsCfg 
 ) . 
 
 Notation " 'getTonsCfg_' '(' ')' " := 
 ( getTonsCfg_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getSells_right  : URValue ( XHMap XInteger OrderInfoXchgLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSells 
 ) . 
 
 Notation " 'getSells_' '(' ')' " := 
 ( getSells_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope .
 
 Definition getBuys_right  : URValue ( XHMap XInteger OrderInfoXchgLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuys 
 ) . 
 
 Notation " 'getBuys_' '(' ')' " := 
 ( getBuys_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getSellAmount_right  : URValue XInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSellAmount 
 ) . 
 
 Notation " 'getSellAmount_' '(' ')' " := 
 ( getSellAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getBuyAmount_right  : URValue XInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBuyAmount 
 ) . 
 
 Notation " 'getBuyAmount_' '(' ')' " := 
 ( getBuyAmount_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope .
 
 Definition _fallback_right { a1 a2 }  
( x : URValue XCell a1 )
( y : URValue XSlice a2 ) 
: URValue XInteger (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 x y ) . 
 
 Notation " '_fallback_' '(' x ',' y ')' " := 
 ( _fallback_right x y ) 
 (in custom URValue at level 0 , x custom URValue at level 0, y custom URValue at level 0 ) : ursus_scope . 

 Definition onTip3LendOwnershipMinValue_right  : URValue XInteger128 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) onTip3LendOwnershipMinValue 
 ) . 
 
 Notation " 'onTip3LendOwnershipMinValue_' '(' ')' " := 
 ( onTip3LendOwnershipMinValue_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition verify_tip3_addr_right { a1 a2 a3 a4 }  ( cfg : URValue ( Tip3ConfigLRecord ) a1 ) ( tip3_wallet : URValue ( XAddress ) a2 ) ( wallet_pubkey : URValue ( XInteger256 ) a3 ) ( internal_owner : URValue ( XInteger256 ) a4 ) : URValue XBool ( orb ( orb ( orb a4 a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) verify_tip3_addr 
 cfg tip3_wallet wallet_pubkey internal_owner ) . 
 
 Notation " 'verify_tip3_addr_' '(' cfg tip3_wallet wallet_pubkey internal_owner ')' " := 
 ( verify_tip3_addr_right 
 cfg tip3_wallet wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 
 , tip3_wallet custom URValue at level 0 
 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope . 

 Definition expected_wallet_address_right { a1 a2 a3 }  ( cfg : URValue ( Tip3ConfigLRecord ) a1 ) ( wallet_pubkey : URValue ( XInteger256 ) a2 ) ( internal_owner : URValue ( XInteger256 ) a3 ) : URValue XInteger256 ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) expected_wallet_address 
 cfg wallet_pubkey internal_owner ) . 
 
 Notation " 'expected_wallet_address_' '(' cfg wallet_pubkey internal_owner ')' " := 
 ( expected_wallet_address_right 
 cfg wallet_pubkey internal_owner ) 
 (in custom URValue at level 0 , cfg custom URValue at level 0 
 , wallet_pubkey custom URValue at level 0 
 , internal_owner custom URValue at level 0 ) : ursus_scope .

 Definition on_ord_fail_right { a1 a2 a3 }  ( ec : URValue ( XInteger ) a1 ) ( wallet_in : URValue ( XAddress (* ITONTokenWalletPtrLRecord *) ) a2 ) ( amount : URValue ( XInteger128 ) a3 ) : URValue OrderRetLRecord ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) on_ord_fail 
 ec wallet_in amount ) . 
 
 Notation " 'on_ord_fail_' '(' ec wallet_in amount ')' " := 
 ( on_ord_fail_right 
 ec wallet_in amount ) 
 (in custom URValue at level 0 , ec custom URValue at level 0 
 , wallet_in custom URValue at level 0 
 , amount custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_price_xchg_state_init_and_addr_right { a1 a2 }  ( price_data : URValue ( ContractLRecord ) a1 ) ( price_code : URValue ( XCell ) a2 ) : URValue ( StateInitLRecord # XInteger256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_price_xchg_state_init_and_addr 
 price_data price_code ) . 
 
 Notation " 'prepare_price_xchg_state_init_and_addr_' '(' price_data price_code ')' " := 
 ( prepare_price_xchg_state_init_and_addr_right 
 price_data price_code ) 
 (in custom URValue at level 0 , price_data custom URValue at level 0 
 , price_code custom URValue at level 0 ) : ursus_scope . 

 Definition is_active_time_right { a1 }  ( order_finish_time : URValue ( XInteger32 ) a1 ) : URValue XBool a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) is_active_time 
 order_finish_time ) . 
 
 Notation " 'is_active_time_' '(' order_finish_time ')' " := 
 ( is_active_time_right 
 order_finish_time ) 
 (in custom URValue at level 0 , order_finish_time custom URValue at level 0 ) : ursus_scope .

 Definition minor_cost_right { a1 a2 }  ( amount : URValue ( XInteger128 ) a1 ) ( price : URValue ( RationalPriceLRecord ) a2 ) : URValue (XMaybe XInteger128) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) minor_cost 
 amount price ) . 
 
 Notation " 'minor_cost_' '(' amount price ')' " := 
 ( minor_cost_right 
 amount price ) 
 (in custom URValue at level 0 , amount custom URValue at level 0 
 , price custom URValue at level 0 ) : ursus_scope . 

 Definition process_queue_impl_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 }  
( tip3root_sell : URValue ( XAddress ) a1 ) 
( tip3root_buy : URValue ( XAddress ) a2 ) 
( notify_addr : URValue ( XAddress (* IFlexNotifyPtrLRecord *) ) a3 ) 
( price : URValue ( RationalPriceLRecord ) a4 ) 
( deals_limit : URValue ( XInteger8 ) a5 ) 
( tons_cfg : URValue ( TonsConfigLRecord ) a6 ) 
( sell_idx : URValue ( XInteger ) a7 ) 
( buy_idx : URValue ( XInteger ) a8 ) 
( sells_amount : URValue ( XInteger128 ) a9 ) 
( sells : URValue ( XQueue OrderInfoXchgLRecord ) a10 ) 
( buys_amount : URValue ( XInteger128 ) a11 ) 
( buys : URValue ( XQueue OrderInfoXchgLRecord ) a12 ) 
: URValue process_retLRecord 
( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a12 a11 ) a10 ) a9 ) a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) 
:= 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ12 ) process_queue_impl 
 tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ) . 
 
 Notation " 'process_queue_impl_' '(' tip3root_sell tip3root_buy notify_addr price deals_limit tons_cfg sell_idx buy_idx sells_amount sells buys_amount buys ')' " := 
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

 Definition cancel_order_impl_right { a1 a2 a3 a4 a5 a6 a7 }  
( orders : URValue ( XQueue OrderInfoXchgLRecord ) a1 ) 
( client_addr : URValue ( addr_std_fixedLRecord ) a2 ) 
( all_amount : URValue ( XInteger128 ) a3 ) 
( sell : URValue ( XBool ) a4 ) 
( return_ownership : URValue ( XInteger (* Grams *) ) a5 ) 
( process_queue : URValue ( XInteger (* Grams *) ) a6 ) 
( incoming_val : URValue ( XInteger (* Grams *) ) a7 ) 
: URValue ((XQueue OrderInfoXchgLRecord) # XInteger128) 
( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancel_order_impl 
 orders client_addr all_amount sell return_ownership process_queue incoming_val ) . 
 
 Notation " 'cancel_order_impl_' '(' orders client_addr all_amount sell return_ownership process_queue incoming_val ')' " := 
 ( cancel_order_impl_right 
 orders client_addr all_amount sell return_ownership process_queue incoming_val ) 
 (in custom URValue at level 0 , orders custom URValue at level 0 
 , client_addr custom URValue at level 0 
 , all_amount custom URValue at level 0 
 , sell custom URValue at level 0 
 , return_ownership custom URValue at level 0 
 , process_queue custom URValue at level 0 
 , incoming_val custom URValue at level 0 ) : ursus_scope .
 
 Definition int_sender_and_value_right  : URValue ( XAddress # XInteger (* Grams *) ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) int_sender_and_value 
 ) . 
 
 Notation " 'int_sender_and_value_' '(' ')' " := 
 ( int_sender_and_value_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

End Calls. 

End FuncNotations.

