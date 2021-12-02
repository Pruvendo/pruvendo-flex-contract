
Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import ZArith.

Require Import FinProof.Common.
Require Import FinProof.ProgrammingWith.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.

Require Import CommonAxioms.
Require Import Contracts.FlexClient.Ledger.
Require Import Contracts.FlexClient.Functions.FuncSig.
Require Import Contracts.FlexClient.ClassTypes.
(* Require Import Contracts.Wrapper.ClassTypes. *)

(* здесь инмпортируем все внешние интерфейсы *)
Require Import Contracts.TradingPair.Interface.
Require Import Contracts.XchgPair.Interface.
Require Import Contracts.Price.Interface.
Require Import Contracts.TONTokenWallet.Interface.
Require Import Contracts.PriceXchg.Interface.
Require Import Contracts.Flex.Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module TradingPairPublicInterfaceModule := Contracts.TradingPair.Interface.PublicInterface xt sm.
Module XchgPairPublicInterface    := Contracts.XchgPair.Interface.PublicInterface xt sm.
Module PricePublicInterface       := Contracts.Price.Interface.PublicInterface xt sm.
Module TokenWalletPublicInterface := Contracts.TONTokenWallet.Interface.PublicInterface xt sm.
Module PriceXchgPublicInterface   := Contracts.PriceXchg.Interface.PublicInterface xt sm.
Module FlexPublicInterface        := Contracts.Flex.Interface.PublicInterface xt sm.
Module FlexClientPublicInterface  := Contracts.FlexClient.Interface.PublicInterface xt sm.
Module TradingPairClassTypesModule     := TradingPair.ClassTypes.ClassTypes xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.

Module FlexClientClassModule      := Contracts.FlexClient.ClassTypes.ClassTypes xt sm. 


Import xt.

Import UrsusNotations.
Local Open Scope ucpp_scope.
Local Open Scope ursus_scope.

Definition ITradingPairPtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_ITradingPair ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage TradingPairPublicInterfaceModule.ITradingPair )) )) . 
Definition ITradingPairPtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_ITradingPair ) : 
                                   URValue ( mapping address (queue (OutgoingMessage TradingPairPublicInterfaceModule.ITradingPair ))) false) . 
Notation " 'ITradingPairPtr' " := ( ITradingPairPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

Definition IXchgPairPtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IXchgPair ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage XchgPairPublicInterface.IXchgPair )) )) . 
Definition IXchgPairPtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IXchgPair ) : 
                                   URValue ( mapping address (queue (OutgoingMessage XchgPairPublicInterface.IXchgPair ))) false) . 
Notation " 'IXchgPairPtr' " := ( IXchgPairPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope. 

Definition ITONTokenWalletPtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_ITONTokenWallet ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage TokenWalletPublicInterface.ITONTokenWallet )) )) . 
Definition ITONTokenWalletPtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_ITONTokenWallet ) : 
                                   URValue ( mapping address (queue (OutgoingMessage TokenWalletPublicInterface.ITONTokenWallet ))) false) . 
Notation " 'ITONTokenWalletPtr' " := ( ITONTokenWalletPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

Definition PriceXchgPtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IPriceXchg ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage PriceXchgPublicInterface.IPriceXchg )) )) . 
Definition PriceXchgPtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IPriceXchg ) : 
                                   URValue ( mapping address (queue (OutgoingMessage PriceXchgPublicInterface.IPriceXchg ))) false) . 
Notation " 'IPriceXchgPtr' " := ( PriceXchgPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.

Definition IFlexPtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IFlex ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage FlexPublicInterface.IFlex )) )) . 
Definition IFlexPtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IFlex ) : 
                                   URValue ( mapping address (queue (OutgoingMessage FlexPublicInterface.IFlex ))) false) . 
Notation " 'IFlexPtr' " := ( IFlexPtr_messages_left ) (in custom ULValue at level 0) : ursus_scope. 

Definition PricePtr_messages_left := ( ULState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IPrice ) : 
                                   ULValue ( mapping address (queue (OutgoingMessage PricePublicInterface.IPrice )) )) . 
Definition PricePtr_messages_right := ( URState (f:=_MessagesAndEvents) (H:=MessagesAndEventsLEmbeddedType _OutgoingMessages_IPrice ) : 
                                   URValue ( mapping address (queue (OutgoingMessage PricePublicInterface.IPrice ))) false) . 
Notation " 'IPricePtr' " := ( PricePtr_messages_left ) (in custom ULValue at level 0) : ursus_scope.


 Definition owner__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_owner_ ) : ULValue uint256 ) . 
 Definition owner__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_owner_ ) : URValue uint256 false ) . 
 Notation " '_owner_' " := ( owner__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_owner_' " := ( owner__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition trading_pair_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_trading_pair_code_ ) : ULValue cell ) . 
 Definition trading_pair_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_trading_pair_code_ ) : URValue cell false ) . 
 Notation " '_trading_pair_code_' " := ( trading_pair_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_trading_pair_code_' " := ( trading_pair_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition xchg_pair_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_xchg_pair_code_ ) : ULValue cell ) . 
 Definition xchg_pair_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_xchg_pair_code_ ) : URValue cell false ) . 
 Notation " '_xchg_pair_code_' " := ( xchg_pair_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_xchg_pair_code_' " := ( xchg_pair_code__right ) (in custom URValue at level 0) : ursus_scope. 

 Definition workchain_id__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_workchain_id_ ) : ULValue int (* uint8 *) ) . 
 Definition workchain_id__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_workchain_id_ ) : URValue int (* uint8 *) false ) . 
 Notation " '_workchain_id_' " := ( workchain_id__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_workchain_id_' " := ( workchain_id__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tons_cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_tons_cfg_ ) : ULValue TonsConfigLRecord ) . 
 Definition tons_cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_tons_cfg_ ) : URValue TonsConfigLRecord false ) . 
 Notation " '_tons_cfg_' " := ( tons_cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tons_cfg_' " := ( tons_cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_flex_ ) : ULValue address ) . 
 Definition flex__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_flex_ ) : URValue address false ) . 
 Notation " '_flex_' " := ( flex__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_' " := ( flex__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition ext_wallet_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_ext_wallet_code_ ) : ULValue ( XMaybe cell ) ) . 
 Definition ext_wallet_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_ext_wallet_code_ ) : URValue ( XMaybe cell ) false ) . 
 Notation " '_ext_wallet_code_' " := ( ext_wallet_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_ext_wallet_code_' " := ( ext_wallet_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex_wallet_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_flex_wallet_code_ ) : ULValue ( XMaybe cell ) ) . 
 Definition flex_wallet_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_flex_wallet_code_ ) : URValue ( XMaybe cell ) false ) . 
 Notation " '_flex_wallet_code_' " := ( flex_wallet_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_wallet_code_' " := ( flex_wallet_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition flex_wrapper_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_flex_wrapper_code_ ) : ULValue ( XMaybe cell ) ) . 
 Definition flex_wrapper_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType DFlexClient_ι_flex_wrapper_code_ ) : URValue ( XMaybe cell ) false ) . 
 Notation " '_flex_wrapper_code_' " := ( flex_wrapper_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_flex_wrapper_code_' " := ( flex_wrapper_code__right ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_ext_wallet_code' " := (sInject missed_ext_wallet_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wallet_code' " := (sInject missed_flex_wallet_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::missed_flex_wrapper_code' " := (sInject missed_flex_wrapper_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::zero_owner_pubkey' " := (sInject zero_owner_pubkey) (in custom URValue at level 0) : ursus_scope. 

Notation " 'DEFAULT_MSG_FLAGS' " := (sInject DEFAULT_MSG_FLAGS) (in custom URValue at level 0) : ursus_scope.

Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.

 Definition constructor_left { R a1 a2 a3 }  ( pubkey : URValue ( uint256 ) a1 ) ( trading_pair_code : URValue cell a2 ) ( xchg_pair_code : URValue cell a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) constructor 
 pubkey trading_pair_code xchg_pair_code ) . 
 
 Notation " 'constructor_' '(' pubkey trading_pair_code xchg_pair_code ')' " := 
 ( constructor_left 
 pubkey trading_pair_code xchg_pair_code ) 
 (in custom ULValue at level 0 , pubkey custom URValue at level 0 
 , trading_pair_code custom URValue at level 0 
 , xchg_pair_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setFlexCfg_left { R a1 a2 }  ( tons_cfg : URValue ( TonsConfigLRecord ) a1 ) ( flex : URValue ( address ) a2 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) setFlexCfg 
 tons_cfg flex ) . 
 
 Notation " 'setFlexCfg_' '(' tons_cfg flex ')' " := 
 ( setFlexCfg_left 
 tons_cfg flex ) 
 (in custom ULValue at level 0 , tons_cfg custom URValue at level 0 
 , flex custom URValue at level 0 ) : ursus_scope . 
 
 Definition setExtWalletCode_left { R a1 }  ( ext_wallet_code : URValue cell a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setExtWalletCode 
 ext_wallet_code ) . 
 
 Notation " 'setExtWalletCode_' '(' ext_wallet_code ')' " := 
 ( setExtWalletCode_left 
 ext_wallet_code ) 
 (in custom ULValue at level 0 , ext_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setFlexWalletCode_left { R a1 }  ( flex_wallet_code : URValue cell a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setFlexWalletCode 
 flex_wallet_code ) . 
 
 Notation " 'setFlexWalletCode_' '(' flex_wallet_code ')' " := 
 ( setFlexWalletCode_left 
 flex_wallet_code ) 
 (in custom ULValue at level 0 , flex_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setFlexWrapperCode_left { R a1 }  ( flex_wrapper_code : URValue cell a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setFlexWrapperCode 
 flex_wrapper_code ) . 
 
 Notation " 'setFlexWrapperCode_' '(' flex_wrapper_code ')' " := 
 ( setFlexWrapperCode_left 
 flex_wrapper_code ) 
 (in custom ULValue at level 0 , flex_wrapper_code custom URValue at level 0 ) : ursus_scope . 
 Definition deployTradingPair_right { a1 a2 a3 a4 a5 }  ( tip3_root : URValue ( address ) a1 ) ( deploy_min_value : URValue ( uint128 ) a2 ) ( deploy_value : URValue ( uint128 ) a3 ) ( min_trade_amount : URValue ( uint128 ) a4 ) ( notify_addr : URValue ( address ) a5 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) deployTradingPair 
 tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ) . 
 
 Notation " 'deployTradingPair_' '(' tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ')' " := 
 ( deployTradingPair_right 
 tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition deployXchgPair_right { a1 a2 a3 a4 a5 a6 }  ( tip3_major_root : URValue ( address ) a1 ) ( tip3_minor_root : URValue ( address ) a2 ) ( deploy_min_value : URValue ( uint128 ) a3 ) ( deploy_value : URValue ( uint128 ) a4 ) ( min_trade_amount : URValue ( uint128 ) a5 ) ( notify_addr : URValue ( address ) a6 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) deployXchgPair 
 tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ) . 
 
 Notation " 'deployXchgPair_' '(' tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ')' " := 
 ( deployXchgPair_right 
 tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition deployPriceWithSell_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 }  ( price : URValue ( uint128 ) a1 ) ( amount : URValue ( uint128 ) a2 ) ( lend_finish_time : URValue ( uint32 ) a3 ) ( min_amount : URValue ( uint128 ) a4 ) ( deals_limit : URValue ( uint8 ) a5 ) ( tons_value : URValue ( uint128 ) a6 ) ( price_code : URValue cell a7 ) ( my_tip3_addr : URValue ( address ) a8 ) ( receive_wallet : URValue ( address ) a9 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a10 ) ( notify_addr : URValue ( address ) a11 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ11 ) deployPriceWithSell 
 price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceWithSell_' '(' price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ')' " := 
 ( deployPriceWithSell_right 
 price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , receive_wallet custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition deployPriceWithBuy_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  ( price : URValue ( uint128 ) a1 ) ( amount : URValue ( uint128 ) a2 ) ( order_finish_time : URValue ( uint32 ) a3 ) ( min_amount : URValue ( uint128 ) a4 ) ( deals_limit : URValue ( uint8 ) a5 ) ( deploy_value : URValue ( uint128 ) a6 ) ( price_code : URValue cell a7 ) ( my_tip3_addr : URValue ( address ) a8 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a9 ) ( notify_addr : URValue ( address ) a10 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ10 ) deployPriceWithBuy 
 price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceWithBuy_' '(' price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ')' " := 
 ( deployPriceWithBuy_right 
 price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 
 , order_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition cancelSellOrder_left { R a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue ( uint128 ) a1 ) ( min_amount : URValue ( uint128 ) a2 ) ( deals_limit : URValue ( uint8 ) a3 ) ( value : URValue ( uint128 ) a4 ) ( price_code : URValue cell a5 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) ( notify_addr : URValue ( address ) a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancelSellOrder 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) . 
 
 Notation " 'cancelSellOrder_' '(' price min_amount deals_limit value price_code tip3cfg notify_addr ')' " := 
 ( cancelSellOrder_left 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition cancelBuyOrder_left { R a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue ( uint128 ) a1 ) ( min_amount : URValue ( uint128 ) a2 ) ( deals_limit : URValue ( uint8 ) a3 ) ( value : URValue ( uint128 ) a4 ) ( price_code : URValue cell a5 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) ( notify_addr : URValue ( address ) a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancelBuyOrder 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) . 
 
 Notation " 'cancelBuyOrder_' '(' price min_amount deals_limit value price_code tip3cfg notify_addr ')' " := 
 ( cancelBuyOrder_left 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition cancelXchgOrder_left { R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  ( sell : URValue ( XBool ) a1 ) ( price_num : URValue ( uint128 ) a2 ) ( price_denum : URValue ( uint128 ) a3 ) ( min_amount : URValue ( uint128 ) a4 ) ( deals_limit : URValue ( uint8 ) a5 ) ( value : URValue ( uint128 ) a6 ) ( xchg_price_code : URValue cell a7 ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) a8 ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) a9 ) ( notify_addr : URValue ( address ) a10 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ10 ) cancelXchgOrder 
 sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ) . 
 
 Notation " 'cancelXchgOrder_' '(' sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ')' " := 
 ( cancelXchgOrder_left 
 sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , sell custom URValue at level 0 
 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , xchg_price_code custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_left { R a1 a2 a3 }  ( dest : URValue ( address ) a1 ) ( value : URValue ( uint128 ) a2 ) ( bounce : URValue ( XBool ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) transfer 
 dest value bounce ) . 
 
 Notation " 'transfer_' '(' dest value bounce ')' " := 
 ( transfer_left 
 dest value bounce ) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 
 , value custom URValue at level 0 
 , bounce custom URValue at level 0 ) : ursus_scope . 

 Definition deployPriceXchg_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 }  ( sell : URValue ( XBool ) a1 ) ( price_num : URValue ( uint128 ) a2 ) ( price_denum : URValue ( uint128 ) a3 ) ( amount : URValue ( uint128 ) a4 ) ( lend_amount : URValue ( uint128 ) a5 ) ( lend_finish_time : URValue ( uint32 ) a6 ) ( min_amount : URValue ( uint128 ) a7 ) ( deals_limit : URValue ( uint8 ) a8 ) ( tons_value : URValue ( uint128 ) a9 ) ( xchg_price_code : URValue cell a10 ) ( my_tip3_addr : URValue ( address ) a11 ) ( receive_wallet : URValue ( address ) a12 ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) a13 ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) a14 ) ( notify_addr : URValue ( address ) a15 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ15 ) deployPriceXchg 
 sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceXchg_' '(' sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ')' " := 
 ( deployPriceXchg_right 
 sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , amount custom URValue at level 0 
 , lend_amount custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_value custom URValue at level 0 
 , xchg_price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , receive_wallet custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition registerWrapper_left { R a1 a2 a3 }  ( wrapper_pubkey : URValue ( uint256 ) a1 ) ( value : URValue ( uint128 ) a2 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) registerWrapper 
 wrapper_pubkey value tip3cfg ) . 
 
 Notation " 'registerWrapper_' '(' wrapper_pubkey value tip3cfg ')' " := 
 ( registerWrapper_left 
 wrapper_pubkey value tip3cfg ) 
 (in custom ULValue at level 0 , wrapper_pubkey custom URValue at level 0 
 , value custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition registerTradingPair_left { R a1 a2 a3 a4 a5 }  ( request_pubkey : URValue ( uint256 ) a1 ) ( value : URValue ( uint128 ) a2 ) ( tip3_root : URValue ( address ) a3 ) ( min_amount : URValue ( uint128 ) a4 ) ( notify_addr : URValue ( address ) a5 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) registerTradingPair 
 request_pubkey value tip3_root min_amount notify_addr ) . 
 
 Notation " 'registerTradingPair_' '(' request_pubkey value tip3_root min_amount notify_addr ')' " := 
 ( registerTradingPair_left 
 request_pubkey value tip3_root min_amount notify_addr ) 
 (in custom ULValue at level 0 , request_pubkey custom URValue at level 0 
 , value custom URValue at level 0 
 , tip3_root custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition registerXchgPair_left { R a1 a2 a3 a4 a5 a6 }  ( request_pubkey : URValue ( uint256 ) a1 ) ( value : URValue ( uint128 ) a2 ) ( tip3_major_root : URValue ( address ) a3 ) ( tip3_minor_root : URValue ( address ) a4 ) ( min_amount : URValue ( uint128 ) a5 ) ( notify_addr : URValue ( address ) a6 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) registerXchgPair 
 request_pubkey value tip3_major_root tip3_minor_root min_amount notify_addr ) . 
 
 Notation " 'registerXchgPair_' '(' request_pubkey value tip3_major_root tip3_minor_root min_amount notify_addr ')' " := 
 ( registerXchgPair_left 
 request_pubkey value tip3_major_root tip3_minor_root min_amount notify_addr ) 
 (in custom ULValue at level 0 , request_pubkey custom URValue at level 0 
 , value custom URValue at level 0 
 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition deployEmptyFlexWallet_right { a1 a2 a3 }  ( pubkey : URValue ( uint256 ) a1 ) ( tons_to_wallet : URValue ( uint128 ) a2 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a3 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) deployEmptyFlexWallet 
 pubkey tons_to_wallet tip3cfg ) . 
 
 Notation " 'deployEmptyFlexWallet_' '(' pubkey tons_to_wallet tip3cfg ')' " := 
 ( deployEmptyFlexWallet_right 
 pubkey tons_to_wallet tip3cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , tons_to_wallet custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 
 
 Definition burnWallet_left { R a1 a2 a3 a4 }  ( tons_value : URValue ( uint128 ) a1 ) ( out_pubkey : URValue ( uint256 ) a2 ) ( out_internal_owner : URValue ( address ) a3 ) ( my_tip3_addr : URValue ( address ) a4 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) burnWallet 
 tons_value out_pubkey out_internal_owner my_tip3_addr ) . 
 
 Notation " 'burnWallet_' '(' tons_value out_pubkey out_internal_owner my_tip3_addr ')' " := 
 ( burnWallet_left 
 tons_value out_pubkey out_internal_owner my_tip3_addr ) 
 (in custom ULValue at level 0 , tons_value custom URValue at level 0 
 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 ) : ursus_scope . 
 Definition getOwner_right  : URValue uint256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwner 
 ) . 
 
 Notation " 'getOwner_' '(' ')' " := 
 ( getOwner_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getFlex_right  : URValue address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getFlex 
 ) . 
 
 Notation " 'getFlex_' '(' ')' " := 
 ( getFlex_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition hasExtWalletCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasExtWalletCode 
 ) . 
 
 Notation " 'hasExtWalletCode_' '(' ')' " := 
 ( hasExtWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition hasFlexWalletCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasFlexWalletCode 
 ) . 
 
 Notation " 'hasFlexWalletCode_' '(' ')' " := 
 ( hasFlexWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition hasFlexWrapperCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasFlexWrapperCode 
 ) . 
 
 Notation " 'hasFlexWrapperCode_' '(' ')' " := 
 ( hasFlexWrapperCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 Definition getPayloadForDeployInternalWallet_right { a1 a2 a3 }  ( owner_pubkey : URValue ( uint256 ) a1 ) ( owner_addr : URValue ( address ) a2 ) ( tons : URValue ( uint128 ) a3 ) : URValue cell ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) getPayloadForDeployInternalWallet 
 owner_pubkey owner_addr tons ) . 
 
 Notation " 'getPayloadForDeployInternalWallet_' '(' owner_pubkey owner_addr tons ')' " := 
 ( getPayloadForDeployInternalWallet_right 
 owner_pubkey owner_addr tons ) 
 (in custom URValue at level 0 , owner_pubkey custom URValue at level 0 
 , owner_addr custom URValue at level 0 
 , tons custom URValue at level 0 ) : ursus_scope . 
 Definition _fallback_right { a1 a2 }  ( msg : URValue cell a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue uint ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 msg msg_body ) . 
 
 Notation " '_fallback_' '(' msg msg_body ')' " := 
 ( _fallback_right 
 msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 

 Definition preparePrice_right { a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue ( uint128 ) a1 ) ( min_amount : URValue ( uint128 ) a2 ) ( deals_limit : URValue ( uint8 ) a3 ) ( tip3_code : URValue cell a4 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a5 ) ( price_code : URValue cell a6 ) ( notify_addr : URValue ( address ) a7 ) : URValue ( StateInitLRecord # ( address # uint256 ) ) ( orb ( orb ( orb ( orb ( orb ( orb a7 a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) preparePrice 
 price min_amount deals_limit tip3_code tip3cfg price_code notify_addr ) . 
 
 Notation " 'preparePrice_' '(' price min_amount deals_limit tip3_code tip3cfg price_code notify_addr ')' " := 
 ( preparePrice_right 
 price min_amount deals_limit tip3_code tip3cfg price_code notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tip3_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , price_code custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 Definition preparePriceXchg_right { a1 a2 a3 a4 a5 a6 a7 a8 }  ( price_num : URValue ( uint128 ) a1 ) ( price_denum : URValue ( uint128 ) a2 ) ( min_amount : URValue ( uint128 ) a3 ) ( deals_limit : URValue ( uint8 ) a4 ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) a5 ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) ( price_code : URValue cell a7 ) ( notify_addr : URValue ( address ) a8 ) : URValue ( StateInitLRecord # ( address # uint256 ) ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb a8 a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ8 ) preparePriceXchg 
 price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ) . 
 
 Notation " 'preparePriceXchg_' '(' price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ')' " := 
 ( preparePriceXchg_right 
 price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ) 
 (in custom URValue at level 0 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 
 , price_code custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

End Calls. 

End FuncNotations.
