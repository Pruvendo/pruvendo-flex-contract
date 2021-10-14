
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

Require Import Contracts.Flex.Ledger.
Require Import Contracts.Flex.Functions.FuncSig.

(* здесь инмпортируем все внешние интерфейсы *)
Require Import Interface.

Module FuncNotations (xt: XTypesSig) 
                     (sm: StateMonadSig) 
                     (dc : ConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

(* здесь модули из каждого внешнего интерфейса *)
Module FlexPublicInterface := PublicInterface xt sm.

Module Export SpecModuleForFuncNotations := Spec xt sm.

Check XQueue.
Import xt.

Import UrsusNotations.

Local Open Scope ursus_scope.

Notation " 'TonsConfig.transfer_tip3' " := (  TonsConfig_ι_transfer_tip3  ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.transfer_tip3' " := (  TonsConfig_ι_transfer_tip3  ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.return_ownership' " := (  TonsConfig_ι_return_ownership  ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.return_ownership' " := (  TonsConfig_ι_return_ownership  ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.trading_pair_deploy' " := (  TonsConfig_ι_trading_pair_deploy  ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.trading_pair_deploy' " := (  TonsConfig_ι_trading_pair_deploy  ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.order_answer' " := (  TonsConfig_ι_order_answer  ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.order_answer' " := (  TonsConfig_ι_order_answer  ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.process_queue' " := (  TonsConfig_ι_process_queue  ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.process_queue' " := (  TonsConfig_ι_process_queue  ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.send_notify' " := (  TonsConfig_ι_send_notify  ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'TonsConfig.send_notify' " := (  TonsConfig_ι_send_notify  ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexOwnershipInfo.deployer_pubkey' " := (  FlexOwnershipInfo_ι_deployer_pubkey  ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexOwnershipInfo.deployer_pubkey' " := (  FlexOwnershipInfo_ι_deployer_pubkey  ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexOwnershipInfo.ownership_description' " := (  FlexOwnershipInfo_ι_ownership_description  ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexOwnershipInfo.ownership_description' " := (  FlexOwnershipInfo_ι_ownership_description  ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'FlexOwnershipInfo.owner_contract' " := (  FlexOwnershipInfo_ι_owner_contract  ) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'FlexOwnershipInfo.owner_contract' " := (  FlexOwnershipInfo_ι_owner_contract  ) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DFlex.deployer_pubkey_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType deployer_pubkey_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DFlex.deployer_pubkey_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType deployer_pubkey_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DFlex.ownership_description_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType ownership_description_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DFlex.ownership_description_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType ownership_description_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DFlex.owner_address_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType owner_address_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DFlex.owner_address_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType owner_address_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DFlex.tons_cfg_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DFlex.tons_cfg_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DFlex.pair_code_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType pair_code_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DFlex.pair_code_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType pair_code_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DFlex.xchg_pair_code_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_code_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DFlex.xchg_pair_code_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_code_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DFlex.price_code_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType price_code_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DFlex.price_code_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType price_code_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DFlex.xchg_price_code_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType xchg_price_code_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DFlex.xchg_price_code_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType xchg_price_code_ )) (in custom URValue at level 0) : ursus_scope.
 Notation " 'DFlex.deals_limit_' " := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ )) (in custom ULValue at level 0) : ursus_scope.
 Notation " 'DFlex.deals_limit_' " := ( URState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ )) (in custom URValue at level 0) : ursus_scope.

 Definition constructor_call { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  ( deployer_pubkey : URValue XInteger256 a1 ) ( ownership_description : URValue XString a2 ) ( owner_address : URValue ( XMaybe XAddress ) a3 ) ( transfer_tip3 : URValue XInteger128 a4 ) ( return_ownership : URValue XInteger128 a5 ) ( trading_pair_deploy : URValue XInteger128 a6 ) ( order_answer : URValue XInteger128 a7 ) ( process_queue : URValue XInteger128 a8 ) ( send_notify : URValue XInteger128 a9 ) ( deals_limit : URValue XInteger8 a10 ) : LedgerT ( ControlResult PhantomType ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a10 a9 ) a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ10 ) constructor1 
 ( SimpleLedgerableArg URValue {{ Λ "deployer_pubkey" }} ( deployer_pubkey ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "ownership_description" }} ( ownership_description ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "owner_address" }} ( owner_address ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "transfer_tip3" }} ( transfer_tip3 ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "return_ownership" }} ( return_ownership ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "trading_pair_deploy" }} ( trading_pair_deploy ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "order_answer" }} ( order_answer ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "process_queue" }} ( process_queue ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "send_notify" }} ( send_notify ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "deals_limit" }} ( deals_limit ) ) 
 . 
 Notation " 'constructor_ref_' '(' deployer_pubkey ownership_description owner_address transfer_tip3 return_ownership trading_pair_deploy order_answer process_queue send_notify deals_limit ')' " := 
 ( FuncallExpression ( constructor_call 
 deployer_pubkey ownership_description owner_address transfer_tip3 return_ownership trading_pair_deploy order_answer process_queue send_notify deals_limit )) 
 (in custom ULValue at level 0 , deployer_pubkey custom URValue at level 0 
 , ownership_description custom ULValue at level 0 
 , owner_address custom ULValue at level 0 
 , transfer_tip3 custom ULValue at level 0 
 , return_ownership custom ULValue at level 0 
 , trading_pair_deploy custom ULValue at level 0 
 , order_answer custom ULValue at level 0 
 , process_queue custom ULValue at level 0 
 , send_notify custom ULValue at level 0 
 , deals_limit custom ULValue at level 0 ) : ursus_scope . 
 
 Definition setPairCode_call { a1 }  ( code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) setPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} ( code ) ) 
 . 
 Notation " 'setPairCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( setPairCode_call 
 code )) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setXchgPairCode_call { a1 }  ( code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) setXchgPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} ( code ) ) 
 . 
 Notation " 'setXchgPairCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( setXchgPairCode_call 
 code )) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setPriceCode_call { a1 }  ( code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) setPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} ( code ) ) 
 . 
 Notation " 'setPriceCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( setPriceCode_call 
 code )) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setXchgPriceCode_call { a1 }  ( code : URValue XCell a1 ) : LedgerT ( ControlResult PhantomType ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) setXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} ( code ) ) 
 . 
 Notation " 'setXchgPriceCode_ref_' '(' code ')' " := 
 ( FuncallExpression ( setXchgPriceCode_call 
 code )) 
 (in custom ULValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 
 Definition transfer_call { a1 a2 }  ( to : URValue XAddress a1 ) ( tons : URValue XInteger128 a2 ) : LedgerT ( ControlResult PhantomType ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) transfer 
 ( SimpleLedgerableArg URValue {{ Λ "to" }} ( to ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tons" }} ( tons ) ) 
 . 
 Notation " 'transfer_ref_' '(' to tons ')' " := 
 ( FuncallExpression ( transfer_call 
 to tons )) 
 (in custom ULValue at level 0 , to custom URValue at level 0 
 , tons custom ULValue at level 0 ) : ursus_scope . 
 
 Definition isFullyInitialized_call  : LedgerT ( ControlResult XBool false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) isFullyInitialized 
 . 
 Notation " 'isFullyInitialized_ref_' '(' ')' " := 
 ( URResult ( isFullyInitialized_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition getTonsCfg_call  : LedgerT ( ControlResult TonsConfigP false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) getTonsCfg 
 . 
 Notation " 'getTonsCfg_ref_' '(' ')' " := 
 ( URResult ( getTonsCfg_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition getTradingPairCode_call  : LedgerT ( ControlResult XCell false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) getTradingPairCode 
 . 
 Notation " 'getTradingPairCode_ref_' '(' ')' " := 
 ( URResult ( getTradingPairCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition getXchgPairCode_call  : LedgerT ( ControlResult XCell false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) getXchgPairCode 
 . 
 Notation " 'getXchgPairCode_ref_' '(' ')' " := 
 ( URResult ( getXchgPairCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition getSellPriceCode_call { a1 }  ( tip3_addr : URValue XAddress a1 ) : LedgerT ( ControlResult XCell false ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) getSellPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr" }} ( tip3_addr ) ) 
 . 
 Notation " 'getSellPriceCode_ref_' '(' tip3_addr ')' " := 
 ( URResult ( getSellPriceCode_call 
 tip3_addr )) 
 (in custom URValue at level 0 , tip3_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition getXchgPriceCode_call { a1 a2 }  ( tip3_addr1 : URValue XAddress a1 ) ( tip3_addr2 : URValue XAddress a2 ) : LedgerT ( ControlResult XCell false ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) getXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr1" }} ( tip3_addr1 ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr2" }} ( tip3_addr2 ) ) 
 . 
 Notation " 'getXchgPriceCode_ref_' '(' tip3_addr1 tip3_addr2 ')' " := 
 ( URResult ( getXchgPriceCode_call 
 tip3_addr1 tip3_addr2 )) 
 (in custom URValue at level 0 , tip3_addr1 custom URValue at level 0 
 , tip3_addr2 custom ULValue at level 0 ) : ursus_scope . 
 
 Definition getSellTradingPair_call { a1 }  ( tip3_root : URValue XAddress a1 ) : LedgerT ( ControlResult XAddress false ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) getSellTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_root" }} ( tip3_root ) ) 
 . 
 Notation " 'getSellTradingPair_ref_' '(' tip3_root ')' " := 
 ( URResult ( getSellTradingPair_call 
 tip3_root )) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 ) : ursus_scope . 
 
 Definition getXchgTradingPair_call { a1 a2 }  ( tip3_major_root : URValue XAddress a1 ) ( tip3_minor_root : URValue XAddress a2 ) : LedgerT ( ControlResult XAddress false ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) getXchgTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_major_root" }} ( tip3_major_root ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_minor_root" }} ( tip3_minor_root ) ) 
 . 
 Notation " 'getXchgTradingPair_ref_' '(' tip3_major_root tip3_minor_root ')' " := 
 ( URResult ( getXchgTradingPair_call 
 tip3_major_root tip3_minor_root )) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom ULValue at level 0 ) : ursus_scope . 
 
 Definition getDealsLimit_call  : LedgerT ( ControlResult XInteger8 false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) getDealsLimit 
 . 
 Notation " 'getDealsLimit_ref_' '(' ')' " := 
 ( URResult ( getDealsLimit_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition getOwnershipInfo_call  : LedgerT ( ControlResult FlexOwnershipInfoP false ( ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) getOwnershipInfo 
 . 
 Notation " 'getOwnershipInfo_ref_' '(' ')' " := 
 ( URResult ( getOwnershipInfo_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition _fallback_call { a1 }  ( cell : URValue (P a1 ) : LedgerT ( ControlResult XInteger false ( a1 ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) _fallback 
 ( SimpleLedgerableArg URValue {{ Λ "cell" }} ( cell ) ) 
 . 
 Notation " '_fallback_ref_' '(' cell ')' " := 
 ( URResult ( _fallback_call 
 cell )) 
 (in custom URValue at level 0 , cell custom URValue at level 0 ) : ursus_scope . 
 
 Definition Ф_prepare_flex_state_init_and_addr_call { a1 a2 }  ( flex_data : URValue DFlexP a1 ) ( flex_code : URValue XCell a2 ) : LedgerT ( ControlResult ( StateInitP # XInteger256 )%sol false ( orb a2 a1 ) ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_flex_state_init_and_addr 
 ( SimpleLedgerableArg URValue {{ Λ "flex_data" }} ( flex_data ) ) 
 ( SimpleLedgerableArg URValue {{ Λ "flex_code" }} ( flex_code ) ) 
 . 
 Notation " 'Ф_prepare_flex_state_init_and_addr_ref_' '(' flex_data flex_code ')' " := 
 ( URResult ( Ф_prepare_flex_state_init_and_addr_call 
 flex_data flex_code )) 
 (in custom URValue at level 0 , flex_data custom URValue at level 0 
 , flex_code custom ULValue at level 0 ) : ursus_scope . 

End Calls. 

End FuncNotations.
