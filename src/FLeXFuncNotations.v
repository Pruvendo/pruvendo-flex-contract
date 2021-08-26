Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 
Require Import Coq.Lists.List.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.StateMonad21. 
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.ProofEnvironment2.
Require Import UMLang.SML_NG25.

Require Import FLeXContractTypes.
Require Import FLeXClassSelf.
Require Import FLeXSpecSelf.
Require Import FLeXConstSig. 
Require Import stdFunc.

Module FLeXFuncNotations (xt: XTypesSig) 
                          (sm: StateMonadSig) 
                          (dc : FLeXConstsTypesSig xt sm ).
Export dc. Export xt. Export sm.

Module Export specFlexSpec := specFlexSpec xt sm.
Locate ursus_call_with_args.
Locate UrsusNotations.
Import ListNotations.
Import UrsusNotations.

Local Open Scope record. 
Local Open Scope solidity_scope. 
Local Open Scope ursus_scope. 
Local Open Scope string_scope.
Local Open Scope program_scope. 

Import ListNotations.


Notation " 'TonsConfig.transfer_tip3' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.order_answer' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.process_queue' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.send_notify' " := ( ULState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom ULValue at level 0) : ursus_scope. 


Notation " 'FLeX.deployer_pubkey_' " := ( ULState (U:= FLeX ) FLeX_ι_deployer_pubkey_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.tons_cfg_' " := ( ULState (U:= FLeX ) FLeX_ι_tons_cfg_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.pair_code_' " := ( ULState (U:= FLeX ) FLeX_ι_pair_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.xchg_pair_code_' " := ( ULState (U:= FLeX ) FLeX_ι_xchg_pair_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.price_code_' " := ( ULState (U:= FLeX ) FLeX_ι_price_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.xchg_price_code_' " := ( ULState (U:= FLeX ) FLeX_ι_xchg_price_code_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.min_amount_' " := ( ULState (U:= FLeX ) FLeX_ι_min_amount_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.deals_limit_' " := ( ULState (U:= FLeX ) FLeX_ι_deals_limit_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FLeX.notify_addr_' " := ( ULState (U:= FLeX ) FLeX_ι_notify_addr_ ) (in custom ULValue at level 0) : ursus_scope. 

 Notation " 'TradingPair.flex_addr_' " := ( ULState (U:= TradingPair ) TradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( ULState (U:= TradingPair ) TradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( ULState (U:= TradingPair ) TradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 

Notation " 'XchgPair.flex_addr_' " := ( ULState (U:= XchgPair ) XchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_major_root_' " := ( ULState (U:= XchgPair ) XchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_minor_root_' " := ( ULState (U:= XchgPair ) XchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.deploy_value_' " := ( ULState (U:= XchgPair ) XchgPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 


Notation " 'TonsConfig.transfer_tip3' " := ( URState (U:= TonsConfig ) TonsConfig_ι_transfer_tip3 ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.return_ownership' " := ( URState (U:= TonsConfig ) TonsConfig_ι_return_ownership ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.trading_pair_deploy' " := ( URState (U:= TonsConfig ) TonsConfig_ι_trading_pair_deploy ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.order_answer' " := ( URState (U:= TonsConfig ) TonsConfig_ι_order_answer ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.process_queue' " := ( URState (U:= TonsConfig ) TonsConfig_ι_process_queue ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TonsConfig.send_notify' " := ( URState (U:= TonsConfig ) TonsConfig_ι_send_notify ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'FLeX.deployer_pubkey_' " := ( URState (U:= FLeX ) FLeX_ι_deployer_pubkey_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.tons_cfg_' " := ( URState (U:= FLeX ) FLeX_ι_tons_cfg_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.pair_code_' " := ( URState (U:= FLeX ) FLeX_ι_pair_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.xchg_pair_code_' " := ( URState (U:= FLeX ) FLeX_ι_xchg_pair_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.price_code_' " := ( URState (U:= FLeX ) FLeX_ι_price_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.xchg_price_code_' " := ( URState (U:= FLeX ) FLeX_ι_xchg_price_code_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.min_amount_' " := ( URState (U:= FLeX ) FLeX_ι_min_amount_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.deals_limit_' " := ( URState (U:= FLeX ) FLeX_ι_deals_limit_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FLeX.notify_addr_' " := ( URState (U:= FLeX ) FLeX_ι_notify_addr_ ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'TradingPair.flex_addr_' " := ( URState (U:= TradingPair ) TradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.tip3_root_' " := ( URState (U:= TradingPair ) TradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TradingPair.deploy_value_' " := ( URState (U:= TradingPair ) TradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 

Notation " 'XchgPair.flex_addr_' " := ( URState (U:= XchgPair ) XchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_major_root_' " := ( URState (U:= XchgPair ) XchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.tip3_minor_root_' " := ( URState (U:= XchgPair ) XchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'XchgPair.deploy_value_' " := ( URState (U:= XchgPair ) XchgPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 


Notation " 'TIMESTAMP_DELAY' " := (sInject TIMESTAMP_DELAY) (in custom URValue at level 0) : ursus_scope.
Notation " 'error_code::message_sender_is_not_my_owner' " := (sInject error_code_ι_message_sender_is_not_my_owner) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::sender_is_not_deployer' " := (sInject error_code_ι_sender_is_not_deployer) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::unexpected_refs_count_in_code' " := (sInject error_code_ι_unexpected_refs_count_in_code) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::cant_override_code' " := (sInject error_code_ι_cant_override_code) (in custom URValue at level 0) : ursus_scope. 

Notation " 'ok' " := (sInject ok) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::out_of_tons' " := (sInject error_code_ι_out_of_tons) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::deals_limit' " := (sInject error_code_ι_deals_limit) (in custom URValue at level 0) : ursus_scope.
Notation " 'error_code::not_enough_tons_to_process' " := (sInject error_code_ι_not_enough_tons_to_process) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::not_enough_tokens_amount' " := (sInject error_code_ι_not_enough_tokens_amount) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::too_big_tokens_amount' " := (sInject error_code_ι_too_big_tokens_amount) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::different_workchain_id' " := (sInject error_code_ι_different_workchain_id) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::unverified_tip3_wallet' " := (sInject error_code_ι_unverified_tip3_wallet) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::canceled' " := (sInject error_code_ι_canceled) (in custom URValue at level 0) : ursus_scope. 
Notation " 'error_code::expired' " := (sInject error_code_ι_expired) (in custom URValue at level 0) : ursus_scope. 
Notation " 'safe_delay_period' " := (sInject safe_delay_period) (in custom URValue at level 0) : ursus_scope. 

Notation " 'error_code::not_enough_tons' " := (sInject error_code_ι_not_enough_tons) (in custom URValue at level 0) : ursus_scope. 

End FLeXFuncNotations.
