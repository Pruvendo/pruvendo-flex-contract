
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


Import xt.

Import UrsusNotations.

Local Open Scope ursus_scope.


Notation " 'TickTock.tick' " := ( TickTock_ι_tick ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TickTock.tick' " := ( TickTock_ι_tick ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'TickTock.tock' " := ( TickTock_ι_tock ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'TickTock.tock' " := ( TickTock_ι_tock ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'anycast_info.rewrite_pfx' " := ( anycast_info_ι_rewrite_pfx ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'anycast_info.rewrite_pfx' " := ( anycast_info_ι_rewrite_pfx ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std.kind' " := ( addr_std_ι_kind ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std.kind' " := ( addr_std_ι_kind ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std.Anycast' " := ( addr_std_ι_Anycast ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std.Anycast' " := ( addr_std_ι_Anycast ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std.workchain_id' " := ( addr_std_ι_workchain_id ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std.workchain_id' " := ( addr_std_ι_workchain_id ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'addr_std.address' " := ( addr_std_ι_address ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'addr_std.address' " := ( addr_std_ι_address ) (in custom URValue at level 0) : ursus_scope. 
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
 Notation " 'FlexOwnershipInfo.deployer_pubkey' " := ( FlexOwnershipInfo_ι_deployer_pubkey ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.deployer_pubkey' " := ( FlexOwnershipInfo_ι_deployer_pubkey ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.ownership_description' " := ( FlexOwnershipInfo_ι_ownership_description ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.ownership_description' " := ( FlexOwnershipInfo_ι_ownership_description ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.owner_contract' " := ( FlexOwnershipInfo_ι_owner_contract ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'FlexOwnershipInfo.owner_contract' " := ( FlexOwnershipInfo_ι_owner_contract ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition deployer_pubkey__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType deployer_pubkey_ ) : ULValue XInteger256 ) . 
 Definition deployer_pubkey__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType deployer_pubkey_ ) : URValue XInteger256 false ) . 
 Notation " '_deployer_pubkey_' " := ( deployer_pubkey__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_deployer_pubkey_' " := ( deployer_pubkey__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition ownership_description__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType ownership_description_ ) : ULValue XString ) . 
 Definition ownership_description__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType ownership_description_ ) : URValue XString false ) . 
 Notation " '_ownership_description_' " := ( ownership_description__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_ownership_description_' " := ( ownership_description__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition owner_address__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType owner_address_ ) : ULValue ( XMaybe XAddress ) ) . 
 Definition owner_address__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType owner_address_ ) : URValue ( XMaybe XAddress ) false ) . 
 Notation " '_owner_address_' " := ( owner_address__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_owner_address_' " := ( owner_address__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition tons_cfg__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : ULValue TonsConfigLRecord ) . 
 Definition tons_cfg__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType tons_cfg_ ) : URValue TonsConfigLRecord false ) . 
 Notation " '_tons_cfg_' " := ( tons_cfg__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_tons_cfg_' " := ( tons_cfg__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition pair_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType pair_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition pair_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType pair_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_pair_code_' " := ( pair_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_pair_code_' " := ( pair_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition xchg_pair_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition xchg_pair_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType xchg_pair_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_xchg_pair_code_' " := ( xchg_pair_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_xchg_pair_code_' " := ( xchg_pair_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition price_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType price_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition price_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType price_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_price_code_' " := ( price_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_price_code_' " := ( price_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition xchg_price_code__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType xchg_price_code_ ) : ULValue ( XMaybe XCell ) ) . 
 Definition xchg_price_code__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType xchg_price_code_ ) : URValue ( XMaybe XCell ) false ) . 
 Notation " '_xchg_price_code_' " := ( xchg_price_code__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_xchg_price_code_' " := ( xchg_price_code__right ) (in custom URValue at level 0) : ursus_scope. 
 
 Definition deals_limit__left := ( ULState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : ULValue XInteger8 ) . 
 Definition deals_limit__right := ( URState (f:=_Contract) (H:=ContractLEmbeddedType deals_limit_ ) : URValue XInteger8 false ) . 
 Notation " '_deals_limit_' " := ( deals_limit__left ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " '_deals_limit_' " := ( deals_limit__right ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.split_depth' " := ( StateInit_ι_split_depth ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.split_depth' " := ( StateInit_ι_split_depth ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.special' " := ( StateInit_ι_special ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.special' " := ( StateInit_ι_special ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.code' " := ( StateInit_ι_code ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.code' " := ( StateInit_ι_code ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.data' " := ( StateInit_ι_data ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.data' " := ( StateInit_ι_data ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'StateInit.library' " := ( StateInit_ι_library ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'StateInit.library' " := ( StateInit_ι_library ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.flex_addr_' " := ( DTradingPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.flex_addr_' " := ( DTradingPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.tip3_root_' " := ( DTradingPair_ι_tip3_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.tip3_root_' " := ( DTradingPair_ι_tip3_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.deploy_value_' " := ( DTradingPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DTradingPair.deploy_value_' " := ( DTradingPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.flex_addr_' " := ( DXchgPair_ι_flex_addr_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.flex_addr_' " := ( DXchgPair_ι_flex_addr_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.tip3_major_root_' " := ( DXchgPair_ι_tip3_major_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.tip3_major_root_' " := ( DXchgPair_ι_tip3_major_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.tip3_minor_root_' " := ( DXchgPair_ι_tip3_minor_root_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.tip3_minor_root_' " := ( DXchgPair_ι_tip3_minor_root_ ) (in custom URValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.deploy_value_' " := ( DXchgPair_ι_deploy_value_ ) (in custom ULValue at level 0) : ursus_scope. 
 Notation " 'DXchgPair.deploy_value_' " := ( DXchgPair_ι_deploy_value_ ) (in custom URValue at level 0) : ursus_scope. 
 
Module Calls (tc : SpecSig).

Export tc.

Local Open Scope string_scope.


Definition constructor_left {R b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 }
( deployer_pubkey : URValue XInteger256 b0) 
( ownership_description : URValue XString b1) 
( owner_address : URValue (XMaybe XAddress) b2)
( transfer_tip3 : URValue XInteger128 b3) 
( return_ownership : URValue XInteger128 b4) 
( trading_pair_deploy : URValue XInteger128 b5) 
( order_answer : URValue XInteger128 b6)
( process_queue : URValue XInteger8 b7) 
( send_notify : URValue XAddress b8)
( deals_limit : URValue XAddress b9) :  UExpression R 
((orb(orb(orb(orb(orb(orb(orb(orb(orb b9 b8)b7)b6)b5)b4)b3)b2)b1)b0)) :=

wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ10) 
constructor 
deployer_pubkey
ownership_description
owner_address
transfer_tip3 
return_ownership 
trading_pair_deploy 
order_answer
process_queue 
send_notify
deals_limit ).

Notation " 'constructor_' '(' x0 ',' x1 ',' x2 ',' x3 ',' x4 ',' x5 ',' x6 ',' x7 ',' x8 ',' x9 ')' " :=
( constructor_left x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 )
(in custom ULValue at level 0 , 
x0 custom URValue at level 0,
x1 custom URValue at level 0,
x2 custom URValue at level 0,
x3 custom URValue at level 0,
x4 custom URValue at level 0,
x5 custom URValue at level 0,
x6 custom URValue at level 0,
x7 custom URValue at level 0,
x8 custom URValue at level 0,
x9 custom URValue at level 0) : ursus_scope.

Definition setPairCode_left {R b1} (x: URValue XCell b1 ) : UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) setPairCode x).    

Notation " 'setPairCode_' '(' x ')' " := (setPairCode_left x)  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.

Definition setXchgPairCode_left {R b1} (x: URValue XCell b1 ) : UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) setXchgPairCode x).    

Notation " 'setXchgPairCode_' '(' x ')' " := (setXchgPairCode x)  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.

Definition setPriceCode_left {R b1} (x: URValue XCell b1 ) : UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) setPriceCode x).    

Notation " 'setPriceCode_' '(' x ')' " := (setPriceCode_left x)  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.

Definition setXchgPriceCode_left {R b1} (x: URValue XCell b1 ) : UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) setXchgPriceCode x).    

Notation " 'setXchgPriceCode_' '(' x ')' " := (setXchgPriceCode_left x)  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.

Definition transfer_INTERNAL_left {R b1 b2} 
(x0: URValue XAddress b1 ) 
(x1: URValue XInteger128 b2 )
: UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) transfer_INTERNAL x0 x1 ).    

Notation " 'transfer_INTERNAL_' '(' x0 ',' x1 ')' " := (transfer_INTERNAL_left x0 x1 )  
   (in custom ULValue at level 0 , 
x0 custom URValue at level 0 ,
x1 custom URValue at level 0) : ursus_scope.

Definition transfer_EXTERNAL_left {R b1 b2} 
(x0: URValue XAddress b1 ) 
(x1: URValue XInteger128 b2 )
: UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) transfer_EXTERNAL x0 x1 ).    

Notation " 'transfer_EXTERNAL_' '(' x0 ',' x1 ')' " := (transfer_EXTERNAL_left x0 x1 )  
   (in custom ULValue at level 0 , 
x0 custom URValue at level 0 ,
x1 custom URValue at level 0) : ursus_scope.

Definition isFullyInitialized_right : URValue XBool false :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) isFullyInitialized ).    

Notation " 'isFullyInitialized_' '(' ')' " := (isFullyInitialized_right )  
   (in custom URValue at level 0 ) : ursus_scope.

Definition getTonsCfg_right : URValue TonsConfigLRecord false :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getTonsCfg ).    

Notation " 'getTonsCfg_' '(' ')' " := ( getTonsCfg_right )  
   (in custom URValue at level 0 ) : ursus_scope.

Definition getTradingPairCode_right : URValue XCell false := (*TODO: maybe true*)
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getTradingPairCode ).    

Notation " 'getTradingPairCode_' '(' ')' " := ( getTradingPairCode_right )  
   (in custom URValue at level 0 ) : ursus_scope.

Definition getXchgPairCode_right : URValue XCell false := (*TODO: maybe true*)
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getXchgPairCode ).    

Notation " 'getXchgPairCode_' '(' ')' " := ( getXchgPairCode_right )  
   (in custom URValue at level 0 ) : ursus_scope.

Definition getSellPriceCode_right {b1} (x: URValue XAddress b1 ) : URValue XCell true :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) getSellPriceCode x).    

Notation " 'getSellPriceCode_' '(' x ')' " := (getSellPriceCode_right x)  
   (in custom URValue at level 0 , x custom URValue at level 0) : ursus_scope.

Definition getXchgPriceCode_right {b1 b2} 
(x0: URValue XAddress b1 ) 
(x1: URValue XAddress b2 ) 
: URValue XCell true :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) getXchgPriceCode x0 x1).    

Notation " 'getXchgPriceCode_' '(' x0 ',' x1 ')' " := (getXchgPriceCode_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.

Definition getSellTradingPair_right {b1} (x: URValue XAddress b1 ) : URValue XAddress b1 :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) getSellTradingPair x).    

Notation " 'getSellTradingPair_' '(' x ')' " := (getSellTradingPair_right x)  
   (in custom URValue at level 0 , x custom URValue at level 0) : ursus_scope.

Definition getXchgTradingPair_right {b1 b2} 
(x0: URValue XAddress b1 ) 
(x1: URValue XAddress b2 ) 
: URValue XAddress (orb b2 b1) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) getXchgTradingPair x0 x1).    

Notation " 'getXchgTradingPair_' '(' x0 ',' x1 ')' " := (getXchgTradingPair_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.

Definition getDealsLimit_right : URValue XInteger8 false := 
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getDealsLimit ).    

Notation " 'getDealsLimit_' '(' ')' " := ( getDealsLimit_right )  
   (in custom URValue at level 0 ) : ursus_scope.

Definition getOwnershipInfo_right : URValue FlexOwnershipInfoLRecord false := 
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getOwnershipInfo ).    

Notation " 'getOwnershipInfo_' '(' ')' " := ( getOwnershipInfo_right )  
   (in custom URValue at level 0 ) : ursus_scope.

Definition _fallback_right {b1 b2} 
(x0: URValue XCell b1 ) 
(x1: URValue XSlice b2 ) 
: URValue XInteger (orb b2 b1) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) _fallback x0 x1).    

Notation " '_fallback_' '(' x0 ',' x1 ')' " := (_fallback_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.

Definition prepare_flex_state_init_and_addr_right {b1 b2} 
(x0: URValue ContractLRecord b1 ) 
(x1: URValue XCell b2 ) 
: URValue ( StateInitLRecord # XInteger256 )%sol (orb b2 b1) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) prepare_flex_state_init_and_addr x0 x1).    

Notation " 'prepare_flex_state_init_and_addr_' '(' x0 ',' x1 ')' " := (prepare_flex_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.


End Calls. 

End FuncNotations.
