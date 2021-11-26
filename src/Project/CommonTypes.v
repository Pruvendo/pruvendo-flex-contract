Require Import UMLang.BasicModuleTypes.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address .
Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address | Tip3Config_ι_workchain_id_.
Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
Inductive PayloadArgsFields := | PayloadArgs_ι_sell | PayloadArgs_ι_amount | PayloadArgs_ι_receive_tip3_wallet | PayloadArgs_ι_client_addr .
Inductive OrderRetFields := | OrderRet_ι_err_code | OrderRet_ι_processed | OrderRet_ι_enqueued .
Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_sells_ | process_ret_ι_buys_amount | process_ret_ι_buys_ | process_ret_ι_ret_ .


Module Types (xt: XTypesSig) (sm: StateMonadSig).
Export xt. 

Module Export BasicTypesModule := BasicTypes xt sm.
Local Open Scope glist_scope.

Definition IFlexNotifyPtr := XAddress. 
Definition ITONTokenWalletPtr := XAddress. 
Definition IPricePtr := XAddress. 
Definition TokensType := XUInteger256. 
Definition WalletGramsType := XUInteger128. 
Definition Grams := XUInteger16 . 
Definition addr_std_compact := XAddress . 
Definition varuint32 := XUInteger32 .
Definition address_t := XAddress.
Definition IWrapperPtr := XAddress .


(* 2 *) Definition TonsConfigL : list Type := 
[ ( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ; 
( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord TonsConfigL TonsConfigFields . 

 Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
 ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 
 Definition addr_std_fixedL : list Type := 
 [ ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ] .
Elpi GeneratePruvendoRecord addr_std_fixedL addr_std_fixedFields . 
Opaque addr_std_fixedLRecord . 

Definition Tip3ConfigL : list Type := 
 [ ( XString ) : Type ; 
 ( XString ) : Type ; 
 ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ; 
 ( XAddress ) : Type ;
 ( XUInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord Tip3ConfigL Tip3ConfigFields . 
Opaque Tip3ConfigLRecord .

Definition StateInitL : list Type := 
 [ ( XMaybe XUInteger ) : Type ; 
 ( XMaybe TickTockLRecord ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 
Opaque StateInitLRecord .


(* 2 *) Definition PayloadArgsL : list Type := 
[ ( XBool ) : Type ; 
( XUInteger128 ) : Type ; 
( addr_std_fixedLRecord ) : Type ; 
( addr_std_fixedLRecord ) : Type ] .
Elpi GeneratePruvendoRecord PayloadArgsL PayloadArgsFields . 
Opaque PayloadArgsLRecord .

 Definition OrderRetL : list Type := 
 [ ( XUInteger32 ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord OrderRetL OrderRetFields . 
 Opaque OrderRetLRecord . 



Definition process_retL : list Type := 
 [ ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( XUInteger128 ) : Type ; 
 ( ( XQueue OrderInfoLRecord ) ) : Type ; 
 ( ( XMaybe OrderRetLRecord ) ) : Type ] .
Elpi GeneratePruvendoRecord process_retL process_retFields . 
 Opaque process_retLRecord .

End Types.
