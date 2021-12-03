Require Import Coq.Program.Equality.

Require Import FinProof.Common.
Require Import UMLang.BasicModuleTypes.
Require Import UMLang.LocalClassGenerator.ClassGenerator.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.

Module Type CompilerOptions.

Parameter Internal: bool .
Parameter TIP3_ENABLE_EXTERNAL : bool .

End CompilerOptions.

(* 1 *)Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 2 *)Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 3 *)(* Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address . *)
(* 4 *)Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address | Tip3Config_ι_workchain_id_.
(* 5 *)Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 7 *)Inductive OrderRetFields := | OrderRet_ι_err_code | OrderRet_ι_processed | OrderRet_ι_enqueued .

Module Types (xt: XTypesSig) (sm: StateMonadSig).
Export xt. 

Module Export BasicTypesModule := BasicTypes xt sm.
Module Export CommonVMStateModule := VMStateModule xt sm.
Local Open Scope glist_scope.

(* 1 *) Definition TonsConfigL : list Type := 
[ ( XUInteger128 ) : Type ; 
  ( XUInteger128 ) : Type ; 
  ( XUInteger128 ) : Type ; 
  ( XUInteger128 ) : Type ; 
  ( XUInteger128 ) : Type ; 
  ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord TonsConfigL TonsConfigFields . 

(* 2 *)Definition TickTockL : list Type := 
 [ ( XBool ) : Type ; 
   ( XBool ) : Type ] .
Elpi GeneratePruvendoRecord TickTockL TickTockFields . 
 
(* 3 *)(* Definition addr_std_fixedL : list Type := 
 [ ( XUInteger8 ) : Type ; 
 ( XUInteger256 ) : Type ] .
Elpi GeneratePruvendoRecord addr_std_fixedL addr_std_fixedFields .  *)

(* 4 *)Definition Tip3ConfigL : list Type := 
 [ ( XString ) : Type ; 
   ( XString ) : Type ; 
   ( XUInteger8 ) : Type ; 
   ( XUInteger256 ) : Type ; 
   ( address ) : Type ;
   ( XUInteger8 ) : Type ] .
Elpi GeneratePruvendoRecord Tip3ConfigL Tip3ConfigFields . 

(* 5 *)Definition StateInitL : list Type := 
 [ ( XMaybe XUInteger ) : Type ; 
   ( XMaybe TickTockLRecord ) : Type ; 
   ( XMaybe cell_ ) : Type ; 
   ( XMaybe cell_ ) : Type ; 
   ( XMaybe cell_ ) : Type ] .
Elpi GeneratePruvendoRecord StateInitL StateInitFields . 

 (* 7 *)Definition OrderRetL : list Type := 
 [ ( XUInteger32 ) : Type ; 
   ( XUInteger128 ) : Type ; 
   ( XUInteger128 ) : Type ] .
Elpi GeneratePruvendoRecord OrderRetL OrderRetFields . 

(******************************************)
Definition TokensType := XUInteger256. 
Definition WalletGramsType := XUInteger128. 
Definition Grams := XUInteger16 .
(*what is this?*)
(* Definition address := addr_stdLRecord.  *)
Definition addr_std_compact := address .
Definition addr_std_fixed := address .
Definition address_t := address .
(*what is this?*)
Definition varuint32 := XUInteger32 .

End Types.
