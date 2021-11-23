Require Import UMLang.BasicModuleTypes.
Require Import UMLang.LocalClassGenerator.ClassGenerator.



Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .

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
                            Definition auto := XUInteger . 
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
Opaque TonsConfigLRecord . 

End Types.
