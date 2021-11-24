Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import CommonNotations.
Require Import Contracts.TONTokenWallet.ClassTypes.
Require Import Contracts.TONTokenWallet.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export CommonNotationsModule := CommonNotations xt sm LedgerModuleForFuncSig. 
(* Module Export stdTypesNotationsModule := stdTypesNotations xt sm LedgerModuleForFuncSig. *)
Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter transfer : ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> UExpression PhantomType false . 
 Parameter transferWithNotify : ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType false . 
 Parameter transferToRecipient : ( ( XAddress ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> UExpression PhantomType false . 
 Parameter transferToRecipientWithNotify : ( ( XAddress ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType false . 
 Parameter requestBalance : UExpression XInteger128 false . 
 Parameter accept : ( ( XInteger128 ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> UExpression XBool true . 
 Parameter internalTransfer : ( ( XInteger128 ) ) -> ( ( XAddress ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter destroy : ( ( XAddress ) ) -> UExpression PhantomType true . 
 Parameter burn : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> UExpression PhantomType false . 
 Parameter lendOwnership : ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger256 ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger32 ) ) -> ( ( XCell ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter returnOwnership : ( ( XInteger128 ) ) -> UExpression PhantomType false . 
 Parameter getDetails : UExpression details_infoLRecord false . 
 Parameter getName : UExpression XString false . 
 Parameter getSymbol : UExpression XString false . 
 Parameter getDecimals : UExpression XInteger8 false . 
 Parameter getBalance : UExpression XInteger128 false . 
 Parameter getRootKey : UExpression XInteger256 false . 
 Parameter getWalletKey : UExpression XInteger256 false . 
 Parameter getRootAddress : UExpression XAddress false . 
 Parameter getOwnerAddress : UExpression XAddress false . 
 Parameter getCode : UExpression XCell false . 
 Parameter allowance : UExpression allowance_infoLRecord false . 
 Parameter approve : ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> UExpression PhantomType true . 
 Parameter transferFrom : ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> UExpression PhantomType false . 
 Parameter transferFromWithNotify : ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XCell ) ) -> UExpression PhantomType false . 
 Parameter internalTransferFrom : ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter disapprove : UExpression PhantomType false . 
 Parameter _on_bounced : ( ( XCell ) ) -> ( ( XSlice ) ) -> UExpression XInteger true . 
 Parameter _fallback : ( ( XCell ) -> ( ( XSlice ) ) -> UExpression XInteger true . 
 Parameter transfer_impl : ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter transfer_to_recipient_impl : ( ( XAddress ) ) -> ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType false . 
 Parameter transfer_from_impl : ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XAddress ) ) -> ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType false . 
 Parameter get_owner_addr : UExpression XAddress false . 
 Parameter fixup_answer_addr : ( ( XAddress ) ) -> UExpression XAddress false . 
 Parameter check_transfer_requires : ( ( XInteger128 ) ) -> ( ( XInteger128 ) ) -> UExpression XInteger128 true . 
 Parameter prepare_transfer_message_flags : ( ( XInteger128 ) ) -> UExpression XInteger false . 
 Parameter update_spent_balance : ( ( XInteger128 ) ) -> ( ( XBool ) ) -> UExpression PhantomType false . 
 Parameter optional_owner : ( ( XAddress ) ) -> UExpression XMaybe XAddress false . 
 Parameter calc_wallet_init_hash : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 
 Parameter expected_sender_address : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> UExpression XInteger256 false . 
 Parameter calc_wallet_init : ( ( XInteger256 ) ) -> ( ( XAddress ) ) -> UExpression ( StateInitLRecord * XAddress ) false . 
 Parameter filter_lend_ownerhip_map : UExpression ( lend_ownership_mapLRecord * XInteger128 ) false . 
 Parameter filter_lend_ownerhip_array : UExpression ( lend_ownership_arrayLRecord * XInteger128 ) false . 
 Parameter is_internal_owner : UExpression XBool false . 
 Parameter check_internal_owner : ( ( XBool ) ) -> ( ( XBool ) ) -> UExpression XInteger128 true . 
 Parameter check_external_owner : UExpression XInteger128 true . 
 Parameter check_owner : ( ( XBool ) ) -> ( ( XBool ) ) -> UExpression XInteger128 false . 
 Parameter prepare_root_state_init_and_addr : ( ( XCell ) ) -> ( ( DRootTokenContractLRecord ) ) -> UExpression ( StateInitLRecord * XInteger256 ) false . 


End SpecSig.

End Spec.  