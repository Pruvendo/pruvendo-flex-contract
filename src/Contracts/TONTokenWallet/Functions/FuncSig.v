Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonAxioms.

Require Import TONTokenWallet.ClassTypes.
Require Import TONTokenWallet.Ledger.
Require Import TONTokenWallet.ClassTypesNotations.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig. 
Module Export stdTypesNotationsModule := stdTypesNotations xt sm LedgerModuleForFuncSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Notation address_t := address.

Notation lend_ownership_map := (mapping addr_std_fixed lend_recordLRecord).
Notation lend_ownership_array := (mapping uint lend_array_recordLRecord).



Module Type SpecSig.



Parameter transfer : ( ( address ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> ( ( XBool ) ) -> UExpression PhantomType true . 
 Parameter transferWithNotify : ( ( address ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter transferToRecipient : ( ( address ) ) -> ( ( XUInteger256 ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> UExpression PhantomType true . 
 Parameter transferToRecipientWithNotify : ( ( address ) ) -> ( ( XUInteger256 ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter requestBalance : UExpression XUInteger128 false . 
 Parameter accept : ( ( XUInteger128 ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> UExpression XBool true . 
 Parameter internalTransfer : ( ( XUInteger128 ) ) -> ( ( address ) ) -> ( ( XUInteger256 ) ) -> ( ( address ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter destroy : ( ( address ) ) -> UExpression PhantomType true . 
 Parameter burn : ( ( XUInteger256 ) ) -> ( ( address ) ) -> UExpression PhantomType true . 
 Parameter lendOwnership : ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger256 ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger32 ) ) -> ( ( XCell ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter returnOwnership : ( ( XUInteger128 ) ) -> UExpression PhantomType true . 
 Parameter getDetails : UExpression details_infoLRecord false . 
 Parameter getName : UExpression XString false . 
 Parameter getSymbol : UExpression XString false . 
 Parameter getDecimals : UExpression XUInteger8 false . 
 Parameter getBalance : UExpression XUInteger128 false . 
 Parameter getRootKey : UExpression XUInteger256 false . 
 Parameter getWalletKey : UExpression XUInteger256 false . 
 Parameter getRootAddress : UExpression address false . 
 Parameter getOwnerAddress : UExpression address false . 
 Parameter getCode : UExpression XCell false . 
 Parameter allowance : UExpression allowance_infoLRecord false . 
 Parameter approve : ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> UExpression PhantomType true . 
 Parameter transferFrom : ( ( address ) ) -> ( ( address ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> UExpression PhantomType true . 
 Parameter transferFromWithNotify : ( ( address ) ) -> ( ( address ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter internalTransferFrom : ( ( address ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter disapprove : UExpression PhantomType true . 
 Parameter _on_bounced : ( ( XCell ) ) -> ( ( XSlice ) ) -> UExpression XUInteger true . 
 Parameter _fallback : ( ( XCell ) ) -> ( ( XSlice ) ) -> UExpression XUInteger true . 
 Parameter transfer_impl : ( ( address ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter transfer_to_recipient_impl : ( ( address ) ) -> ( ( XUInteger256 ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter transfer_from_impl : ( ( address ) ) -> ( ( address ) ) -> ( ( address ) ) -> ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> ( ( XBool ) ) -> ( ( XCell ) ) -> UExpression PhantomType true . 
 Parameter get_owner_addr : UExpression address false . 
 Parameter fixup_answer_addr : ( ( address ) ) -> UExpression address false . 
 Parameter check_transfer_requires : ( ( XUInteger128 ) ) -> ( ( XUInteger128 ) ) -> UExpression XUInteger128 true . 
 Parameter prepare_transfer_message_flags : ( ULValue ( XUInteger128 ) ) -> UExpression XUInteger false . 
 Parameter update_spent_balance : ( ( XUInteger128 ) ) -> ( ( XBool ) ) -> UExpression PhantomType false . 
 Parameter optional_owner : ( ( address ) ) -> UExpression ( XMaybe address ) false . 
 Parameter calc_wallet_init_hash : ( ( XUInteger256 ) ) -> ( ( address ) ) -> UExpression ( StateInitLRecord # XUInteger256 ) false . 
 Parameter expected_sender_address : ( ( XUInteger256 ) ) -> ( ( address ) ) -> UExpression XUInteger256 false . 
 Parameter calc_wallet_init : ( ( XUInteger256 ) ) -> ( ( address ) ) -> UExpression ( StateInitLRecord # address ) false . 
 Parameter filter_lend_ownerhip_map : UExpression ( lend_ownership_map # XUInteger128 ) false . 
 Parameter filter_lend_ownerhip_array : UExpression ( lend_ownership_array # XUInteger128 ) false . 
 Parameter is_internal_owner : UExpression XBool false . 
 Parameter check_internal_owner : ( ( XBool ) ) -> ( ( XBool ) ) -> UExpression XUInteger128 true . 
 Parameter check_external_owner : UExpression XUInteger128 true . 
 Parameter check_owner : ( ( XBool ) ) -> ( ( XBool ) ) -> UExpression XUInteger128 true . 

End SpecSig.

End Spec.  