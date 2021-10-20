 Require Import Coq.Program.Basics. 

Require Import String. 
Require Import FinProof.Types.IsoTypes. 
Require Import FinProof.Common. 
Require Import FinProof.MonadTransformers21. 

Require Import FinProof.ProgrammingWith.  
Require Import UMLang.UrsusLib. 
Require Import UMLang.SolidityNotations2. 
Require Import UMLang.ClassGenerator.ClassGenerator.
Require Import UrsusTVM.tvmFunc. 

(* Require Import Project.CommonTypes.  *)
Require Import Contracts.FlexClient.ClassTypes.
Require Import Contracts.FlexClient.Interface.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope xlist_scope.


(* 1 *) Inductive MessagesAndEventsFields := | MessagesAndEvents_ι_field_1 | MessagesAndEvents_ι_field_2 | MessagesAndEvents_ι_field_3 | MessagesAndEvents_ι_field_4 .
(* 1 *) Inductive FlexClientFields := | FlexClient_ι_owner_ | FlexClient_ι_trading_pair_code_ | FlexClient_ι_xchg_pair_code_ | FlexClient_ι_workchain_id_ | FlexClient_ι_tons_cfg_ | FlexClient_ι_flex_ | FlexClient_ι_notify_addr_ | FlexClient_ι_ext_wallet_code_ | FlexClient_ι_flex_wallet_code_ | FlexClient_ι_flex_wrapper_code_ .
(* 1 *) Inductive LocalStateFieldsI := | LocalState_ι_uint256 | LocalState_ι_uint256Index | LocalState_ι_cell | LocalState_ι_cellIndex | LocalState_ι_TonsConfig | LocalState_ι_TonsConfigIndex | LocalState_ι_address | LocalState_ι_addressIndex | LocalState_ι_uint128 | LocalState_ι_uint128Index | LocalState_ι_TradingPair | LocalState_ι_TradingPairIndex | LocalState_ι_tplStateInituint256 | LocalState_ι_tplStateInituint256Index | LocalState_ι_StateInit | LocalState_ι_StateInitIndex | LocalState_ι_XchgPair | LocalState_ι_XchgPairIndex | LocalState_ι_tplStateInitaddress | LocalState_ι_tplStateInitaddressIndex | LocalState_ι_SellArgs | LocalState_ι_SellArgsIndex | LocalState_ι_ITONTokenWalletPtr | LocalState_ι_ITONTokenWalletPtrIndex | LocalState_ι_IPricePtr | LocalState_ι_IPricePtrIndex | LocalState_ι_int | LocalState_ι_intIndex | LocalState_ι_Price | LocalState_ι_PriceIndex | LocalState_ι_uint8 | LocalState_ι_uint8Index | LocalState_ι_uint32 | LocalState_ι_uint32Index | LocalState_ι_Tip3Config | LocalState_ι_Tip3ConfigIndex | LocalState_ι_PriceXchg | LocalState_ι_PriceXchgIndex | LocalState_ι_PayloadArgs | LocalState_ι_PayloadArgsIndex | LocalState_ι_optcell | LocalState_ι_optcellIndex | LocalState_ι_bool | LocalState_ι_boolIndex .
(* 1 *) Inductive LedgerFieldsI := | Ledger_ι_Contract | Ledger_ι_ContractCopy | Ledger_ι_VMState | Ledger_ι_MessagesAndEvents | Ledger_ι_MessagesAndEventsCopy | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .

 Module FlexClientClass (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 
(*  Module Export SolidityNotationsClass := SolidityNotations xt sm.  *)
 Module Export VMStateModule := VMStateModule xt sm. 
 Module Export ClassTypesModule := ClassTypes xt sm .
(* Module Export CommonTypes := Types xt sm. *)


 Inductive f1000 := | _int | _intIndex . 
 Definition t1000 := [ ( XHMap (string*nat) XInteger ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord f1000 t1000 . 
 Opaque f1000Record . 
 
 Inductive f1001 := | _optcell | _optcellIndex . 
 Definition t1001 := [ ( XHMap (string*nat) ( XMaybe XCell ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord f1001 t1001 . 
 Opaque f1001Record . 
 
 Inductive f1010 := | _tpladdressaddress | _tpladdressaddressIndex . 
 Definition t1010 := [ ( XHMap (string*nat) ( XAddress * XAddress ) ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord f1010 t1010 . 
 Opaque f1010Record . 
 
 Inductive f1011 := | _uint256 | _uint256Index . 
 Definition t1011 := [ ( XHMap (string*nat) XInteger256 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord f1011 t1011 . 
 Opaque f1011Record . 
 
 Inductive f1100 := | _uint128 | _uint128Index . 
 Definition t1100 := [ ( XHMap (string*nat) XInteger128 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord f1100 t1100 . 
 Opaque f1100Record . 
 
 Inductive f1101 := | _uint8 | _uint8Index . 
 Definition t1101 := [ ( XHMap (string*nat) XInteger8 ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord f1101 t1101 . 
 Opaque f1101Record . 
 
 Inductive f1110 := | _address | _addressIndex . 
 Definition t1110 := [ ( XHMap (string*nat) XAddress ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord f1110 t1110 . 
 Opaque f1110Record . 
 
 Inductive f1111 := | _cell | _cellIndex . 
 Definition t1111 := [ ( XHMap (string*nat) XCell ) : Type ; ( XHMap string nat ) : Type ] . 
 GeneratePruvendoRecord f1111 t1111 . 
 Opaque f1111Record . 
 
 
 Inductive f100 := | f1000 | f1001 . 
 Definition t100 := [ t1000 ; t1001 ] . 
 GeneratePruvendoRecord f100 t100 . 
 Opaque f100Record . 
 
 Inductive f101 := | f1010 | f1011 . 
 Definition t101 := [ t1010 ; t1011 ] . 
 GeneratePruvendoRecord f101 t101 . 
 Opaque f101Record . 
 
 Inductive f110 := | f1100 | f1101 . 
 Definition t110 := [ t1100 ; t1101 ] . 
 GeneratePruvendoRecord f110 t110 . 
 Opaque f110Record . 
 
 Inductive f111 := | f1110 | f1111 . 
 Definition t111 := [ t1110 ; t1111 ] . 
 GeneratePruvendoRecord f111 t111 . 
 Opaque f111Record . 
 
 
 Inductive f10 := | f100 | f101 . 
 Definition t10 := [ t100 ; t101 ] . 
 GeneratePruvendoRecord f10 t10 . 
 Opaque f10Record . 
 
 Inductive f11 := | f110 | f111 . 
 Definition t11 := [ t110 ; t111 ] . 
 GeneratePruvendoRecord f11 t11 . 
 Opaque f11Record . 
 
 
 Inductive f1 := | f10 | f11 . 
 Definition t1 := [ t10 ; t11 ] . 
 GeneratePruvendoRecord f1 t1 . 
 Opaque f1Record . 













(* 2 *) Definition MessagesAndEventsStateL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XBool ) : Type ; 
 ( XCell ) : Type ; 
 ( ( XHMap XInteger XInteger ) ) : Type ] .

GeneratePruvendoRecord MessagesAndEventsStateL MessagesAndEventsFields .

Check addr_std_compact.

(* 2 *) Definition FlexClientStateL : list Type := 
 [ ( XInteger256 ) : Type ; 
 ( XCell ) : Type ; 
 ( XCell ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TonsConfigStateLRecord ) : Type ; 
 ( addr_std_compact ) : Type ; 
 ( addr_std_compact ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ; 
 ( XMaybe XCell ) : Type ] .
Elpi GeneratePruvendoRecord FlexClientStateL FlexClientFields . 
 Opaque FlexClientStateLRecord . 

(* 2 *) Definition LocalStateStateL : list Type := 
 [ ( XHMap (string*nat) XInteger256 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XCell ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) TonsConfigStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XAddress ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger128 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) TradingPairStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( StateInitStateLRecord * XInteger256 ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) StateInitStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XchgPairStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( StateInitStateLRecord * XAddress * XInteger256 ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) SellArgsStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ITONTokenWalletPtr ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) IPricePtr ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) DPriceStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger8 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XInteger32 ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) Tip3ConfigStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) DPriceXchgStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) PayloadArgsStateLRecord ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) ( XMaybe XCell ) ) : Type ; 
 ( XHMap string nat ) : Type ; 
 ( XHMap (string*nat) XBool ) : Type ; 
 ( XHMap string nat ) : Type ] .
Elpi GeneratePruvendoRecord LocalStateStateL LocalStateFieldsI . 
 Opaque LocalStateStateLRecord . 

(* 2 *) Definition LedgerStateL : list Type := 
 [ ( FlexClientStateLRecord ) : Type ; 
   ( FlexClientStateLRecord ) : Type ; 
 ( VMStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ] .

Opaque FlexClientStateLRecord.
Opaque VMStateLRecord.
Opaque MessagesAndEventsStateLRecord.
Opaque LocalStateStateLRecord.
Elpi GeneratePruvendoRecord LedgerStateL LedgerFieldsI .
Transparent VMStateLRecord.
Transparent MessagesAndEventsStateLRecord.
Transparent LocalStateStateLRecord.

Transparent MessagesAndEventsStateLRecord .
Transparent TickTockStateLRecord .
Transparent StateInitStateLRecord .
Transparent anycast_infoStateLRecord .
Transparent addr_stdStateLRecord .
Transparent addr_std_fixedStateLRecord .
Transparent SellArgsStateLRecord .
Transparent FlexBurnWalletArgsStateLRecord .
Transparent TonsConfigStateLRecord .
Transparent FlexClientStateLRecord .
Transparent XchgPairStateLRecord .
Transparent OrderInfoStateLRecord .
Transparent Tip3ConfigStateLRecord . 
Transparent DPriceStateLRecord .
Transparent RationalPriceStateLRecord .
Transparent DPriceXchgStateLRecord .
Transparent TradingPairStateLRecord .
Transparent PayloadArgsStateLRecord .
Transparent LocalStateStateLRecord .
Transparent LedgerStateLRecord .

(***************************************)

Definition LedgerPruvendoRecord := LedgerStateLPruvendoRecord .
Definition LedgerLocalState := LocalStateStateLRecord .
Definition LedgerLocalFields := LocalStateFieldsI.
Definition LedgerLocalPruvendoRecord := LocalStateStateLPruvendoRecord .
Definition LocalEmbedded := LedgerStateLEmbeddedType Ledger_ι_LocalState .
Definition LocalCopyEmbedded := LedgerStateLEmbeddedType Ledger_ι_LocalStateCopy.
Definition LocalDefault : XDefault LocalStateStateLRecord := prod_default.
Definition Ledger_LocalState := Ledger_ι_LocalState.
Definition Ledger_LocalStateCopy := Ledger_ι_LocalStateCopy.
Definition iso_local := Ledger_ι_LocalStateIso.
Definition Ledger := LedgerStateLRecord.
Definition LedgerFields := LedgerFieldsI.

Lemma LedgerFieldsDec: forall (m1 m2: LedgerFieldsI), {m1=m2}+{m1<>m2}.
Proof.
  intros.
  decide equality.
Defined.

Lemma LocalCopySameType: field_type  Ledger_LocalState = 
field_type Ledger_LocalStateCopy.
Proof.
  reflexivity.
Defined.

Class LocalStateField (X:Type): Type := 
{
    local_index_embedded:> EmbeddedType LocalStateStateLRecord (XHMap string nat) ;
    local_state_field: LedgerLocalFields;
    local_field_type_correct: field_type local_state_field = XHMap (string*nat)%type X;
}.


Definition LedgerVMStateEmbedded := LedgerStateLEmbeddedType Ledger_ι_VMState . 
Definition LedgerVMStateField := Ledger_ι_VMState .
Definition isoVMState := Ledger_ι_VMStateIso.

Definition LedgerMessagesEmbedded := LedgerStateLEmbeddedType Ledger_ι_MessagesAndEvents . 
Definition LedgerMessagesField := Ledger_ι_MessagesAndEvents .
Definition isoMessages := Ledger_ι_MessagesAndEventsIso.
Definition MessagesAndEvents := MessagesAndEventsStateLRecord .

GenerateLocalStateInstances LocalStateStateL LocalStateFieldsI Build_LocalStateField LocalStateStateLEmbeddedType.

Check LocalState_ι_intLocalField.
Check LocalState_ι_boolLocalField.

Definition LocalStateField_XInteger := LocalState_ι_intLocalField .
Definition LocalStateField_XBool := LocalState_ι_boolLocalField .
Definition LocalStateField_XCell := LocalState_ι_cellLocalField .


(***************************************)
Lemma MessagesAndEventsFields_noeq : forall (f1 f2:  MessagesAndEventsFields ) 
         (v2: field_type f2) (r :  MessagesAndEventsStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= MessagesAndEventsStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

Lemma FlexClientFields_noeq : forall (f1 f2:  FlexClientFields ) 
         (v2: field_type f2) (r :  FlexClientStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= FlexClientStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

(* Lemma LocalStateFields_noeq : forall (f1 f2:  LocalStateFieldsI ) 
         (v2: field_type f2) (r :  LocalStateStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= LocalStateStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed . *)

Lemma LedgerFields_noeq : forall (f1 f2:  LedgerFields ) 
         (v2: field_type f2) (r :  LedgerStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= LedgerStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

End FlexClientClass .
