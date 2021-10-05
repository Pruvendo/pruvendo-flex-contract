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

Require Import Project.CommonTypes.

Require Import Contracts.FlexClient.ClassTypes.
Require Import Contracts.FlexClient.Interface.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope xlist_scope.

(* 1 *) Inductive MessagesAndEventsFields := | MessagesAndEvents_ι_field_1 | MessagesAndEvents_ι_field_2 | MessagesAndEvents_ι_field_3 | MessagesAndEvents_ι_field_4 .
(* 1 *) Inductive ContractFields := | owner_ | trading_pair_code_ | xchg_pair_code_ | workchain_id_ | tons_cfg_ | flex_ | notify_addr_ | ext_wallet_code_ | flex_wallet_code_ | flex_wrapper_code_ .
(* 1 *) Inductive LocalStateFieldsI := | _uint256 | _uint256Index | _cell | _cellIndex | _TonsConfig | _TonsConfigIndex | _address | _addressIndex | _uint128 | _uint128Index | _TradingPair | _TradingPairIndex | _tplStateInituint256 | _tplStateInituint256Index | _StateInit | _StateInitIndex | _XchgPair | _XchgPairIndex | _tplStateInitaddress | _tplStateInitaddressIndex | _SellArgs | _SellArgsIndex | _ITONTokenWalletPtr | _ITONTokenWalletPtrIndex | _IPricePtr | _IPricePtrIndex | _int | _intIndex | _Price | _PriceIndex | _uint8 | _uint8Index | _uint32 | _uint32Index | _Tip3Config | _Tip3ConfigIndex | _PriceXchg | _PriceXchgIndex | _PayloadArgs | _PayloadArgsIndex | _optcell | _optcellIndex | _bool | _boolIndex .
(* 1 *) Inductive LedgerFieldsI := | _Contract | _ContractCopy | _VMState | _MessagesAndEvents | _MessagesAndEventsCopy | _LocalState | _LocalStateCopy .

 Module Ledger (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 
 Module Import SolidityNotationsForLedger := SolidityNotations xt sm.  
 Module Export VMStateModule := VMStateModule xt sm. 
 Module Export TypesModuleForLedger := ClassTypes xt sm .

(* 2 *) Definition MessagesAndEventsStateL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XBool ) : Type ; 
 ( XCell ) : Type ; 
 ( ( XHMap XInteger XInteger ) ) : Type ] .

GeneratePruvendoRecord MessagesAndEventsStateL MessagesAndEventsFields .

(* 2 *) Definition ContractL : list Type := 
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
Elpi GeneratePruvendoRecord ContractL ContractFields . 
 Opaque ContractLRecord . 
 
Locate SellArgsStateL.

(* 2 *) Definition LocalStateL : list Type := 
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
Elpi GeneratePruvendoRecord LocalStateL LocalStateFieldsI . 
 Opaque LocalStateLRecord . 

(* 2 *) Definition LedgerStateL : list Type := 
 [ ( FlexClientStateLRecord ) : Type ; 
   ( FlexClientStateLRecord ) : Type ; 
 ( VMStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ] .

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
Transparent ContractLRecord .
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
Definition LedgerLocalState := LocalStateLRecord .
Definition LedgerLocalFields := LocalStateFieldsI.
Definition LedgerLocalPruvendoRecord := LocalStateLPruvendoRecord .
Definition LocalEmbedded := LedgerStateLEmbeddedType _LocalState .
Definition LocalCopyEmbedded := LedgerStateLEmbeddedType _LocalStateCopy.
Definition LocalDefault : XDefault LocalStateStateLRecord := prod_default.
Definition Ledger_LocalState := _LocalState.
Definition Ledger_LocalStateCopy := _LocalStateCopy.
Definition iso_local := _LocalStateIso.
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


Definition LedgerVMStateEmbedded := LedgerStateLEmbeddedType _VMState . 
Definition LedgerVMStateField := _VMState .
Definition isoVMState := _VMStateIso.

Definition LedgerMessagesEmbedded := LedgerStateLEmbeddedType _MessagesAndEvents . 
Definition LedgerMessagesField := _MessagesAndEvents .
Definition isoMessages := _MessagesAndEventsIso.
Definition MessagesAndEvents := MessagesAndEventsStateLRecord .

GenerateLocalStateInstances LocalStateStateL LocalStateFieldsI Build_LocalStateField LocalStateStateLEmbeddedType.
#[global]
 Declare Instance foo : LocalStateField (StateInitStateLRecord * XInteger256).

Definition LocalStateField_XInteger := _intLocalField .
Definition LocalStateField_XBool := _boolLocalField .
Definition LocalStateField_XCell := _cellLocalField .

(* Definition LedgerVMStateEmbedded := LedgerStateLEmbeddedType _VMState . 
Definition LedgerVMStateField := _VMState .
Definition isoVMState := _VMStateIso.

GenerateLocalStateInstances LocalStateStateL LocalStateFieldsI Build_LocalStateField LocalStateStateLEmbeddedType.

Definition LocalStateField_XInteger := _intLocalField .
Definition LocalStateField_XBool := _boolLocalField .
Definition LocalStateField_XCell := _cellLocalField .
 *)

(*
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
Qed . *)

End Ledger .
