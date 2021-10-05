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

Require Import Contracts.Price.ClassTypes.
Require Import Contracts.Price.Interface.

Local Open Scope record. 
Local Open Scope program_scope.
Local Open Scope xlist_scope.


(* 1 *) Inductive MessagesAndEventsFields := | MessagesAndEvents_ι_field_1 | MessagesAndEvents_ι_field_2 | MessagesAndEvents_ι_field_3 | MessagesAndEvents_ι_field_4 .
(* 1 *) Inductive PriceFields := | Price_ι_price_ | Price_ι_sells_amount_ | Price_ι_buys_amount_ | Price_ι_flex_ | Price_ι_min_amount_ | Price_ι_deals_limit_ | Price_ι_notify_addr_ | Price_ι_workchain_id_ | Price_ι_tons_cfg_ | Price_ι_tip3_code_ | Price_ι_tip3cfg_ .
(* 1 *) Inductive LocalStateFieldsI := 
| LocalState_ι_cell 
| LocalState_ι_cellIndex 
| LocalState_ι_bool 
| LocalState_ι_boolIndex 
| LocalState_ι_int 
| LocalState_ι_intIndex 
 .
(* 1 *) Inductive LedgerFieldsI := | Ledger_ι_Contract | Ledger_ι_ContractCopy | Ledger_ι_VMState | Ledger_ι_MessagesAndEvents | Ledger_ι_MessagesAndEventsCopy | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .

 Module PriceClass (xt: XTypesSig) (sm: StateMonadSig) <: ClassSigTVM xt sm. 
 Module Export SolidityNotationsClass := SolidityNotations xt sm. 
 Module Export VMStateModule := VMStateModule xt sm. 
 Module Export ClassTypesModule := ClassTypes xt sm .
Import xt.
Opaque Tip3ConfigStateLRecord .
(* 2 *) Definition MessagesAndEventsStateL : list Type := 
 [ ( XInteger ) : Type ; 
 ( XBool ) : Type ; 
 ( XCell ) : Type ; 
 ( ( XHMap XInteger XInteger ) ) : Type ] .
GeneratePruvendoRecord MessagesAndEventsStateL MessagesAndEventsFields . 
  Opaque MessagesAndEventsStateLRecord . 

(* 2 *) Definition PriceStateL : list Type := 
 [ ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( addr_std_fixedStateLRecord ) : Type ; 
 ( XInteger128 ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( XAddress ) : Type ; 
 ( XInteger8 ) : Type ; 
 ( TonsConfigStateLRecord ) : Type ; 
 ( XCell ) : Type ; 
 ( Tip3ConfigStateLRecord ) : Type ] .
GeneratePruvendoRecord PriceStateL PriceFields . 
 Opaque PriceStateLRecord .

(* 2 *) Definition LocalStateStateL : list Type := 
 [  ( XHMap (string*nat) XCell) : Type ; 
    ( XHMap string nat ) : Type ;
    ( XHMap (string*nat) XBool) : Type ; 
    ( XHMap string nat ) : Type ;
    ( XHMap (string*nat) XInteger) : Type ;
    ( XHMap string nat ) : Type  ] .

GeneratePruvendoRecord LocalStateStateL LocalStateFieldsI . 
 Opaque LocalStateStateLRecord .

(* 2 *) Definition LedgerStateL : list Type := 
 [ ( PriceStateLRecord ) : Type ; 
 ( PriceStateLRecord ) : Type ; 
 ( VMStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( MessagesAndEventsStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ; 
 ( LocalStateStateLRecord ) : Type ] .
Elpi GeneratePruvendoRecord LedgerStateL LedgerFieldsI .

Transparent TickTockStateLRecord .
Transparent StateInitStateLRecord .
Transparent addr_std_fixedStateLRecord .
Transparent TonsConfigStateLRecord .
Transparent OrderRetStateLRecord .
Transparent SellArgsStateLRecord .
Transparent OrderInfoStateLRecord .
Transparent DetailsInfoStateLRecord .
Transparent Tip3ConfigStateLRecord .
Transparent PriceStateLRecord .
Transparent dealerStateLRecord .
Transparent process_retStateLRecord .
Transparent lend_ownership_infoStateLRecord .
Transparent allowance_infoStateLRecord .
Transparent TONTokenWalletStateLRecord .
Transparent OrderInfoXchgStateLRecord .

Transparent VMStateLRecord.
Transparent MessagesAndEventsStateLRecord.
Transparent LocalStateStateLRecord.

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

Declare Instance LocalState_ι_cell : LocalStateField XCell  .  
 
 Declare Instance LocalState_ι_StateInit     : LocalStateField StateInitStateLRecord  .  
 
 Declare Instance LocalState_ι_tplStateInituint256 : LocalStateField ( StateInitStateLRecord * XInteger256 )  .  
 
 Declare Instance LocalState_ι_bool     : LocalStateField XBool  .  
 
 Declare Instance LocalState_ι_uint32     : LocalStateField XInteger32  .  
 
 Declare Instance LocalState_ι_Price     : LocalStateField PriceStateLRecord  .  
 
 Declare Instance LocalState_ι_optuint128     : LocalStateField ( XMaybe XInteger128 )  .  
 
 Declare Instance LocalState_ι_uint128     : LocalStateField XInteger128  .  
 
 Declare Instance LocalState_ι_OrderInfo     : LocalStateField OrderInfoStateLRecord  .  
 
 Declare Instance LocalState_ι_int     : LocalStateField XInteger  .  
 
 Declare Instance LocalState_ι_optpair_unsigned_OrderInfo__     : LocalStateField ( XMaybe (XInteger * OrderInfoStateLRecord) )  .  
 
 Declare Instance LocalState_ι_OrderRet     : LocalStateField OrderRetStateLRecord  .  
 
 Declare Instance LocalState_ι_unsigned     : LocalStateField XInteger  .  
 
 Declare Instance LocalState_ι_dealer     : LocalStateField dealerStateLRecord  .  
 
 Declare Instance LocalState_ι_uint8     : LocalStateField XInteger8  .  
 
 Declare Instance LocalState_ι_TonsConfig     : LocalStateField TonsConfigStateLRecord  .  
 
 Declare Instance LocalState_ι_tplqueue_OrderInfouint128     : LocalStateField ( (XHMap XInteger OrderInfoStateLRecord) * XInteger128 )  .  
 
 Declare Instance LocalState_ι_addr_std_fixed     : LocalStateField addr_std_fixedStateLRecord  .  
 
 Declare Instance LocalState_ι_Grams     : LocalStateField XInteger256 (* Grams *)  .  
 
 Declare Instance LocalState_ι_SellArgs     : LocalStateField SellArgsStateLRecord  .  
 
 Declare Instance LocalState_ι_address     : LocalStateField XAddress  .  
 
 Declare Instance LocalState_ι_DetailsInfo     : LocalStateField DetailsInfoStateLRecord  .  
 
 Declare Instance LocalState_ι_dict_arrayOrderInfo     : LocalStateField ( XHMap XInteger OrderInfoStateLRecord )  .  
 
 Declare Instance LocalState_ι_optaddress     : LocalStateField ( XMaybe XAddress )  .  
 
 Declare Instance LocalState_ι_TONTokenWallet     : LocalStateField TONTokenWalletStateLRecord  .  
 
 Declare Instance LocalState_ι_tpladdressGrams     : LocalStateField ( XAddress * XInteger256 (* Grams *) )  .  
 
 Declare Instance LocalState_ι_TvmSlice     : LocalStateField XSlice  .  
 
 Declare Instance LocalState_ι_optOrderRet     : LocalStateField ( XMaybe OrderRetStateLRecord )  .  

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

Lemma PriceFields_noeq : forall (f1 f2:  PriceFields ) 
         (v2: field_type f2) (r :  PriceStateLRecord  ) ,  
f1 <> f2 -> 
f1 {$$ r with f2 := v2 $$} = f1 r.
Proof.
  intros.
  destruct f1; destruct f2; 
  (revert r;     
               apply (countable_prop_proof (T:= PriceStateLRecord ));
               cbv;
               first [reflexivity| contradiction]).
Qed .

Lemma LocalStateFields_noeq : forall (f1 f2:  LocalStateFieldsI ) 
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
Qed .

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

End PriceClass .
