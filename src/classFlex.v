
 Require Import Coq.Program.Basics. 
 Require Import Coq.Logic.FunctionalExtensionality. 
 Require Import Coq.Program.Combinators. 
 Require Import FinProof.ProgrammingWith. 
 Require Import FinProof.Types.IsoTypes. 
 
 Require Import String. 
 
 Local Open Scope record. 
 Local Open Scope program_scope. 
 Require Import FinProof.Common. 
 Require Import FinProof.MonadTransformers21. 
 Require Import FinProof.StateMonad21. 
 
 Require Import UMLang.SolidityNotations2. 
 Require Import UMLang.SML_NG24. 
 
 Section RecordsDefinitions. 
 
 Set Implicit Arguments. 
 Unset Strict Implicit. 
 Set Contextual Implicit. 
 Set Maximal Implicit Insertion. 
 
 Variables I I8 I16 I32 I64 I128 I256 : Type. 
 Variables A B C S Bs : Type. 
 Variables L M H Q R : Type -> Type. (* H - handle<type> , Q - queue<type> , R - ref<type> *) 
 Variables HM P : Type -> Type -> Type. 
 Variables T G Sl Bt Bi IFLeXNotifyPtrP : Type. 
 
 (* Variables TipAccountP PadawanP ProposalResolverP : Type . *) 
 

(* 1 *) Inductive TonsConfigFields := | TonsConfig_ι_transfer_tip3 | TonsConfig_ι_return_ownership | TonsConfig_ι_trading_pair_deploy | TonsConfig_ι_order_answer | TonsConfig_ι_process_queue | TonsConfig_ι_send_notify .
(* 2 *) Definition TonsConfigP := 
 ( I128 * 
 I128 * 
 I128 * 
 I128 * 
 I128 * 
 I128 )%type .
(* 1 *) Inductive addr_std_fixedFields := | addr_std_fixed_ι_workchain_id | addr_std_fixed_ι_address .
(* 2 *) Definition addr_std_fixedP := 
 ( I8 * 
 I256 )%type .
(* 1 *) Inductive OrderInfoFields := | OrderInfo_ι_original_amount | OrderInfo_ι_amount | OrderInfo_ι_account | OrderInfo_ι_tip3_wallet | OrderInfo_ι_client_addr | OrderInfo_ι_order_finish_time .
(* 2 *) Definition OrderInfoP := 
 ( I128 * 
 I128 * 
 I128 * 
 addr_std_fixedP * 
 addr_std_fixedP * 
 I32 )%type .
(* 1 *) Inductive OrderRetFields := | OrderRet_ι_err_code | OrderRet_ι_processed | OrderRet_ι_enqueued .
(* 2 *) Definition OrderRetP := 
 ( I32 * 
 I128 * 
 I128 )%type .
(* 1 *) Inductive dealerFields := | dealer_ι_tip3root_ | dealer_ι_notify_addr_ | dealer_ι_price_ | dealer_ι_deals_limit_ | dealer_ι_tons_cfg_ | dealer_ι_sells_amount_ | dealer_ι_buys_amount_ .
(* 2 *) Definition dealerP := 
 ( A * 
 (* IFLeXNotifyPtrP *) I * 
 I128 * 
 I * 
 TonsConfigP * 
 I128 * 
 I128 )%type .
(* 1 *) Inductive FLeXSellArgsAddrsFields := | FLeXSellArgsAddrs_ι_my_tip3_addr | FLeXSellArgsAddrs_ι_receive_wallet .
(* 2 *) Definition FLeXSellArgsAddrsP := 
 ( A * 
 A )%type .
(* 1 *) Inductive Tip3ConfigFields := | Tip3Config_ι_name | Tip3Config_ι_symbol | Tip3Config_ι_decimals | Tip3Config_ι_root_public_key | Tip3Config_ι_root_address .
(* 2 *) Definition Tip3ConfigP := 
 ( S * 
 S * 
 I8 * 
 I256 * 
 A )%type .
(* 1 *) Inductive FLeXSellArgsFields := | FLeXSellArgs_ι_price | FLeXSellArgs_ι_amount | FLeXSellArgs_ι_lend_finish_time | FLeXSellArgs_ι_min_amount | FLeXSellArgs_ι_deals_limit | FLeXSellArgs_ι_tons_value | FLeXSellArgs_ι_price_code | FLeXSellArgs_ι_tip3_code .
(* 2 *) Definition FLeXSellArgsP := 
 ( I128 * 
 I128 * 
 I32 * 
 I128 * 
 I8 * 
 I128 * 
 C * 
 C )%type .
(* 1 *) Inductive FLeXBuyArgsFields := | FLeXBuyArgs_ι_price | FLeXBuyArgs_ι_amount | FLeXBuyArgs_ι_order_finish_time | FLeXBuyArgs_ι_min_amount | FLeXBuyArgs_ι_deals_limit | FLeXBuyArgs_ι_deploy_value | FLeXBuyArgs_ι_price_code | FLeXBuyArgs_ι_my_tip3_addr | FLeXBuyArgs_ι_tip3_code .
(* 2 *) Definition FLeXBuyArgsP := 
 ( I128 * 
 I128 * 
 I32 * 
 I128 * 
 I8 * 
 I128 * 
 C * 
 A * 
 C )%type .
(* 1 *) Inductive FLeXXchgArgsFields := | FLeXXchgArgs_ι_sell | FLeXXchgArgs_ι_price_num | FLeXXchgArgs_ι_price_denum | FLeXXchgArgs_ι_amount | FLeXXchgArgs_ι_lend_amount | FLeXXchgArgs_ι_lend_finish_time | FLeXXchgArgs_ι_min_amount | FLeXXchgArgs_ι_deals_limit | FLeXXchgArgs_ι_tons_value | FLeXXchgArgs_ι_xchg_price_code | FLeXXchgArgs_ι_tip3_code .
(* 2 *) Definition FLeXXchgArgsP := 
 ( B * 
 I128 * 
 I128 * 
 I128 * 
 I128 * 
 I32 * 
 I128 * 
 I8 * 
 I128 * 
 C * 
 C )%type .
(* 1 *) Inductive FLeXCancelArgsFields := | FLeXCancelArgs_ι_price | FLeXCancelArgs_ι_min_amount | FLeXCancelArgs_ι_deals_limit | FLeXCancelArgs_ι_value | FLeXCancelArgs_ι_price_code | FLeXCancelArgs_ι_tip3_code .
(* 2 *) Definition FLeXCancelArgsP := 
 ( I128 * 
 I128 * 
 I8 * 
 I128 * 
 C * 
 C )%type .
(* 1 *) Inductive FLeXXchgCancelArgsFields := | FLeXXchgCancelArgs_ι_sell | FLeXXchgCancelArgs_ι_price_num | FLeXXchgCancelArgs_ι_price_denum | FLeXXchgCancelArgs_ι_min_amount | FLeXXchgCancelArgs_ι_deals_limit | FLeXXchgCancelArgs_ι_value | FLeXXchgCancelArgs_ι_xchg_price_code | FLeXXchgCancelArgs_ι_tip3_code .
(* 2 *) Definition FLeXXchgCancelArgsP := 
 ( B * 
 I128 * 
 I128 * 
 I128 * 
 I8 * 
 I128 * 
 C * 
 C )%type .
(* 1 *) Inductive DFLeXClientFields := | DFLeXClient_ι_owner_ | DFLeXClient_ι_trading_pair_code_ | DFLeXClient_ι_xchg_pair_code_ | DFLeXClient_ι_workchain_id_ | DFLeXClient_ι_tons_cfg_ | DFLeXClient_ι_flex_ | DFLeXClient_ι_notify_addr_ .
(* 2 *) Definition DFLeXClientP := 
 ( I256 * 
 C * 
 C * 
 I8 * 
 TonsConfigP * 
 A * 
 A )%type .
(* 1 *) Inductive DFLeXFields := | DFLeX_ι_deployer_pubkey_ | DFLeX_ι_tons_cfg_ | DFLeX_ι_min_amount_ | DFLeX_ι_deals_limit_ | DFLeX_ι_notify_addr_ .
(* 2 *) Definition DFLeXP := 
 ( I256 * 
 TonsConfigP * 
 I128 * 
 I8 * 
 A )%type .
(* 1 *) Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_buys_amount .
(* 2 *) Definition process_retP := 
 ( I128 * 
 I128 )%type .
(* 1 *) Inductive SellArgsFields := | SellArgs_ι_amount | SellArgs_ι_receive_wallet .
(* 2 *) Definition SellArgsP := 
 ( I128 * 
 addr_std_fixedP )%type .
(* 1 *) Inductive DetailsInfoFields := | DetailsInfo_ι_price | DetailsInfo_ι_min_amount | DetailsInfo_ι_sell_amount | DetailsInfo_ι_buy_amount .
(* 2 *) Definition DetailsInfoP := 
 ( I128 * 
 I128 * 
 I128 * 
 I128 )%type .
(* 1 *) Inductive DPriceFields := | DPrice_ι_price_ | DPrice_ι_sells_amount_ | DPrice_ι_buys_amount_ | DPrice_ι_flex_ | DPrice_ι_min_amount_ | DPrice_ι_deals_limit_ | DPrice_ι_notify_addr_ | DPrice_ι_workchain_id_ | DPrice_ι_tons_cfg_ | DPrice_ι_tip3_code_ | DPrice_ι_tip3cfg_ .
(* 2 *) Definition DPriceP := 
 ( I128 * 
 I128 * 
 I128 * 
 addr_std_fixedP * 
 I128 * 
 I8 * 
 (* IFLeXNotifyPtrP *) I8 * 
 I8 * 
 TonsConfigP * 
 C * 
 Tip3ConfigP )%type .
(* 1 *) Inductive RationalPriceFields := | RationalPrice_ι_num | RationalPrice_ι_denum .
(* 2 *) Definition RationalPriceP := 
 ( I128 * 
 I128 )%type .
(* 1 *) Inductive PayloadArgsFields := | PayloadArgs_ι_sell | PayloadArgs_ι_amount | PayloadArgs_ι_receive_tip3_wallet | PayloadArgs_ι_client_addr .
(* 2 *) Definition PayloadArgsP := 
 ( B * 
 I128 * 
 addr_std_fixedP * 
 addr_std_fixedP )%type .
(* 1 *) Inductive OrderInfoXchgFields := | OrderInfoXchg_ι_original_amount | OrderInfoXchg_ι_amount | OrderInfoXchg_ι_account | OrderInfoXchg_ι_tip3_wallet_provide | OrderInfoXchg_ι_tip3_wallet_receive | OrderInfoXchg_ι_client_addr | OrderInfoXchg_ι_order_finish_time .
(* 2 *) Definition OrderInfoXchgP := 
 ( I128 * 
 I128 * 
 I128 * 
 addr_std_fixedP * 
 addr_std_fixedP * 
 addr_std_fixedP * 
 I32 )%type .
(* 1 *) Inductive DetailsInfoXchgFields := | DetailsInfoXchg_ι_price_num | DetailsInfoXchg_ι_price_denum | DetailsInfoXchg_ι_min_amount | DetailsInfoXchg_ι_sell_amount | DetailsInfoXchg_ι_buy_amount .
(* 2 *) Definition DetailsInfoXchgP := 
 ( I128 * 
 I128 * 
 I128 * 
 I128 * 
 I128 )%type .
(* 1 *) Inductive DPriceXchgFields := | DPriceXchg_ι_price_ | DPriceXchg_ι_sells_amount_ | DPriceXchg_ι_buys_amount_ | DPriceXchg_ι_flex_ | DPriceXchg_ι_min_amount_ | DPriceXchg_ι_deals_limit_ | DPriceXchg_ι_notify_addr_ | DPriceXchg_ι_workchain_id_ | DPriceXchg_ι_tons_cfg_ | DPriceXchg_ι_tip3_code_ | DPriceXchg_ι_major_tip3cfg_ | DPriceXchg_ι_minor_tip3cfg_ .
(* 2 *) Definition DPriceXchgP :=
 ( RationalPriceP * 
 I128 * 
 I128 * 
 addr_std_fixedP * 
 I128 * 
 I8 * 
 (* IFLeXNotifyPtrP *) I8 * 
 I8 * 
 TonsConfigP * 
 C * 
 Tip3ConfigP * 
 Tip3ConfigP )%type .
(* 1 *) Inductive DTradingPairFields := | DTradingPair_ι_flex_addr_ | DTradingPair_ι_tip3_root_ | DTradingPair_ι_deploy_value_ .
(* 2 *) Definition DTradingPairP := 
 ( A * 
 A * 
 I128 )%type .
(* 1 *) Inductive DXchgPairFields := | DXchgPair_ι_flex_addr_ | DXchgPair_ι_tip3_major_root_ | DXchgPair_ι_tip3_minor_root_ | DXchgPair_ι_deploy_value_ .
(* 2 *) Definition DXchgPairP := 
 ( A * 
 A * 
 A * 
 I128 )%type .
(* 1 *) Inductive VMCommitFields := | VMCommit_ι_dealer .
(* 2 *) Definition VMCommitP := 
 ( dealerP )%type . 
(* 1 *) Inductive LocalStateFields := 
| LocalState_ι_uint256 
| LocalState_ι_Grams
.
(* 2 *) Definition LocalStateP := 
 ( HM string I256  * 
 HM string G )%type .
(* 1 *) Inductive LedgerFields := | Ledger_ι_dealer | Ledger_ι_VMCommit | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .
(* 2 *) Definition LedgerP := 
 ( dealerP * 
 VMCommitP * 
 LocalStateP * 
 LocalStateP )%type .
Notation "'{$$' r 'With' y ':=' v '$$}'" := (@setPruvendoRecord _ _ _ y v r) : struct_scope.

End RecordsDefinitions .

 Require Import UMLang.ProofEnvironment2. 
 
 Module LedgerClass (xt: XTypesSig) (sm: StateMonadSig) . 
 
 Module Export SMLClass := SML xt sm . 
 Export SolidityNotationsSML. 
 (* Module Import SolidityNotationsClass := SolidityNotationsSML xt sm. *) 
 
 Existing Instance monadStateS. 
 Existing Instance monadStateStateS. 
 
 
 Definition IFLeXNotifyPtrP := XInteger . 

Definition TonsConfig := @ TonsConfigP
XInteger128
.
Definition addr_std_fixed := @ addr_std_fixedP
XInteger8 XInteger256
.
Definition OrderInfo := @ OrderInfoP
XInteger8 XInteger32 XInteger128 XInteger256
.
Definition OrderRet := @ OrderRetP
XInteger32 XInteger128
.
Print dealerP.
Definition dealer := @ dealerP
XInteger XInteger128 XAddress
.
Definition FLeXSellArgsAddrs := @ FLeXSellArgsAddrsP
XAddress
.
Definition Tip3Config := @ Tip3ConfigP
XInteger8 XInteger256 XAddress XString
.
Definition FLeXSellArgs := @ FLeXSellArgsP
XInteger8 XInteger32 XInteger128 TvmCell
.
Definition FLeXBuyArgs := @ FLeXBuyArgsP
XInteger8 XInteger32 XInteger128 XAddress TvmCell
.
Definition FLeXXchgArgs := @ FLeXXchgArgsP
XInteger8 XInteger32 XInteger128 XBool TvmCell
.
Definition FLeXCancelArgs := @ FLeXCancelArgsP
XInteger8 XInteger128 TvmCell
.
Definition FLeXXchgCancelArgs := @ FLeXXchgCancelArgsP
XInteger8 XInteger128 XBool TvmCell
.
Definition DFLeXClient := @ DFLeXClientP
XInteger8 XInteger128 XInteger256 XAddress TvmCell
.
Definition DFLeX := @ DFLeXP
XInteger8 XInteger128 XInteger256 XAddress
.
Definition process_ret := @ process_retP
XInteger128
.
Definition SellArgs := @ SellArgsP
XInteger8 XInteger128 XInteger256
.
Definition DetailsInfo := @ DetailsInfoP
XInteger128
.
Definition DPrice := @ DPriceP
XInteger8 XInteger128 XInteger256 XAddress TvmCell XString
.
Definition RationalPrice := @ RationalPriceP
XInteger128
.
Definition PayloadArgs := @ PayloadArgsP
XInteger8 XInteger128 XInteger256 XBool
.
Definition OrderInfoXchg := @ OrderInfoXchgP
XInteger8 XInteger32 XInteger128 XInteger256
.
Definition DetailsInfoXchg := @ DetailsInfoXchgP
XInteger128
.
Definition DPriceXchg := @ DPriceXchgP
XInteger8 XInteger128 XInteger256 XAddress TvmCell XString
.
Definition DTradingPair := @ DTradingPairP
XInteger128 XAddress
.
Definition DXchgPair := @ DXchgPairP
XInteger128 XAddress
.
Definition VMCommit := @ VMCommitP
XInteger XInteger128 XAddress
.

Print LocalStateP.
Definition LocalState := @ LocalStateP
XInteger256 XHMap XInteger
.
Print LedgerP.
Definition Ledger := @ LedgerP
XInteger XInteger128 XInteger256 XAddress XHMap XInteger 
.
Global Instance TonsConfig_default : XDefault TonsConfig := { 
  	 default := ( default , default , default , default , default , default ) } .
Global Instance addr_std_fixed_default : XDefault addr_std_fixed := { 
  	 default := ( default , default ) } .
Global Instance OrderInfo_default : XDefault OrderInfo := { 
  	 default := ( default , default , default , default , default , default ) } .
Global Instance OrderRet_default : XDefault OrderRet := { 
  	 default := ( default , default , default ) } .
Global Instance dealer_default : XDefault dealer := {
  	 default := ( default , default , default , default , default , default , default ) } .
Global Instance FLeXSellArgsAddrs_default : XDefault FLeXSellArgsAddrs := { 
  	 default := ( default , default ) } .
Global Instance Tip3Config_default : XDefault Tip3Config := { 
  	 default := ( default , default , default , default , default ) } .
Global Instance FLeXSellArgs_default : XDefault FLeXSellArgs := { 
  	 default := ( default , default , default , default , default , default , default , default ) } .
Global Instance FLeXBuyArgs_default : XDefault FLeXBuyArgs := { 
  	 default := ( default , default , default , default , default , default , default , default , default ) } .

Global Instance FLeXXchgArgs_default : XDefault FLeXXchgArgs := { 
  	 default := ( default , default , default , default , default , default , default , default , default , default , default ) } .
Global Instance FLeXCancelArgs_default : XDefault FLeXCancelArgs := { 
  	 default := ( default , default , default , default , default , default ) } .
Global Instance FLeXXchgCancelArgs_default : XDefault FLeXXchgCancelArgs := { 
  	 default := ( default , default , default , default , default , default , default , default ) } .
Global Instance DFLeXClient_default : XDefault DFLeXClient := { 
  	 default := ( default , default , default , default , default , default , default ) } .
Global Instance DFLeX_default : XDefault DFLeX := { 
  	 default := ( default , default , default , default , default ) } .
Global Instance process_ret_default : XDefault process_ret := { 
  	 default := ( default , default ) } .
Global Instance SellArgs_default : XDefault SellArgs := { 
  	 default := ( default , default ) } .
Global Instance DetailsInfo_default : XDefault DetailsInfo := { 
  	 default := ( default , default , default , default ) } .
Global Instance DPrice_default : XDefault DPrice := {
  	 default := ( default , default , default , default , default , default , default , default , default , default , default ) } .
Global Instance RationalPrice_default : XDefault RationalPrice := { 
  	 default := ( default , default ) } .
Global Instance PayloadArgs_default : XDefault PayloadArgs := { 
  	 default := ( default , default , default , default ) } .
Global Instance OrderInfoXchg_default : XDefault OrderInfoXchg := { 
  	 default := ( default , default , default , default , default , default , default ) } .
Global Instance DetailsInfoXchg_default : XDefault DetailsInfoXchg := { 
  	 default := ( default , default , default , default , default ) } .
Global Instance DPriceXchg_default : XDefault DPriceXchg := { 
  	 default := ( default , default , default , default , default , default , default , default , default , default , default , default ) } .
Global Instance DTradingPair_default : XDefault DTradingPair := { 
  	 default := ( default , default , default ) } .
Global Instance DXchgPair_default : XDefault DXchgPair := { 
  	 default := ( default , default , default , default ) } .
Global Instance VMCommit_default : XDefault VMCommit := { 
  	 default := ( default ) } .
Global Instance LocalState_default : XDefault LocalState := { 
  	 default := ( default , default ) } .
Global Instance Ledger_default : XDefault Ledger := { 
  	 default := ( default , default , default , default ) } .

 Unset Implicit Arguments. 
 Set Strict Implicit. 
 Unset Contextual Implicit. 
 Unset Maximal Implicit Insertion. 

Notation " 'fst0' x " := ( x ) (at level 60, right associativity).
Notation " 'fst1' x " := ( fst ( fst0 x ) ) (at level 60, right associativity).
Notation " 'fst2' x " := ( fst ( fst1 x ) ) (at level 60, right associativity).
Notation " 'fst3' x " := ( fst ( fst2 x ) ) (at level 60, right associativity).
Notation " 'fst4' x " := ( fst ( fst3 x ) ) (at level 60, right associativity).
Notation " 'fst5' x " := ( fst ( fst4 x ) ) (at level 60, right associativity).
Notation " 'fst6' x " := ( fst ( fst5 x ) ) (at level 60, right associativity).
Notation " 'fst7' x " := ( fst ( fst6 x ) ) (at level 60, right associativity).
Notation " 'fst8' x " := ( fst ( fst7 x ) ) (at level 60, right associativity).
Notation " 'fst9' x " := ( fst ( fst8 x ) ) (at level 60, right associativity).
Notation " 'fst10' x " := ( fst ( fst9 x ) ) (at level 60, right associativity).
Notation " 'fst11' x " := ( fst ( fst10 x ) ) (at level 60, right associativity).
Notation " 'fst12' x " := ( fst ( fst11 x ) ) (at level 60, right associativity).
Notation " 'fst13' x " := ( fst ( fst12 x ) ) (at level 60, right associativity).
Notation " 'fst14' x " := ( fst ( fst13 x ) ) (at level 60, right associativity).
Notation " 'fst15' x " := ( fst ( fst14 x ) ) (at level 60, right associativity).
Notation " 'fst16' x " := ( fst ( fst15 x ) ) (at level 60, right associativity).
Notation " 'fst17' x " := ( fst ( fst16 x ) ) (at level 60, right associativity).
Notation " 'fst18' x " := ( fst ( fst17 x ) ) (at level 60, right associativity).
Notation " 'fst19' x " := ( fst ( fst18 x ) ) (at level 60, right associativity).
Notation " 'fst20' x " := ( fst ( fst19 x ) ) (at level 60, right associativity).
Notation " 'fst21' x " := ( fst ( fst20 x ) ) (at level 60, right associativity).
Notation " 'fst22' x " := ( fst ( fst21 x ) ) (at level 60, right associativity).
Notation " 'fst23' x " := ( fst ( fst22 x ) ) (at level 60, right associativity).
Notation " 'fst24' x " := ( fst ( fst23 x ) ) (at level 60, right associativity).
Notation " 'fst25' x " := ( fst ( fst24 x ) ) (at level 60, right associativity).
Notation " 'fst26' x " := ( fst ( fst25 x ) ) (at level 60, right associativity).
Notation " 'fst27' x " := ( fst ( fst26 x ) ) (at level 60, right associativity).
Notation " 'fst28' x " := ( fst ( fst27 x ) ) (at level 60, right associativity).
Notation " 'fst29' x " := ( fst ( fst28 x ) ) (at level 60, right associativity).
Notation " 'fst30' x " := ( fst ( fst29 x ) ) (at level 60, right associativity).
Notation " 'fst31' x " := ( fst ( fst30 x ) ) (at level 60, right associativity).
Notation " 'fst32' x " := ( fst ( fst31 x ) ) (at level 60, right associativity).
Notation " 'fst33' x " := ( fst ( fst32 x ) ) (at level 60, right associativity).
Notation " 'fst34' x " := ( fst ( fst33 x ) ) (at level 60, right associativity).
Notation " 'fst35' x " := ( fst ( fst34 x ) ) (at level 60, right associativity).
Notation " 'fst36' x " := ( fst ( fst35 x ) ) (at level 60, right associativity).
Notation " 'fst37' x " := ( fst ( fst36 x ) ) (at level 60, right associativity).
Notation " 'fst38' x " := ( fst ( fst37 x ) ) (at level 60, right associativity).
Notation " 'fst39' x " := ( fst ( fst38 x ) ) (at level 60, right associativity).
Notation " 'fst40' x " := ( fst ( fst39 x ) ) (at level 60, right associativity).
(* 3 *) Definition TonsConfig_field_type f : Type :=  
match f with | TonsConfig_ι_transfer_tip3 => XInteger128 | TonsConfig_ι_return_ownership => XInteger128 | TonsConfig_ι_trading_pair_deploy => XInteger128 | TonsConfig_ι_order_answer => XInteger128 | TonsConfig_ι_process_queue => XInteger128 | TonsConfig_ι_send_notify => XInteger128 end .
(* 4 *) Definition TonsConfig_get (f: TonsConfigFields )(r: TonsConfig ) :  TonsConfig_field_type f := 
 match f with | TonsConfig_ι_transfer_tip3 => fst5 r 
 | TonsConfig_ι_return_ownership => snd ( fst4 r ) 
 | TonsConfig_ι_trading_pair_deploy => snd ( fst3 r ) 
 | TonsConfig_ι_order_answer => snd ( fst2 r ) 
 | TonsConfig_ι_process_queue => snd ( fst1 r ) 
 | TonsConfig_ι_send_notify => snd r 
 end .
(* 5 *) Coercion TonsConfig_get : TonsConfigFields >-> Funclass .
(* 6 *) Definition TonsConfig_set (f: TonsConfigFields ) 
(v: TonsConfig_field_type f) (r: TonsConfig ): TonsConfig  :=
  match f, v with | TonsConfig_ι_transfer_tip3 , v' => ( v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_return_ownership , v' => ( fst5 r , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_trading_pair_deploy , v' => ( fst5 r , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_order_answer , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | TonsConfig_ι_process_queue , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | TonsConfig_ι_send_notify , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance TonsConfig_PruvendoRecord : PruvendoRecord TonsConfig TonsConfigFields :=
{
  field_type := TonsConfig_field_type; 
  getPruvendoRecord := @TonsConfig_get ;
  setPruvendoRecord := @TonsConfig_set ;
} .
(* 3 *) Definition addr_std_fixed_field_type f : Type :=  
match f with | addr_std_fixed_ι_workchain_id => XInteger8 | addr_std_fixed_ι_address => XInteger256 end .
(* 4 *) Definition addr_std_fixed_get (f: addr_std_fixedFields )(r: addr_std_fixed ) :  addr_std_fixed_field_type f := 
 match f with | addr_std_fixed_ι_workchain_id => fst1 r 
 | addr_std_fixed_ι_address => snd r 
 end .
(* 5 *) Coercion addr_std_fixed_get : addr_std_fixedFields >-> Funclass .
(* 6 *) Definition addr_std_fixed_set (f: addr_std_fixedFields ) 
(v: addr_std_fixed_field_type f) (r: addr_std_fixed ): addr_std_fixed  :=
  match f, v with | addr_std_fixed_ι_workchain_id , v' => ( v' , snd r ) 
 | addr_std_fixed_ι_address , v' => ( fst1 r , v' ) 
 end .
(* 7 *) Global Instance addr_std_fixed_PruvendoRecord : PruvendoRecord addr_std_fixed addr_std_fixedFields :=
{
  field_type := addr_std_fixed_field_type; 
  getPruvendoRecord := @addr_std_fixed_get ;
  setPruvendoRecord := @addr_std_fixed_set ;
} .
(* 3 *) Definition OrderInfo_field_type f : Type :=  
match f with | OrderInfo_ι_original_amount => XInteger128 | OrderInfo_ι_amount => XInteger128 | OrderInfo_ι_account => XInteger128 | OrderInfo_ι_tip3_wallet => addr_std_fixed | OrderInfo_ι_client_addr => addr_std_fixed | OrderInfo_ι_order_finish_time => XInteger32 end .
(* 4 *) Definition OrderInfo_get (f: OrderInfoFields )(r: OrderInfo ) :  OrderInfo_field_type f := 
 match f with | OrderInfo_ι_original_amount => fst5 r 
 | OrderInfo_ι_amount => snd ( fst4 r ) 
 | OrderInfo_ι_account => snd ( fst3 r ) 
 | OrderInfo_ι_tip3_wallet => snd ( fst2 r ) 
 | OrderInfo_ι_client_addr => snd ( fst1 r ) 
 | OrderInfo_ι_order_finish_time => snd r 
 end .
(* 5 *) Coercion OrderInfo_get : OrderInfoFields >-> Funclass .
(* 6 *) Definition OrderInfo_set (f: OrderInfoFields ) 
(v: OrderInfo_field_type f) (r: OrderInfo ): OrderInfo  :=
  match f, v with | OrderInfo_ι_original_amount , v' => ( v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | OrderInfo_ι_amount , v' => ( fst5 r , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | OrderInfo_ι_account , v' => ( fst5 r , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | OrderInfo_ι_tip3_wallet , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | OrderInfo_ι_client_addr , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | OrderInfo_ι_order_finish_time , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance OrderInfo_PruvendoRecord : PruvendoRecord OrderInfo OrderInfoFields :=
{
  field_type := OrderInfo_field_type; 
  getPruvendoRecord := @OrderInfo_get ;
  setPruvendoRecord := @OrderInfo_set ;
} .
(* 3 *) Definition OrderRet_field_type f : Type :=  
match f with | OrderRet_ι_err_code => XInteger32 | OrderRet_ι_processed => XInteger128 | OrderRet_ι_enqueued => XInteger128 end .
(* 4 *) Definition OrderRet_get (f: OrderRetFields )(r: OrderRet ) :  OrderRet_field_type f := 
 match f with | OrderRet_ι_err_code => fst2 r 
 | OrderRet_ι_processed => snd ( fst1 r ) 
 | OrderRet_ι_enqueued => snd r 
 end .
(* 5 *) Coercion OrderRet_get : OrderRetFields >-> Funclass .
(* 6 *) Definition OrderRet_set (f: OrderRetFields ) 
(v: OrderRet_field_type f) (r: OrderRet ): OrderRet  :=
  match f, v with | OrderRet_ι_err_code , v' => ( v' , snd ( fst1 r ) , snd r ) 
 | OrderRet_ι_processed , v' => ( fst2 r , v' , snd r ) 
 | OrderRet_ι_enqueued , v' => ( fst2 r , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance OrderRet_PruvendoRecord : PruvendoRecord OrderRet OrderRetFields :=
{
  field_type := OrderRet_field_type; 
  getPruvendoRecord := @OrderRet_get ;
  setPruvendoRecord := @OrderRet_set ;
} .
(* 3 *) Definition dealer_field_type f : Type :=  
match f with | dealer_ι_tip3root_ => XAddress 
| dealer_ι_notify_addr_ => XInteger (* IFLeXNotifyPtr *) 
| dealer_ι_price_ => XInteger128 
| dealer_ι_deals_limit_ => XInteger 
| dealer_ι_tons_cfg_ => TonsConfig 
| dealer_ι_sells_amount_ => XInteger128 
| dealer_ι_buys_amount_ => XInteger128 
end .
(* 4 *) Definition dealer_get (f: dealerFields )(r: dealer ) :  dealer_field_type f := 
 match f with | dealer_ι_tip3root_ => fst6 r 
 | dealer_ι_notify_addr_ => snd ( fst5 r ) 
 | dealer_ι_price_ => snd ( fst4 r ) 
 | dealer_ι_deals_limit_ => snd ( fst3 r ) 
 | dealer_ι_tons_cfg_ => snd ( fst2 r ) 
 | dealer_ι_sells_amount_ => snd ( fst1 r ) 
 | dealer_ι_buys_amount_ => snd r 
 end .
(* 5 *) Coercion dealer_get : dealerFields >-> Funclass .
(* 6 *) Definition dealer_set (f: dealerFields ) 
(v: dealer_field_type f) (r: dealer ): dealer  :=
  match f, v with | dealer_ι_tip3root_ , v' => ( v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_notify_addr_ , v' => ( fst6 r , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_price_ , v' => ( fst6 r , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_deals_limit_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_tons_cfg_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | dealer_ι_sells_amount_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | dealer_ι_buys_amount_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance dealer_PruvendoRecord : PruvendoRecord dealer dealerFields :=
{
  field_type := dealer_field_type; 
  getPruvendoRecord := @dealer_get ;
  setPruvendoRecord := @dealer_set ;
} .
(* 3 *) Definition FLeXSellArgsAddrs_field_type f : Type :=  
match f with | FLeXSellArgsAddrs_ι_my_tip3_addr => XAddress | FLeXSellArgsAddrs_ι_receive_wallet => XAddress end .
(* 4 *) Definition FLeXSellArgsAddrs_get (f: FLeXSellArgsAddrsFields )(r: FLeXSellArgsAddrs ) :  FLeXSellArgsAddrs_field_type f := 
 match f with | FLeXSellArgsAddrs_ι_my_tip3_addr => fst1 r 
 | FLeXSellArgsAddrs_ι_receive_wallet => snd r 
 end .
(* 5 *) Coercion FLeXSellArgsAddrs_get : FLeXSellArgsAddrsFields >-> Funclass .
(* 6 *) Definition FLeXSellArgsAddrs_set (f: FLeXSellArgsAddrsFields ) 
(v: FLeXSellArgsAddrs_field_type f) (r: FLeXSellArgsAddrs ): FLeXSellArgsAddrs  :=
  match f, v with | FLeXSellArgsAddrs_ι_my_tip3_addr , v' => ( v' , snd r ) 
 | FLeXSellArgsAddrs_ι_receive_wallet , v' => ( fst1 r , v' ) 
 end .
(* 7 *) Global Instance FLeXSellArgsAddrs_PruvendoRecord : PruvendoRecord FLeXSellArgsAddrs FLeXSellArgsAddrsFields :=
{
  field_type := FLeXSellArgsAddrs_field_type; 
  getPruvendoRecord := @FLeXSellArgsAddrs_get ;
  setPruvendoRecord := @FLeXSellArgsAddrs_set ;
} .
(* 3 *) Definition Tip3Config_field_type f : Type :=  
match f with | Tip3Config_ι_name => XString | Tip3Config_ι_symbol => XString | Tip3Config_ι_decimals => XInteger8 | Tip3Config_ι_root_public_key => XInteger256 | Tip3Config_ι_root_address => XAddress end .
(* 4 *) Definition Tip3Config_get (f: Tip3ConfigFields )(r: Tip3Config ) :  Tip3Config_field_type f := 
 match f with | Tip3Config_ι_name => fst4 r 
 | Tip3Config_ι_symbol => snd ( fst3 r ) 
 | Tip3Config_ι_decimals => snd ( fst2 r ) 
 | Tip3Config_ι_root_public_key => snd ( fst1 r ) 
 | Tip3Config_ι_root_address => snd r 
 end .
(* 5 *) Coercion Tip3Config_get : Tip3ConfigFields >-> Funclass .
(* 6 *) Definition Tip3Config_set (f: Tip3ConfigFields ) 
(v: Tip3Config_field_type f) (r: Tip3Config ): Tip3Config  :=
  match f, v with | Tip3Config_ι_name , v' => ( v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Tip3Config_ι_symbol , v' => ( fst4 r , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Tip3Config_ι_decimals , v' => ( fst4 r , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | Tip3Config_ι_root_public_key , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | Tip3Config_ι_root_address , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance Tip3Config_PruvendoRecord : PruvendoRecord Tip3Config Tip3ConfigFields :=
{
  field_type := Tip3Config_field_type; 
  getPruvendoRecord := @Tip3Config_get ;
  setPruvendoRecord := @Tip3Config_set ;
} .
(* 3 *) Definition FLeXSellArgs_field_type f : Type :=  
match f with | FLeXSellArgs_ι_price => XInteger128 | FLeXSellArgs_ι_amount => XInteger128 | FLeXSellArgs_ι_lend_finish_time => XInteger32 | FLeXSellArgs_ι_min_amount => XInteger128 | FLeXSellArgs_ι_deals_limit => XInteger8 | FLeXSellArgs_ι_tons_value => XInteger128 | FLeXSellArgs_ι_price_code => TvmCell | FLeXSellArgs_ι_tip3_code => TvmCell end .
(* 4 *) Definition FLeXSellArgs_get (f: FLeXSellArgsFields )(r: FLeXSellArgs ) :  FLeXSellArgs_field_type f := 
 match f with | FLeXSellArgs_ι_price => fst7 r 
 | FLeXSellArgs_ι_amount => snd ( fst6 r ) 
 | FLeXSellArgs_ι_lend_finish_time => snd ( fst5 r ) 
 | FLeXSellArgs_ι_min_amount => snd ( fst4 r ) 
 | FLeXSellArgs_ι_deals_limit => snd ( fst3 r ) 
 | FLeXSellArgs_ι_tons_value => snd ( fst2 r ) 
 | FLeXSellArgs_ι_price_code => snd ( fst1 r ) 
 | FLeXSellArgs_ι_tip3_code => snd r 
 end .
(* 5 *) Coercion FLeXSellArgs_get : FLeXSellArgsFields >-> Funclass .
(* 6 *) Definition FLeXSellArgs_set (f: FLeXSellArgsFields ) 
(v: FLeXSellArgs_field_type f) (r: FLeXSellArgs ): FLeXSellArgs  :=
  match f, v with | FLeXSellArgs_ι_price , v' => ( v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_amount , v' => ( fst7 r , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_lend_finish_time , v' => ( fst7 r , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_min_amount , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_deals_limit , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_tons_value , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_price_code , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXSellArgs_ι_tip3_code , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance FLeXSellArgs_PruvendoRecord : PruvendoRecord FLeXSellArgs FLeXSellArgsFields :=
{
  field_type := FLeXSellArgs_field_type; 
  getPruvendoRecord := @FLeXSellArgs_get ;
  setPruvendoRecord := @FLeXSellArgs_set ;
} .
(* 3 *) Definition FLeXBuyArgs_field_type f : Type :=  
match f with | FLeXBuyArgs_ι_price => XInteger128 | FLeXBuyArgs_ι_amount => XInteger128 | FLeXBuyArgs_ι_order_finish_time => XInteger32 | FLeXBuyArgs_ι_min_amount => XInteger128 | FLeXBuyArgs_ι_deals_limit => XInteger8 | FLeXBuyArgs_ι_deploy_value => XInteger128 | FLeXBuyArgs_ι_price_code => TvmCell | FLeXBuyArgs_ι_my_tip3_addr => XAddress | FLeXBuyArgs_ι_tip3_code => TvmCell end .
(* 4 *) Definition FLeXBuyArgs_get (f: FLeXBuyArgsFields )(r: FLeXBuyArgs ) :  FLeXBuyArgs_field_type f := 
 match f with | FLeXBuyArgs_ι_price => fst8 r 
 | FLeXBuyArgs_ι_amount => snd ( fst7 r ) 
 | FLeXBuyArgs_ι_order_finish_time => snd ( fst6 r ) 
 | FLeXBuyArgs_ι_min_amount => snd ( fst5 r ) 
 | FLeXBuyArgs_ι_deals_limit => snd ( fst4 r ) 
 | FLeXBuyArgs_ι_deploy_value => snd ( fst3 r ) 
 | FLeXBuyArgs_ι_price_code => snd ( fst2 r ) 
 | FLeXBuyArgs_ι_my_tip3_addr => snd ( fst1 r ) 
 | FLeXBuyArgs_ι_tip3_code => snd r 
 end .
(* 5 *) Coercion FLeXBuyArgs_get : FLeXBuyArgsFields >-> Funclass .
(* 6 *) Definition FLeXBuyArgs_set (f: FLeXBuyArgsFields ) 
(v: FLeXBuyArgs_field_type f) (r: FLeXBuyArgs ): FLeXBuyArgs  :=
  match f, v with | FLeXBuyArgs_ι_price , v' => ( v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_amount , v' => ( fst8 r , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_order_finish_time , v' => ( fst8 r , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_min_amount , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_deals_limit , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_deploy_value , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_price_code , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_my_tip3_addr , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXBuyArgs_ι_tip3_code , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance FLeXBuyArgs_PruvendoRecord : PruvendoRecord FLeXBuyArgs FLeXBuyArgsFields :=
{
  field_type := FLeXBuyArgs_field_type; 
  getPruvendoRecord := @FLeXBuyArgs_get ;
  setPruvendoRecord := @FLeXBuyArgs_set ;
} .
(* 3 *) Definition FLeXXchgArgs_field_type f : Type :=  
match f with | FLeXXchgArgs_ι_sell => XBool | FLeXXchgArgs_ι_price_num => XInteger128 | FLeXXchgArgs_ι_price_denum => XInteger128 | FLeXXchgArgs_ι_amount => XInteger128 | FLeXXchgArgs_ι_lend_amount => XInteger128 | FLeXXchgArgs_ι_lend_finish_time => XInteger32 | FLeXXchgArgs_ι_min_amount => XInteger128 | FLeXXchgArgs_ι_deals_limit => XInteger8 | FLeXXchgArgs_ι_tons_value => XInteger128 | FLeXXchgArgs_ι_xchg_price_code => TvmCell | FLeXXchgArgs_ι_tip3_code => TvmCell end .
(* 4 *) Definition FLeXXchgArgs_get (f: FLeXXchgArgsFields )(r: FLeXXchgArgs ) :  FLeXXchgArgs_field_type f := 
 match f with | FLeXXchgArgs_ι_sell => fst10 r 
 | FLeXXchgArgs_ι_price_num => snd ( fst9 r ) 
 | FLeXXchgArgs_ι_price_denum => snd ( fst8 r ) 
 | FLeXXchgArgs_ι_amount => snd ( fst7 r ) 
 | FLeXXchgArgs_ι_lend_amount => snd ( fst6 r ) 
 | FLeXXchgArgs_ι_lend_finish_time => snd ( fst5 r ) 
 | FLeXXchgArgs_ι_min_amount => snd ( fst4 r ) 
 | FLeXXchgArgs_ι_deals_limit => snd ( fst3 r ) 
 | FLeXXchgArgs_ι_tons_value => snd ( fst2 r ) 
 | FLeXXchgArgs_ι_xchg_price_code => snd ( fst1 r ) 
 | FLeXXchgArgs_ι_tip3_code => snd r 
 end .
(* 5 *) Coercion FLeXXchgArgs_get : FLeXXchgArgsFields >-> Funclass .
(* 6 *) Definition FLeXXchgArgs_set (f: FLeXXchgArgsFields ) 
(v: FLeXXchgArgs_field_type f) (r: FLeXXchgArgs ): FLeXXchgArgs  :=
  match f, v with | FLeXXchgArgs_ι_sell , v' => ( v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_price_num , v' => ( fst10 r , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_price_denum , v' => ( fst10 r , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_amount , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_lend_amount , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_lend_finish_time , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_min_amount , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_deals_limit , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_tons_value , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_xchg_price_code , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXXchgArgs_ι_tip3_code , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance FLeXXchgArgs_PruvendoRecord : PruvendoRecord FLeXXchgArgs FLeXXchgArgsFields :=
{
  field_type := FLeXXchgArgs_field_type; 
  getPruvendoRecord := @FLeXXchgArgs_get ;
  setPruvendoRecord := @FLeXXchgArgs_set ;
} .
(* 3 *) Definition FLeXCancelArgs_field_type f : Type :=  
match f with | FLeXCancelArgs_ι_price => XInteger128 | FLeXCancelArgs_ι_min_amount => XInteger128 | FLeXCancelArgs_ι_deals_limit => XInteger8 | FLeXCancelArgs_ι_value => XInteger128 | FLeXCancelArgs_ι_price_code => TvmCell | FLeXCancelArgs_ι_tip3_code => TvmCell end .
(* 4 *) Definition FLeXCancelArgs_get (f: FLeXCancelArgsFields )(r: FLeXCancelArgs ) :  FLeXCancelArgs_field_type f := 
 match f with | FLeXCancelArgs_ι_price => fst5 r 
 | FLeXCancelArgs_ι_min_amount => snd ( fst4 r ) 
 | FLeXCancelArgs_ι_deals_limit => snd ( fst3 r ) 
 | FLeXCancelArgs_ι_value => snd ( fst2 r ) 
 | FLeXCancelArgs_ι_price_code => snd ( fst1 r ) 
 | FLeXCancelArgs_ι_tip3_code => snd r 
 end .
(* 5 *) Coercion FLeXCancelArgs_get : FLeXCancelArgsFields >-> Funclass .
(* 6 *) Definition FLeXCancelArgs_set (f: FLeXCancelArgsFields ) 
(v: FLeXCancelArgs_field_type f) (r: FLeXCancelArgs ): FLeXCancelArgs  :=
  match f, v with | FLeXCancelArgs_ι_price , v' => ( v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_min_amount , v' => ( fst5 r , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_deals_limit , v' => ( fst5 r , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_value , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_price_code , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXCancelArgs_ι_tip3_code , v' => ( fst5 r , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance FLeXCancelArgs_PruvendoRecord : PruvendoRecord FLeXCancelArgs FLeXCancelArgsFields :=
{
  field_type := FLeXCancelArgs_field_type; 
  getPruvendoRecord := @FLeXCancelArgs_get ;
  setPruvendoRecord := @FLeXCancelArgs_set ;
} .
(* 3 *) Definition FLeXXchgCancelArgs_field_type f : Type :=  
match f with | FLeXXchgCancelArgs_ι_sell => XBool | FLeXXchgCancelArgs_ι_price_num => XInteger128 | FLeXXchgCancelArgs_ι_price_denum => XInteger128 | FLeXXchgCancelArgs_ι_min_amount => XInteger128 | FLeXXchgCancelArgs_ι_deals_limit => XInteger8 | FLeXXchgCancelArgs_ι_value => XInteger128 | FLeXXchgCancelArgs_ι_xchg_price_code => TvmCell | FLeXXchgCancelArgs_ι_tip3_code => TvmCell end .
(* 4 *) Definition FLeXXchgCancelArgs_get (f: FLeXXchgCancelArgsFields )(r: FLeXXchgCancelArgs ) :  FLeXXchgCancelArgs_field_type f := 
 match f with | FLeXXchgCancelArgs_ι_sell => fst7 r 
 | FLeXXchgCancelArgs_ι_price_num => snd ( fst6 r ) 
 | FLeXXchgCancelArgs_ι_price_denum => snd ( fst5 r ) 
 | FLeXXchgCancelArgs_ι_min_amount => snd ( fst4 r ) 
 | FLeXXchgCancelArgs_ι_deals_limit => snd ( fst3 r ) 
 | FLeXXchgCancelArgs_ι_value => snd ( fst2 r ) 
 | FLeXXchgCancelArgs_ι_xchg_price_code => snd ( fst1 r ) 
 | FLeXXchgCancelArgs_ι_tip3_code => snd r 
 end .
(* 5 *) Coercion FLeXXchgCancelArgs_get : FLeXXchgCancelArgsFields >-> Funclass .
(* 6 *) Definition FLeXXchgCancelArgs_set (f: FLeXXchgCancelArgsFields ) 
(v: FLeXXchgCancelArgs_field_type f) (r: FLeXXchgCancelArgs ): FLeXXchgCancelArgs  :=
  match f, v with | FLeXXchgCancelArgs_ι_sell , v' => ( v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgCancelArgs_ι_price_num , v' => ( fst7 r , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgCancelArgs_ι_price_denum , v' => ( fst7 r , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgCancelArgs_ι_min_amount , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgCancelArgs_ι_deals_limit , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgCancelArgs_ι_value , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXXchgCancelArgs_ι_xchg_price_code , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXXchgCancelArgs_ι_tip3_code , v' => ( fst7 r , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance FLeXXchgCancelArgs_PruvendoRecord : PruvendoRecord FLeXXchgCancelArgs FLeXXchgCancelArgsFields :=
{
  field_type := FLeXXchgCancelArgs_field_type; 
  getPruvendoRecord := @FLeXXchgCancelArgs_get ;
  setPruvendoRecord := @FLeXXchgCancelArgs_set ;
} .
(* 3 *) Definition DFLeXClient_field_type f : Type :=  
match f with | DFLeXClient_ι_owner_ => XInteger256 | DFLeXClient_ι_trading_pair_code_ => TvmCell | DFLeXClient_ι_xchg_pair_code_ => TvmCell | DFLeXClient_ι_workchain_id_ => XInteger8 | DFLeXClient_ι_tons_cfg_ => TonsConfig | DFLeXClient_ι_flex_ => XAddress | DFLeXClient_ι_notify_addr_ => XAddress end .
(* 4 *) Definition DFLeXClient_get (f: DFLeXClientFields )(r: DFLeXClient ) :  DFLeXClient_field_type f := 
 match f with | DFLeXClient_ι_owner_ => fst6 r 
 | DFLeXClient_ι_trading_pair_code_ => snd ( fst5 r ) 
 | DFLeXClient_ι_xchg_pair_code_ => snd ( fst4 r ) 
 | DFLeXClient_ι_workchain_id_ => snd ( fst3 r ) 
 | DFLeXClient_ι_tons_cfg_ => snd ( fst2 r ) 
 | DFLeXClient_ι_flex_ => snd ( fst1 r ) 
 | DFLeXClient_ι_notify_addr_ => snd r 
 end .
(* 5 *) Coercion DFLeXClient_get : DFLeXClientFields >-> Funclass .
(* 6 *) Definition DFLeXClient_set (f: DFLeXClientFields ) 
(v: DFLeXClient_field_type f) (r: DFLeXClient ): DFLeXClient  :=
  match f, v with | DFLeXClient_ι_owner_ , v' => ( v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DFLeXClient_ι_trading_pair_code_ , v' => ( fst6 r , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DFLeXClient_ι_xchg_pair_code_ , v' => ( fst6 r , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DFLeXClient_ι_workchain_id_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DFLeXClient_ι_tons_cfg_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | DFLeXClient_ι_flex_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | DFLeXClient_ι_notify_addr_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance DFLeXClient_PruvendoRecord : PruvendoRecord DFLeXClient DFLeXClientFields :=
{
  field_type := DFLeXClient_field_type; 
  getPruvendoRecord := @DFLeXClient_get ;
  setPruvendoRecord := @DFLeXClient_set ;
} .
(* 3 *) Definition DFLeX_field_type f : Type :=  
match f with | DFLeX_ι_deployer_pubkey_ => XInteger256 | DFLeX_ι_tons_cfg_ => TonsConfig | DFLeX_ι_min_amount_ => XInteger128 | DFLeX_ι_deals_limit_ => XInteger8 | DFLeX_ι_notify_addr_ => XAddress end .
(* 4 *) Definition DFLeX_get (f: DFLeXFields )(r: DFLeX ) :  DFLeX_field_type f := 
 match f with | DFLeX_ι_deployer_pubkey_ => fst4 r 
 | DFLeX_ι_tons_cfg_ => snd ( fst3 r ) 
 | DFLeX_ι_min_amount_ => snd ( fst2 r ) 
 | DFLeX_ι_deals_limit_ => snd ( fst1 r ) 
 | DFLeX_ι_notify_addr_ => snd r 
 end .
(* 5 *) Coercion DFLeX_get : DFLeXFields >-> Funclass .
(* 6 *) Definition DFLeX_set (f: DFLeXFields ) 
(v: DFLeX_field_type f) (r: DFLeX ): DFLeX  :=
  match f, v with | DFLeX_ι_deployer_pubkey_ , v' => ( v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DFLeX_ι_tons_cfg_ , v' => ( fst4 r , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DFLeX_ι_min_amount_ , v' => ( fst4 r , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | DFLeX_ι_deals_limit_ , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | DFLeX_ι_notify_addr_ , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance DFLeX_PruvendoRecord : PruvendoRecord DFLeX DFLeXFields :=
{
  field_type := DFLeX_field_type; 
  getPruvendoRecord := @DFLeX_get ;
  setPruvendoRecord := @DFLeX_set ;
} .
(* 3 *) Definition process_ret_field_type f : Type :=  
match f with | process_ret_ι_sells_amount => XInteger128 | process_ret_ι_buys_amount => XInteger128 end .
(* 4 *) Definition process_ret_get (f: process_retFields )(r: process_ret ) :  process_ret_field_type f := 
 match f with | process_ret_ι_sells_amount => fst1 r 
 | process_ret_ι_buys_amount => snd r 
 end .
(* 5 *) Coercion process_ret_get : process_retFields >-> Funclass .
(* 6 *) Definition process_ret_set (f: process_retFields ) 
(v: process_ret_field_type f) (r: process_ret ): process_ret  :=
  match f, v with | process_ret_ι_sells_amount , v' => ( v' , snd r ) 
 | process_ret_ι_buys_amount , v' => ( fst1 r , v' ) 
 end .
(* 7 *) Global Instance process_ret_PruvendoRecord : PruvendoRecord process_ret process_retFields :=
{
  field_type := process_ret_field_type; 
  getPruvendoRecord := @process_ret_get ;
  setPruvendoRecord := @process_ret_set ;
} .
(* 3 *) Definition SellArgs_field_type f : Type :=  
match f with | SellArgs_ι_amount => XInteger128 | SellArgs_ι_receive_wallet => addr_std_fixed end .
(* 4 *) Definition SellArgs_get (f: SellArgsFields )(r: SellArgs ) :  SellArgs_field_type f := 
 match f with | SellArgs_ι_amount => fst1 r 
 | SellArgs_ι_receive_wallet => snd r 
 end .
(* 5 *) Coercion SellArgs_get : SellArgsFields >-> Funclass .
(* 6 *) Definition SellArgs_set (f: SellArgsFields ) 
(v: SellArgs_field_type f) (r: SellArgs ): SellArgs  :=
  match f, v with | SellArgs_ι_amount , v' => ( v' , snd r ) 
 | SellArgs_ι_receive_wallet , v' => ( fst1 r , v' ) 
 end .
(* 7 *) Global Instance SellArgs_PruvendoRecord : PruvendoRecord SellArgs SellArgsFields :=
{
  field_type := SellArgs_field_type; 
  getPruvendoRecord := @SellArgs_get ;
  setPruvendoRecord := @SellArgs_set ;
} .
(* 3 *) Definition DetailsInfo_field_type f : Type :=  
match f with | DetailsInfo_ι_price => XInteger128 | DetailsInfo_ι_min_amount => XInteger128 | DetailsInfo_ι_sell_amount => XInteger128 | DetailsInfo_ι_buy_amount => XInteger128 end .
(* 4 *) Definition DetailsInfo_get (f: DetailsInfoFields )(r: DetailsInfo ) :  DetailsInfo_field_type f := 
 match f with | DetailsInfo_ι_price => fst3 r 
 | DetailsInfo_ι_min_amount => snd ( fst2 r ) 
 | DetailsInfo_ι_sell_amount => snd ( fst1 r ) 
 | DetailsInfo_ι_buy_amount => snd r 
 end .
(* 5 *) Coercion DetailsInfo_get : DetailsInfoFields >-> Funclass .
(* 6 *) Definition DetailsInfo_set (f: DetailsInfoFields ) 
(v: DetailsInfo_field_type f) (r: DetailsInfo ): DetailsInfo  :=
  match f, v with | DetailsInfo_ι_price , v' => ( v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DetailsInfo_ι_min_amount , v' => ( fst3 r , v' , snd ( fst1 r ) , snd r ) 
 | DetailsInfo_ι_sell_amount , v' => ( fst3 r , snd ( fst2 r ) , v' , snd r ) 
 | DetailsInfo_ι_buy_amount , v' => ( fst3 r , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance DetailsInfo_PruvendoRecord : PruvendoRecord DetailsInfo DetailsInfoFields :=
{
  field_type := DetailsInfo_field_type; 
  getPruvendoRecord := @DetailsInfo_get ;
  setPruvendoRecord := @DetailsInfo_set ;
} .
(* 3 *) Definition DPrice_field_type f : Type :=  
match f with | DPrice_ι_price_ => XInteger128 
| DPrice_ι_sells_amount_ => XInteger128 
| DPrice_ι_buys_amount_ => XInteger128 
| DPrice_ι_flex_ => addr_std_fixed 
| DPrice_ι_min_amount_ => XInteger128 
| DPrice_ι_deals_limit_ => XInteger8 
| DPrice_ι_notify_addr_ => (* IFLeXNotifyPtr *) XInteger8
| DPrice_ι_workchain_id_ => XInteger8 
| DPrice_ι_tons_cfg_ => TonsConfig 
| DPrice_ι_tip3_code_ => TvmCell 
| DPrice_ι_tip3cfg_ => Tip3Config 
end .
(* 4 *) Definition DPrice_get (f: DPriceFields )(r: DPrice ) :  DPrice_field_type f := 
 match f with | DPrice_ι_price_ => fst10 r 
 | DPrice_ι_sells_amount_ => snd ( fst9 r ) 
 | DPrice_ι_buys_amount_ => snd ( fst8 r ) 
 | DPrice_ι_flex_ => snd ( fst7 r ) 
 | DPrice_ι_min_amount_ => snd ( fst6 r ) 
 | DPrice_ι_deals_limit_ => snd ( fst5 r ) 
 | DPrice_ι_notify_addr_ => snd ( fst4 r ) 
 | DPrice_ι_workchain_id_ => snd ( fst3 r ) 
 | DPrice_ι_tons_cfg_ => snd ( fst2 r ) 
 | DPrice_ι_tip3_code_ => snd ( fst1 r ) 
 | DPrice_ι_tip3cfg_ => snd r 
 end .
(* 5 *) Coercion DPrice_get : DPriceFields >-> Funclass .
(* 6 *) Definition DPrice_set (f: DPriceFields ) 
(v: DPrice_field_type f) (r: DPrice ): DPrice  :=
  match f, v with | DPrice_ι_price_ , v' => ( v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_sells_amount_ , v' => ( fst10 r , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_buys_amount_ , v' => ( fst10 r , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_flex_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_min_amount_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_deals_limit_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_notify_addr_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_workchain_id_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_tons_cfg_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | DPrice_ι_tip3_code_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | DPrice_ι_tip3cfg_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance DPrice_PruvendoRecord : PruvendoRecord DPrice DPriceFields :=
{
  field_type := DPrice_field_type; 
  getPruvendoRecord := @DPrice_get ;
  setPruvendoRecord := @DPrice_set ;
} .
(* 3 *) Definition RationalPrice_field_type f : Type :=  
match f with | RationalPrice_ι_num => XInteger128 | RationalPrice_ι_denum => XInteger128 end .
(* 4 *) Definition RationalPrice_get (f: RationalPriceFields )(r: RationalPrice ) :  RationalPrice_field_type f := 
 match f with | RationalPrice_ι_num => fst1 r 
 | RationalPrice_ι_denum => snd r 
 end .
(* 5 *) Coercion RationalPrice_get : RationalPriceFields >-> Funclass .
(* 6 *) Definition RationalPrice_set (f: RationalPriceFields ) 
(v: RationalPrice_field_type f) (r: RationalPrice ): RationalPrice  :=
  match f, v with | RationalPrice_ι_num , v' => ( v' , snd r ) 
 | RationalPrice_ι_denum , v' => ( fst1 r , v' ) 
 end .
(* 7 *) Global Instance RationalPrice_PruvendoRecord : PruvendoRecord RationalPrice RationalPriceFields :=
{
  field_type := RationalPrice_field_type; 
  getPruvendoRecord := @RationalPrice_get ;
  setPruvendoRecord := @RationalPrice_set ;
} .
(* 3 *) Definition PayloadArgs_field_type f : Type :=  
match f with | PayloadArgs_ι_sell => XBool | PayloadArgs_ι_amount => XInteger128 | PayloadArgs_ι_receive_tip3_wallet => addr_std_fixed | PayloadArgs_ι_client_addr => addr_std_fixed end .
(* 4 *) Definition PayloadArgs_get (f: PayloadArgsFields )(r: PayloadArgs ) :  PayloadArgs_field_type f := 
 match f with | PayloadArgs_ι_sell => fst3 r 
 | PayloadArgs_ι_amount => snd ( fst2 r ) 
 | PayloadArgs_ι_receive_tip3_wallet => snd ( fst1 r ) 
 | PayloadArgs_ι_client_addr => snd r 
 end .
(* 5 *) Coercion PayloadArgs_get : PayloadArgsFields >-> Funclass .
(* 6 *) Definition PayloadArgs_set (f: PayloadArgsFields ) 
(v: PayloadArgs_field_type f) (r: PayloadArgs ): PayloadArgs  :=
  match f, v with | PayloadArgs_ι_sell , v' => ( v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PayloadArgs_ι_amount , v' => ( fst3 r , v' , snd ( fst1 r ) , snd r ) 
 | PayloadArgs_ι_receive_tip3_wallet , v' => ( fst3 r , snd ( fst2 r ) , v' , snd r ) 
 | PayloadArgs_ι_client_addr , v' => ( fst3 r , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance PayloadArgs_PruvendoRecord : PruvendoRecord PayloadArgs PayloadArgsFields :=
{
  field_type := PayloadArgs_field_type; 
  getPruvendoRecord := @PayloadArgs_get ;
  setPruvendoRecord := @PayloadArgs_set ;
} .
(* 3 *) Definition OrderInfoXchg_field_type f : Type :=  
match f with | OrderInfoXchg_ι_original_amount => XInteger128 | OrderInfoXchg_ι_amount => XInteger128 | OrderInfoXchg_ι_account => XInteger128 | OrderInfoXchg_ι_tip3_wallet_provide => addr_std_fixed | OrderInfoXchg_ι_tip3_wallet_receive => addr_std_fixed | OrderInfoXchg_ι_client_addr => addr_std_fixed | OrderInfoXchg_ι_order_finish_time => XInteger32 end .
(* 4 *) Definition OrderInfoXchg_get (f: OrderInfoXchgFields )(r: OrderInfoXchg ) :  OrderInfoXchg_field_type f := 
 match f with | OrderInfoXchg_ι_original_amount => fst6 r 
 | OrderInfoXchg_ι_amount => snd ( fst5 r ) 
 | OrderInfoXchg_ι_account => snd ( fst4 r ) 
 | OrderInfoXchg_ι_tip3_wallet_provide => snd ( fst3 r ) 
 | OrderInfoXchg_ι_tip3_wallet_receive => snd ( fst2 r ) 
 | OrderInfoXchg_ι_client_addr => snd ( fst1 r ) 
 | OrderInfoXchg_ι_order_finish_time => snd r 
 end .
(* 5 *) Coercion OrderInfoXchg_get : OrderInfoXchgFields >-> Funclass .
(* 6 *) Definition OrderInfoXchg_set (f: OrderInfoXchgFields ) 
(v: OrderInfoXchg_field_type f) (r: OrderInfoXchg ): OrderInfoXchg  :=
  match f, v with | OrderInfoXchg_ι_original_amount , v' => ( v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | OrderInfoXchg_ι_amount , v' => ( fst6 r , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | OrderInfoXchg_ι_account , v' => ( fst6 r , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | OrderInfoXchg_ι_tip3_wallet_provide , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | OrderInfoXchg_ι_tip3_wallet_receive , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | OrderInfoXchg_ι_client_addr , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | OrderInfoXchg_ι_order_finish_time , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance OrderInfoXchg_PruvendoRecord : PruvendoRecord OrderInfoXchg OrderInfoXchgFields :=
{
  field_type := OrderInfoXchg_field_type; 
  getPruvendoRecord := @OrderInfoXchg_get ;
  setPruvendoRecord := @OrderInfoXchg_set ;
} .
(* 3 *) Definition DetailsInfoXchg_field_type f : Type :=  
match f with | DetailsInfoXchg_ι_price_num => XInteger128 | DetailsInfoXchg_ι_price_denum => XInteger128 | DetailsInfoXchg_ι_min_amount => XInteger128 | DetailsInfoXchg_ι_sell_amount => XInteger128 | DetailsInfoXchg_ι_buy_amount => XInteger128 end .
(* 4 *) Definition DetailsInfoXchg_get (f: DetailsInfoXchgFields )(r: DetailsInfoXchg ) :  DetailsInfoXchg_field_type f := 
 match f with | DetailsInfoXchg_ι_price_num => fst4 r 
 | DetailsInfoXchg_ι_price_denum => snd ( fst3 r ) 
 | DetailsInfoXchg_ι_min_amount => snd ( fst2 r ) 
 | DetailsInfoXchg_ι_sell_amount => snd ( fst1 r ) 
 | DetailsInfoXchg_ι_buy_amount => snd r 
 end .
(* 5 *) Coercion DetailsInfoXchg_get : DetailsInfoXchgFields >-> Funclass .
(* 6 *) Definition DetailsInfoXchg_set (f: DetailsInfoXchgFields ) 
(v: DetailsInfoXchg_field_type f) (r: DetailsInfoXchg ): DetailsInfoXchg  :=
  match f, v with | DetailsInfoXchg_ι_price_num , v' => ( v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DetailsInfoXchg_ι_price_denum , v' => ( fst4 r , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DetailsInfoXchg_ι_min_amount , v' => ( fst4 r , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | DetailsInfoXchg_ι_sell_amount , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | DetailsInfoXchg_ι_buy_amount , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance DetailsInfoXchg_PruvendoRecord : PruvendoRecord DetailsInfoXchg DetailsInfoXchgFields :=
{
  field_type := DetailsInfoXchg_field_type; 
  getPruvendoRecord := @DetailsInfoXchg_get ;
  setPruvendoRecord := @DetailsInfoXchg_set ;
} .
(* 3 *) Definition DPriceXchg_field_type f : Type :=  
match f with | DPriceXchg_ι_price_ => (* price_t *) RationalPrice
| DPriceXchg_ι_sells_amount_ => XInteger128 
| DPriceXchg_ι_buys_amount_ => XInteger128 
| DPriceXchg_ι_flex_ => addr_std_fixed 
| DPriceXchg_ι_min_amount_ => XInteger128 
| DPriceXchg_ι_deals_limit_ => XInteger8 
| DPriceXchg_ι_notify_addr_ => (* IFLeXNotifyPtr *) XInteger8
| DPriceXchg_ι_workchain_id_ => XInteger8 
| DPriceXchg_ι_tons_cfg_ => TonsConfig 
| DPriceXchg_ι_tip3_code_ => TvmCell 
| DPriceXchg_ι_major_tip3cfg_ => Tip3Config 
| DPriceXchg_ι_minor_tip3cfg_ => Tip3Config 
end .
(* 4 *) Definition DPriceXchg_get (f: DPriceXchgFields )(r: DPriceXchg ) :  DPriceXchg_field_type f := 
 match f with | DPriceXchg_ι_price_ => fst11 r 
 | DPriceXchg_ι_sells_amount_ => snd ( fst10 r ) 
 | DPriceXchg_ι_buys_amount_ => snd ( fst9 r ) 
 | DPriceXchg_ι_flex_ => snd ( fst8 r ) 
 | DPriceXchg_ι_min_amount_ => snd ( fst7 r ) 
 | DPriceXchg_ι_deals_limit_ => snd ( fst6 r ) 
 | DPriceXchg_ι_notify_addr_ => snd ( fst5 r ) 
 | DPriceXchg_ι_workchain_id_ => snd ( fst4 r ) 
 | DPriceXchg_ι_tons_cfg_ => snd ( fst3 r ) 
 | DPriceXchg_ι_tip3_code_ => snd ( fst2 r ) 
 | DPriceXchg_ι_major_tip3cfg_ => snd ( fst1 r ) 
 | DPriceXchg_ι_minor_tip3cfg_ => snd r 
 end .
(* 5 *) Coercion DPriceXchg_get : DPriceXchgFields >-> Funclass .
(* 6 *) Definition DPriceXchg_set (f: DPriceXchgFields ) 
(v: DPriceXchg_field_type f) (r: DPriceXchg ): DPriceXchg  :=
  match f, v with | DPriceXchg_ι_price_ , v' => ( v' , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_sells_amount_ , v' => ( fst11 r , v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_buys_amount_ , v' => ( fst11 r , snd ( fst10 r ) , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_flex_ , v' => ( fst11 r , snd ( fst10 r ) , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_min_amount_ , v' => ( fst11 r , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_deals_limit_ , v' => ( fst11 r , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_notify_addr_ , v' => ( fst11 r , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_workchain_id_ , v' => ( fst11 r , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_tons_cfg_ , v' => ( fst11 r , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_tip3_code_ , v' => ( fst11 r , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | DPriceXchg_ι_major_tip3cfg_ , v' => ( fst11 r , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | DPriceXchg_ι_minor_tip3cfg_ , v' => ( fst11 r , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance DPriceXchg_PruvendoRecord : PruvendoRecord DPriceXchg DPriceXchgFields :=
{
  field_type := DPriceXchg_field_type; 
  getPruvendoRecord := @DPriceXchg_get ;
  setPruvendoRecord := @DPriceXchg_set ;
} .
(* 3 *) Definition DTradingPair_field_type f : Type :=  
match f with | DTradingPair_ι_flex_addr_ => XAddress | DTradingPair_ι_tip3_root_ => XAddress | DTradingPair_ι_deploy_value_ => XInteger128 end .
(* 4 *) Definition DTradingPair_get (f: DTradingPairFields )(r: DTradingPair ) :  DTradingPair_field_type f := 
 match f with | DTradingPair_ι_flex_addr_ => fst2 r 
 | DTradingPair_ι_tip3_root_ => snd ( fst1 r ) 
 | DTradingPair_ι_deploy_value_ => snd r 
 end .
(* 5 *) Coercion DTradingPair_get : DTradingPairFields >-> Funclass .
(* 6 *) Definition DTradingPair_set (f: DTradingPairFields ) 
(v: DTradingPair_field_type f) (r: DTradingPair ): DTradingPair  :=
  match f, v with | DTradingPair_ι_flex_addr_ , v' => ( v' , snd ( fst1 r ) , snd r ) 
 | DTradingPair_ι_tip3_root_ , v' => ( fst2 r , v' , snd r ) 
 | DTradingPair_ι_deploy_value_ , v' => ( fst2 r , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance DTradingPair_PruvendoRecord : PruvendoRecord DTradingPair DTradingPairFields :=
{
  field_type := DTradingPair_field_type; 
  getPruvendoRecord := @DTradingPair_get ;
  setPruvendoRecord := @DTradingPair_set ;
} .
(* 3 *) Definition DXchgPair_field_type f : Type :=  
match f with | DXchgPair_ι_flex_addr_ => XAddress | DXchgPair_ι_tip3_major_root_ => XAddress | DXchgPair_ι_tip3_minor_root_ => XAddress | DXchgPair_ι_deploy_value_ => XInteger128 end .
(* 4 *) Definition DXchgPair_get (f: DXchgPairFields )(r: DXchgPair ) :  DXchgPair_field_type f := 
 match f with | DXchgPair_ι_flex_addr_ => fst3 r 
 | DXchgPair_ι_tip3_major_root_ => snd ( fst2 r ) 
 | DXchgPair_ι_tip3_minor_root_ => snd ( fst1 r ) 
 | DXchgPair_ι_deploy_value_ => snd r 
 end .
(* 5 *) Coercion DXchgPair_get : DXchgPairFields >-> Funclass .
(* 6 *) Definition DXchgPair_set (f: DXchgPairFields ) 
(v: DXchgPair_field_type f) (r: DXchgPair ): DXchgPair  :=
  match f, v with | DXchgPair_ι_flex_addr_ , v' => ( v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DXchgPair_ι_tip3_major_root_ , v' => ( fst3 r , v' , snd ( fst1 r ) , snd r ) 
 | DXchgPair_ι_tip3_minor_root_ , v' => ( fst3 r , snd ( fst2 r ) , v' , snd r ) 
 | DXchgPair_ι_deploy_value_ , v' => ( fst3 r , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance DXchgPair_PruvendoRecord : PruvendoRecord DXchgPair DXchgPairFields :=
{
  field_type := DXchgPair_field_type; 
  getPruvendoRecord := @DXchgPair_get ;
  setPruvendoRecord := @DXchgPair_set ;
} .
(* 3 *) Definition VMCommit_field_type f : Type :=  
match f with | VMCommit_ι_dealer => dealer end .
(* 4 *) Definition VMCommit_get (f: VMCommitFields )(r: VMCommit ) :  VMCommit_field_type f := 
 match f with | VMCommit_ι_dealer => fst0 r 
 end .
(* 5 *) Coercion VMCommit_get : VMCommitFields >-> Funclass .
(* 6 *) Definition VMCommit_set (f: VMCommitFields ) 
(v: VMCommit_field_type f) (r: VMCommit ): VMCommit  :=
  match f, v with | VMCommit_ι_dealer , v' => ( v' ) 
 end .
(* 7 *) Global Instance VMCommit_PruvendoRecord : PruvendoRecord VMCommit VMCommitFields :=
{
  field_type := VMCommit_field_type; 
  getPruvendoRecord := @VMCommit_get ;
  setPruvendoRecord := @VMCommit_set ;
} .
(* 3 *) Definition LocalState_field_type f : Type :=  
match f with 
| LocalState_ι_uint256 => XHMap string XInteger256 
| LocalState_ι_Grams => XHMap string XInteger
end .
(* 4 *) Definition LocalState_get (f: LocalStateFields )(r: LocalState ) :  LocalState_field_type f := 
 match f with 
| LocalState_ι_uint256 => fst1 r
 | LocalState_ι_Grams  => snd r 
 end .
(* 5 *) Coercion LocalState_get : LocalStateFields >-> Funclass .
(* 6 *) Definition LocalState_set (f: LocalStateFields ) 
(v: LocalState_field_type f) (r: LocalState ): LocalState  :=
  match f, v with 
| LocalState_ι_uint256 , v' => ( v' , snd r ) 
| LocalState_ι_Grams , v' => ( fst1 r , v' )
 end .
(* 7 *) Global Instance LocalState_PruvendoRecord : PruvendoRecord LocalState LocalStateFields :=
{
  field_type := LocalState_field_type; 
  getPruvendoRecord := @LocalState_get ;
  setPruvendoRecord := @LocalState_set ;
} .
(* 3 *) Definition Ledger_field_type f : Type :=  
match f with | Ledger_ι_dealer => dealer | Ledger_ι_VMCommit => VMCommit | Ledger_ι_LocalState => LocalState | Ledger_ι_LocalStateCopy => LocalState end .
(* 4 *) Definition Ledger_get (f: LedgerFields )(r: Ledger ) :  Ledger_field_type f := 
 match f with | Ledger_ι_dealer => fst3 r 
 | Ledger_ι_VMCommit => snd ( fst2 r ) 
 | Ledger_ι_LocalState => snd ( fst1 r ) 
 | Ledger_ι_LocalStateCopy => snd r 
 end .
(* 5 *) Coercion Ledger_get : LedgerFields >-> Funclass .
(* 6 *) Definition Ledger_set (f: LedgerFields ) 
(v: Ledger_field_type f) (r: Ledger ): Ledger  :=
  match f, v with | Ledger_ι_dealer , v' => ( v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Ledger_ι_VMCommit , v' => ( fst3 r , v' , snd ( fst1 r ) , snd r ) 
 | Ledger_ι_LocalState , v' => ( fst3 r , snd ( fst2 r ) , v' , snd r ) 
 | Ledger_ι_LocalStateCopy , v' => ( fst3 r , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance Ledger_PruvendoRecord : PruvendoRecord Ledger LedgerFields :=
{
  field_type := Ledger_field_type; 
  getPruvendoRecord := @Ledger_get ;
  setPruvendoRecord := @Ledger_set ;
} .
Definition T1 := dealer .
Definition T2 := VMCommit .
Definition T3 := LocalState .
Definition T4 := LocalState .

 
 Definition projEmbed_T1 : Ledger -> T1 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_dealer. 
 Definition injEmbed_T1 : T1 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_dealer. 
 
 Lemma projinj_T1 : forall ( t : T1 ) ( s : Ledger ), projEmbed_T1 ( injEmbed_T1 t s ) = t . 
 Proof. 
 intros. auto. 
 Qed. 
 
 Lemma injproj_T1 : forall ( s : Ledger ) , injEmbed_T1 ( projEmbed_T1 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T1 : forall ( t1 t2 : T1 ) ( s : Ledger ) , 
 injEmbed_T1 t1 ( injEmbed_T1 t2 s) = 
 injEmbed_T1 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT1 : EmbeddedType Ledger T1 := 
 { 
 projEmbed := projEmbed_T1 ; 
 injEmbed := injEmbed_T1 ; 
 projinj := projinj_T1 ; 
 injproj := injproj_T1 ; 
 injinj := injinj_T1 ; 
 } . 
 


 
 Definition projEmbed_T2 : Ledger -> T2 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_VMCommit. 
 Definition injEmbed_T2 : T2 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_VMCommit. 
 
 Lemma projinj_T2 : forall ( t : T2 ) ( s : Ledger ), projEmbed_T2 ( injEmbed_T2 t s ) = t . 
 Proof. 
 intros. auto. 
 Qed. 
 
 Lemma injproj_T2 : forall ( s : Ledger ) , injEmbed_T2 ( projEmbed_T2 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T2 : forall ( t1 t2 : T2 ) ( s : Ledger ) , 
 injEmbed_T2 t1 ( injEmbed_T2 t2 s) = 
 injEmbed_T2 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT2 : EmbeddedType Ledger T2 := 
 { 
 projEmbed := projEmbed_T2 ; 
 injEmbed := injEmbed_T2 ; 
 projinj := projinj_T2 ; 
 injproj := injproj_T2 ; 
 injinj := injinj_T2 ; 
 } . 
 


 
 Definition projEmbed_T3 : Ledger -> T3 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalState. 
 Definition injEmbed_T3 : T3 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalState. 
 
 Lemma projinj_T3 : forall ( t : T3 ) ( s : Ledger ), projEmbed_T3 ( injEmbed_T3 t s ) = t . 
 Proof. 
 intros. auto. 
 Qed. 
 
 Lemma injproj_T3 : forall ( s : Ledger ) , injEmbed_T3 ( projEmbed_T3 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T3 : forall ( t1 t2 : T3 ) ( s : Ledger ) , 
 injEmbed_T3 t1 ( injEmbed_T3 t2 s) = 
 injEmbed_T3 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT3 : EmbeddedType Ledger T3 := 
 { 
 projEmbed := projEmbed_T3 ; 
 injEmbed := injEmbed_T3 ; 
 projinj := projinj_T3 ; 
 injproj := injproj_T3 ; 
 injinj := injinj_T3 ; 
 } . 
 


 
 Definition projEmbed_T4 : Ledger -> T4 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalStateCopy. 
 Definition injEmbed_T4 : T4 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalStateCopy. 
 
 Lemma projinj_T4 : forall ( t : T4 ) ( s : Ledger ), projEmbed_T4 ( injEmbed_T4 t s ) = t . 
 Proof. 
 intros. auto. 
 Qed. 
 
 Lemma injproj_T4 : forall ( s : Ledger ) , injEmbed_T4 ( projEmbed_T4 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T4 : forall ( t1 t2 : T4 ) ( s : Ledger ) , 
 injEmbed_T4 t1 ( injEmbed_T4 t2 s) = 
 injEmbed_T4 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT4 : EmbeddedType Ledger T4 := 
 { 
 projEmbed := projEmbed_T4 ; 
 injEmbed := injEmbed_T4 ; 
 projinj := projinj_T4 ; 
 injproj := injproj_T4 ; 
 injinj := injinj_T4 ; 
 } . 
 

Axiom (* Lemma *) injcommute_T1_T2: 
               forall ( u : T2 ) ( t : T1 ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT2) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT2) u s ) ).
(* Proof.
 intros. 
 auto.
Qed. *)

Instance InjectCommutableStates_T1_T2 : 
@InjectCommutableStates Ledger ( T1 ) T2 := 
{
(*   embeddedTypeT := embeddedT1; *)
  embeddedTypeU := embeddedT2 ;

  injcommute := injcommute_T1_T2 
}.

Definition embeddedProduct_T1_T2 := 
           @embeddedProduct Ledger ( T1 ) T2
           InjectCommutableStates_T1_T2.

Existing Instance embeddedProduct_T1_T2.


Lemma injcommute_T1xT2_T3 : 
               forall ( u : T3 ) ( t :  (T1 * T2)%xprod ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT3) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT3) u s ) ).
Proof.
 intros. auto.
Qed.

Instance InjectCommutableStates_T1xT2_T3 : 
@InjectCommutableStates Ledger (T1 * T2)%xprod T3 := 
{
  embeddedTypeU := embeddedT3 ;

  injcommute := injcommute_T1xT2_T3 
}.

Definition embeddedProduct_T1xT2_T3 := 
           @embeddedProduct Ledger (T1 * T2)%xprod T3
  
           InjectCommutableStates_T1xT2_T3.

Existing Instance embeddedProduct_T1xT2_T3 . 


Lemma injcommute_T1xT2xT3_T4 : 
               forall ( u : T4 ) ( t :  ((T1 * T2)%xprod* T3)%xprod ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT4) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT4) u s ) ).
Proof.
 intros. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3_T4 : 
@InjectCommutableStates Ledger ((T1 * T2)%xprod* T3)%xprod T4 := 
{
  embeddedTypeU := embeddedT4 ;

  injcommute := injcommute_T1xT2xT3_T4 
}.

Definition embeddedProduct_T1xT2xT3_T4 := 
           @embeddedProduct Ledger ((T1 * T2)%xprod* T3)%xprod T4
  
           InjectCommutableStates_T1xT2xT3_T4.

Existing Instance embeddedProduct_T1xT2xT3_T4 . 


 
Axiom (* Lemma *) fullState_T1xT2xT3_T4 : forall s s0, 
 injEmbed ( T := (((T1 * T2)%xprod * T3)%xprod * T4)%xprod ) 
 ( projEmbed s ) ( injEmbed ( T := T4 ) ( projEmbed s ) s0 ) = s. 
(*  Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed.  *)
 
 Check FullState. 
 
 Instance FullState_T1xT2xT3_T4 : 
 FullState Ledger ((T1 * T2)%xprod * T3)%xprod T4 := 
 { 
 injComm := InjectCommutableStates_T1xT2xT3_T4 ; 
 fullState := fullState_T1xT2xT3_T4 
 } . 
 

Local Open Scope solidity_scope.
Notation "'↑ε4' m ":= (liftEmbeddedState ( H := embeddedT4 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε3' m ":= (liftEmbeddedState ( H := embeddedT3 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε2' m ":= (liftEmbeddedState ( H := embeddedT2 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε1' m ":= (liftEmbeddedState ( H := embeddedT1 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.

Notation "'↑4' m ":= (liftEmbeddedState ( H := embeddedT4 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑3' m ":= (liftEmbeddedState ( H := embeddedT3 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑2' m ":= (liftEmbeddedState ( H := embeddedT2 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑1' m ":= (liftEmbeddedState ( H := embeddedT1 ) ( m ) ) (at level 10, left associativity): solidity_scope.

Notation "'↑↑4' m ":= (liftEmbeddedState ( H := embeddedT4 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑3' m ":= (liftEmbeddedState ( H := embeddedT3 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑2' m ":= (liftEmbeddedState ( H := embeddedT2 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑1' m ":= (liftEmbeddedState ( H := embeddedT1 ) ) (at level 10, left associativity): solidity_scope.

Notation "'↑0' m " := ( liftEmbeddedState ( H :=  embeddedProduct_T1xT2xT3_T4 ) ( m )) (at level 10, left associativity): solidity_scope.
Notation "'↑↑0'" := ( liftEmbeddedState ( H :=  embeddedProduct_T1xT2xT3_T4 )) (at level 32, left associativity): solidity_scope.
Notation " ↓ m " := ( callEmbeddedStateAdj m default (H0 :=  FullState_T1xT2xT3_T4 ) ) (at level 31, left associativity): solidity_scope.
Global Instance iso_T1 : IsoTypes T1 (field_type (R:=Ledger) Ledger_ι_dealer) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T2 : IsoTypes T2 (field_type (R:=Ledger) Ledger_ι_VMCommit) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T3 : IsoTypes T3 (field_type (R:=Ledger) Ledger_ι_LocalState) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T4 : IsoTypes T4 (field_type (R:=Ledger) Ledger_ι_LocalStateCopy) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.


End LedgerClass .
