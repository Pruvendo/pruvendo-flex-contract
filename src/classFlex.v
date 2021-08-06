 Require Import Coq.Program.Basics. 
 Require Import Coq.Logic.FunctionalExtensionality. 
 Require Import Coq.Program.Combinators. 
 Require Import FinProof.ProgrammingWith. 
 Require Import String. 
 
Require Import FinProof.ProgrammingWith.
Require Import FinProof.Types.IsoTypes.
Require Import FinProof.Common.
Require Import FinProof.MonadTransformers21.
Require Import FinProof.StateMonad21.
Require Import FinProof.EpsilonMonad.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG25.
  
Local Open Scope record.
Local Open Scope program_scope. 
 
Section RecordsDefinitions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Maximal Implicit Insertion.
 
 Variables I I8 I16 I32 I64 I128 I256 : Type. 
 Variables A B C S Bs : Type. 
 Variables L M H Q R Bq : Type -> Type. (* H - handle<type> , Q - queue<type> , R - ref<type> Bq - big_queue<type>*) 
 Variables HM P : Type -> Type -> Type. 
 Variables T G Sl Bt Bi : Type. 
 
 (* Variables TipAccountP PadawanP ProposalResolverP : Type . *) 
 

(* 1 *) Inductive TickTockFields := | TickTock_ι_tick | TickTock_ι_tock .
(* 2 *) Definition TickTockP := 
 ( B * 
 B )%type .
(* 1 *) Inductive allowance_infoFields := | allowance_info_ι_spender | allowance_info_ι_remainingTokens .
(* 2 *) Definition allowance_infoP := 
 ( A * 
 I256 )%type .
(* 1 *) Inductive StateInitFields := | StateInit_ι_split_depth | StateInit_ι_special | StateInit_ι_code | StateInit_ι_data | StateInit_ι_library .
(* 2 *) Definition StateInitP := 
 ( M I8 * 
 M TickTockP * 
 M C * 
 M C * 
 M C )%type .
(* 1 *) Inductive DTONTokenWalletFields := | DTONTokenWallet_ι_name_ | DTONTokenWallet_ι_symbol_ | DTONTokenWallet_ι_decimals_ | DTONTokenWallet_ι_balance_ | DTONTokenWallet_ι_root_public_key_ | DTONTokenWallet_ι_wallet_public_key_ | DTONTokenWallet_ι_root_address_ | DTONTokenWallet_ι_owner_address_ | DTONTokenWallet_ι_code_ | DTONTokenWallet_ι_allowance_ | DTONTokenWallet_ι_workchain_id_ .
(* 2 *) Definition DTONTokenWalletP := 
 ( (L I8) * 
 (L I8) * 
 I8 * 
 I128 * 
 I256 * 
 I256 * 
 A * 
 M A * 
 C * 
 M allowance_infoP * 
 I8 )%type .
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
  (* 1 *) Inductive dealerFields := | dealer_ι_tip3root_ | dealer_ι_notify_addr_ | dealer_ι_price_ | dealer_ι_deals_limit_ | dealer_ι_tons_cfg_ | dealer_ι_sells_amount_ | dealer_ι_sells_ | dealer_ι_buys_amount_ | dealer_ι_buys_ | dealer_ι_ret_ .
  (* 2 *) Definition dealerP := 
 ( A * 
 I16 (* handle<IFLeXNotify> *) * 
 I128 * 
 I * 
 TonsConfigP * 
 I128 * 
 Q OrderInfoP * 
 I128 * 
 Q OrderInfoP * 
 M OrderRetP )%type .
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

(* 1 *) Inductive FLeXSellArgsFields := | FLeXSellArgs_ι_price | FLeXSellArgs_ι_amount | FLeXSellArgs_ι_lend_finish_time | FLeXSellArgs_ι_min_amount | FLeXSellArgs_ι_deals_limit | FLeXSellArgs_ι_tons_value | FLeXSellArgs_ι_price_code | FLeXSellArgs_ι_addrs | FLeXSellArgs_ι_tip3_code | FLeXSellArgs_ι_tip3cfg .
(* 2 *) Definition FLeXSellArgsP := 
 ( I128 * 
 I128 * 
 I32 * 
 I128 * 
 I8 * 
 I128 * 
 C * 
 R FLeXSellArgsAddrsP * 
 C * 
 R Tip3ConfigP )%type .

(* 1 *) Inductive FLeXBuyArgsFields := | FLeXBuyArgs_ι_price | FLeXBuyArgs_ι_amount | FLeXBuyArgs_ι_order_finish_time | FLeXBuyArgs_ι_min_amount | FLeXBuyArgs_ι_deals_limit | FLeXBuyArgs_ι_deploy_value | FLeXBuyArgs_ι_price_code | FLeXBuyArgs_ι_my_tip3_addr | FLeXBuyArgs_ι_tip3_code | FLeXBuyArgs_ι_tip3cfg .
(* 2 *) Definition FLeXBuyArgsP := 
 ( I128 * 
 I128 * 
 I32 * 
 I128 * 
 I8 * 
 I128 * 
 C * 
 A * 
 C * 
 R Tip3ConfigP )%type .

(* 1 *) Inductive FLeXXchgCfgsFields := | FLeXXchgCfgs_ι_major_tip3cfg | FLeXXchgCfgs_ι_minor_tip3cfg .
(* 2 *) Definition FLeXXchgCfgsP := 
 ( R Tip3ConfigP * 
 R Tip3ConfigP )%type .

(* 1 *) Inductive FLeXXchgArgsFields := | FLeXXchgArgs_ι_sell | FLeXXchgArgs_ι_price_num | FLeXXchgArgs_ι_price_denum | FLeXXchgArgs_ι_amount | FLeXXchgArgs_ι_lend_amount | FLeXXchgArgs_ι_lend_finish_time | FLeXXchgArgs_ι_min_amount | FLeXXchgArgs_ι_deals_limit | FLeXXchgArgs_ι_tons_value | FLeXXchgArgs_ι_xchg_price_code | FLeXXchgArgs_ι_addrs | FLeXXchgArgs_ι_tip3_code | FLeXXchgArgs_ι_tip3cfgs .
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
 R FLeXSellArgsAddrsP * 
 C * 
 R FLeXXchgCfgsP )%type .

(* 1 *) Inductive FLeXCancelArgsFields := | FLeXCancelArgs_ι_price | FLeXCancelArgs_ι_min_amount | FLeXCancelArgs_ι_deals_limit | FLeXCancelArgs_ι_value | FLeXCancelArgs_ι_price_code | FLeXCancelArgs_ι_tip3_code | FLeXCancelArgs_ι_tip3cfg .
(* 2 *) Definition FLeXCancelArgsP := 
 ( I128 * 
 I128 * 
 I8 * 
 I128 * 
 C * 
 C * 
 R Tip3ConfigP )%type .

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
(* 1 *) Inductive FLeXClientFields := | FLeXClient_ι_owner_ | FLeXClient_ι_trading_pair_code_ | FLeXClient_ι_xchg_pair_code_ | FLeXClient_ι_workchain_id_ | FLeXClient_ι_tons_cfg_ | FLeXClient_ι_flex_ | FLeXClient_ι_notify_addr_ .
(* 2 *) Definition FLeXClientP := 
 ( I256 * 
 C * 
 C * 
 I8 * 
 TonsConfigP * 
 A * 
 A )%type .
(* 1 *) Inductive FLeXFields := | FLeX_ι_deployer_pubkey_ | FLeX_ι_tons_cfg_ | FLeX_ι_pair_code_ | FLeX_ι_xchg_pair_code_ | FLeX_ι_price_code_ | FLeX_ι_xchg_price_code_ | FLeX_ι_min_amount_ | FLeX_ι_deals_limit_ | FLeX_ι_notify_addr_ .
(* 2 *) Definition FLeXP := 
 ( I256 * 
 TonsConfigP * 
 M C * 
 M C * 
 M C * 
 M C * 
 I128 * 
 I8 * 
 A )%type .
(* 1 *) Inductive process_retFields := | process_ret_ι_sells_amount | process_ret_ι_sells_ | process_ret_ι_buys_amount | process_ret_ι_buys_ | process_ret_ι_ret_ .
(* 2 *) Definition process_retP := 
 ( I128 * 
 Q OrderInfoP * 
 I128 * 
 Q OrderInfoP * 
 M OrderRetP )%type .
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

(* 1 *) Inductive PriceFields := | Price_ι_price_ | Price_ι_sells_amount_ | Price_ι_buys_amount_ | Price_ι_flex_ | Price_ι_min_amount_ | Price_ι_deals_limit_ | Price_ι_notify_addr_ | Price_ι_workchain_id_ | Price_ι_tons_cfg_ | Price_ι_tip3_code_ | Price_ι_tip3cfg_ | Price_ι_sells_ | Price_ι_buys_ .
(* 2 *) Definition PriceP := 
 ( I128 * 
 I128 * 
 I128 * 
 addr_std_fixedP * 
 I128 * 
 I8 * 
 I16 (* handle<IFLeXNotify> *) * 
 I8 * 
 TonsConfigP * 
 C * 
 Tip3ConfigP * 
 Q OrderInfoP * 
 Q OrderInfoP )%type .

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

(* 1 *) Inductive PriceXchgFields := | PriceXchg_ι_price_ | PriceXchg_ι_sells_amount_ | PriceXchg_ι_buys_amount_ | PriceXchg_ι_flex_ | PriceXchg_ι_min_amount_ | PriceXchg_ι_deals_limit_ | PriceXchg_ι_notify_addr_ | PriceXchg_ι_workchain_id_ | PriceXchg_ι_tons_cfg_ | PriceXchg_ι_tip3_code_ | PriceXchg_ι_major_tip3cfg_ | PriceXchg_ι_minor_tip3cfg_ | PriceXchg_ι_sells_ | PriceXchg_ι_buys_ .
(* 2 *) Definition PriceXchgP := 
 ( RationalPriceP * 
 I128 * 
 I128 * 
 addr_std_fixedP * 
 I128 * 
 I8 * 
 H I16 (* IFLeXNotify *)  * 
 I8 * 
 TonsConfigP * 
 C * 
 Tip3ConfigP * 
 Tip3ConfigP * 
 Bq OrderInfoXchgP * 
 Bq OrderInfoXchgP )%type .

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
(* 1 *) Inductive VMCommitFields := | VMCommit_ι_FLeX | VMCommit_ι_FLeXClient | VMCommit_ι_Price | VMCommit_ι_PriceXchg .
(* 2 *) Definition VMCommitP := 
 ( FLeXP * 
 FLeXClientP * 
 PriceP * 
 PriceXchgP )%type .

(* 1 *) Inductive LocalStateFields := | LocalState_ι_uint256 | LocalState_ι_cell | LocalState_ι_TonsConfig | LocalState_ι_address | LocalState_ι_uint128 | LocalState_ι_StateInit | LocalState_ι_DTradingPair | LocalState_ι_handle_ITradingPair_ | LocalState_ι_DXchgPair | LocalState_ι_handle_IXchgPair_ | LocalState_ι_parse_FLeXSellArgs_ | LocalState_ι_handle_IPrice_ | LocalState_ι_SellArgs | LocalState_ι_parse_FLeXBuyArgs_ | LocalState_ι_parse_FLeXCancelArgs_ | LocalState_ι_parse_FLeXXchgCancelArgs_ | LocalState_ι_handle_IPriceXchg_ | LocalState_ι_bool_t | LocalState_ι_parse_FLeXXchgArgs_ | LocalState_ι_PayloadArgs | LocalState_ι_handle_ITONTokenWallet_ | LocalState_ι_uint8 | LocalState_ι_Tip3Config | LocalState_ι_DPrice | LocalState_ι_DPriceXchg | LocalState_ι_tuple_address_address | LocalState_ι_uint32 | LocalState_ι_unsigned | LocalState_ι_OrderInfo | LocalState_ι_int | LocalState_ι_optional_uint128_ | LocalState_ι_bool 
| LocalState_ι_optional_OrderInfoWithIdx_ 
| LocalState_ι_queue_OrderInfo_ 
| LocalState_ι_pair_unsigned_OrderInfo_ 

| LocalState_ι_uint256Index 
| LocalState_ι_cellIndex 
| LocalState_ι_TonsConfigIndex 
| LocalState_ι_addressIndex 
| LocalState_ι_uint128Index 
| LocalState_ι_StateInitIndex 
| LocalState_ι_DTradingPairIndex 
| LocalState_ι_handle_ITradingPair_Index 
| LocalState_ι_DXchgPairIndex 
| LocalState_ι_handle_IXchgPair_Index 
| LocalState_ι_parse_FLeXSellArgs_Index 
| LocalState_ι_handle_IPrice_Index 
| LocalState_ι_SellArgsIndex 
| LocalState_ι_parse_FLeXBuyArgs_Index 
| LocalState_ι_parse_FLeXCancelArgs_Index 
| LocalState_ι_parse_FLeXXchgCancelArgs_Index 
| LocalState_ι_handle_IPriceXchg_Index 
| LocalState_ι_bool_tIndex 
| LocalState_ι_parse_FLeXXchgArgs_Index 
| LocalState_ι_PayloadArgsIndex 
| LocalState_ι_handle_ITONTokenWallet_Index 
| LocalState_ι_uint8Index 
| LocalState_ι_Tip3ConfigIndex 
| LocalState_ι_DPriceIndex 
| LocalState_ι_DPriceXchgIndex | LocalState_ι_tuple_address_addressIndex | LocalState_ι_uint32Index | LocalState_ι_unsignedIndex | LocalState_ι_OrderInfoIndex | LocalState_ι_intIndex | LocalState_ι_optional_uint128_Index | LocalState_ι_boolIndex | LocalState_ι_optional_OrderInfoWithIdx_Index | LocalState_ι_queue_OrderInfo_Index | LocalState_ι_pair_unsigned_OrderInfo_Index .
(* 2 *) Definition LocalStateP := 
 ( HM (string*nat) I256 * 
 HM (string*nat) C * 
 HM (string*nat) TonsConfigP * 
 HM (string*nat) A * 
 HM (string*nat) I128 * 
 HM (string*nat) StateInitP * 
 HM (string*nat) DTradingPairP * 
 HM (string*nat) I16 (* handle_ITradingPair_P *) * 
 HM (string*nat) DXchgPairP * 
 HM (string*nat) I16 (* handle_IXchgPair_P *) * 
 HM (string*nat) I16 (* parse_FLeXSellArgs_P *) * 
 HM (string*nat) I16 (* handle_IPrice_P *) * 
 HM (string*nat) SellArgsP * 
 HM (string*nat) I16 (* parse_FLeXBuyArgs_P *) * 
 HM (string*nat) I16 (* parse_FLeXCancelArgs_P *) * 
 HM (string*nat) I16 (* parse_FLeXXchgCancelArgs_P *) * 
 HM (string*nat) I16 (* handle_IPriceXchg_P *) * 
 HM (string*nat) B * 
 HM (string*nat) I16 (* parse_FLeXXchgArgs_P *) * 
 HM (string*nat) PayloadArgsP * 
 HM (string*nat) I16 (* handle_ITONTokenWallet_P *) * 
 HM (string*nat) I8 * 
 HM (string*nat) Tip3ConfigP * 
 HM (string*nat) PriceP * 
 HM (string*nat) PriceXchgP * 
 HM (string*nat) (A*A) * 
 HM (string*nat) I32 * 
 HM (string*nat) I * 
 HM (string*nat) OrderInfoP * 
 HM (string*nat) I * 
 HM (string*nat) (M I128) * 
 HM (string*nat) B * 
 HM (string*nat) (M (I*OrderInfoP)) * 
 HM (string*nat) I16 (* queue_OrderInfo_P *) * 
 HM (string*nat) (I*OrderInfoP) * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat * 
 HM string nat )%type .


(* 1 *) Inductive LedgerFieldsI := | Ledger_ι_FLeX | Ledger_ι_FLeXClient | Ledger_ι_Price | Ledger_ι_PriceXchg | Ledger_ι_VMCommit | Ledger_ι_LocalState | Ledger_ι_LocalStateCopy .
(* 2 *) Definition LedgerP := 
 ( FLeXP * 
 FLeXClientP * 
 PriceP * 
 PriceXchgP * 
 VMCommitP * 
 LocalStateP * 
 LocalStateP )%type .
Notation "'{$$' r 'With' y ':=' v '$$}'" := (@setPruvendoRecord _ _ _ y v r) : struct_scope.

End RecordsDefinitions .

Require Import UMLang.ProofEnvironment2.


Module LedgerClass (xt: XTypesSig) (sm: StateMonadSig) <: ClassSig xt.


Module Export SolidityNotationsClass := SolidityNotations xt  sm.
Import xt. 
Existing Instance monadStateT. 
Existing Instance monadStateStateT.
Print FLeXXchgCfgsP.
Definition FLeXXchgCfgs := @ FLeXXchgCfgsP 
XInteger8 XInteger256 XAddress XString XMaybe.

Definition TickTock := @ TickTockP
XBool
.
Definition allowance_info := @ allowance_infoP
XInteger256 XAddress
.
Definition StateInit := @ StateInitP
XInteger8 XBool TvmCell XMaybe
.
Definition DTONTokenWallet := @ DTONTokenWalletP
XInteger8 XInteger128 XInteger256 XAddress TvmCell XList XMaybe
.
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
Definition dealer := @ dealerP
XInteger XInteger8     XInteger16     XInteger32  XInteger128 XInteger256 XAddress XMaybe XMaybe
.
Definition FLeXSellArgsAddrs := @ FLeXSellArgsAddrsP
XAddress
.
Definition Tip3Config := @ Tip3ConfigP
XInteger8 XInteger256 XAddress XString
. 
Print FLeXSellArgsP.
Definition FLeXSellArgs := @ FLeXSellArgsP
XInteger8 XInteger32 XInteger128 XInteger256 XAddress TvmCell XString XMaybe
.
Print FLeXBuyArgsP .
Definition FLeXBuyArgs := @ FLeXBuyArgsP
XInteger8 XInteger32 XInteger128 XInteger256 XAddress TvmCell XString XMaybe
. 
Print FLeXXchgArgsP .
Definition FLeXXchgArgs := @ FLeXXchgArgsP
XInteger8 XInteger32 XInteger128 XInteger256 XAddress XBool TvmCell XString XMaybe
.
Print FLeXCancelArgsP .
Definition FLeXCancelArgs := @ FLeXCancelArgsP
XInteger8 XInteger128 XInteger256 XAddress TvmCell XString XMaybe
.
Definition FLeXXchgCancelArgs := @ FLeXXchgCancelArgsP
XInteger8 XInteger128 XBool TvmCell
.
Definition FLeXClient := @ FLeXClientP
XInteger8 XInteger128 XInteger256 XAddress TvmCell
.
Definition FLeX := @ FLeXP
XInteger8 XInteger128 XInteger256 XAddress TvmCell XMaybe
.
Print process_retP .
Definition process_ret := @ process_retP
XInteger8 XInteger32 XInteger128 XInteger256 XMaybe XMaybe
.
Definition SellArgs := @ SellArgsP
XInteger8 XInteger128 XInteger256
.
Definition DetailsInfo := @ DetailsInfoP
XInteger128
.

Print PriceP.
Definition Price := @ PriceP
XInteger8   XInteger16  XInteger32  XInteger128 XInteger256 XAddress TvmCell XString XMaybe
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
Print PriceXchgP .
Definition PriceXchg := @ PriceXchgP
XInteger8   XInteger16  XInteger32  XInteger128 XInteger256 XAddress TvmCell XString XMaybe XMaybe
.
Definition DTradingPair := @ DTradingPairP
XInteger128 XAddress
.
Definition DXchgPair := @ DXchgPairP
XInteger128 XAddress
.
Print VMCommitP .
Definition VMCommit := @ VMCommitP
XInteger8    XInteger16  XInteger32  XInteger128 XInteger256 XAddress TvmCell XString XMaybe XMaybe XMaybe XMaybe 
. 
Print LocalStateP .
Definition LocalState := @ LocalStateP
XInteger XInteger8    XInteger16    XInteger32 XInteger128 XInteger256 XAddress XBool TvmCell XString XMaybe XMaybe XMaybe XMaybe XHMap
.
Print LedgerP .
Definition Ledger := @ LedgerP
XInteger XInteger8    XInteger16    XInteger32 XInteger128 XInteger256 XAddress XBool TvmCell XString XMaybe XMaybe XMaybe XMaybe XHMap
.
Definition LedgerFields := LedgerFieldsI.

Global Instance FLeXXchgCfgs_default : XDefault FLeXXchgCfgs := { 
  	 default := ( default , default ) } .
Global Instance TickTock_default : XDefault TickTock := { 
  	 default := ( default , default ) } .
Global Instance allowance_info_default : XDefault allowance_info := { 
  	 default := ( default , default ) } .
Global Instance StateInit_default : XDefault StateInit := { 
  	 default := ( default , default , default , default , default ) } .
Global Instance DTONTokenWallet_default : XDefault DTONTokenWallet := { 
  	 default := ( default , default , default , default , default , default , default , default , default , default , default ) } .
Global Instance TonsConfig_default : XDefault TonsConfig := { 
  	 default := ( default , default , default , default , default , default ) } .
Global Instance addr_std_fixed_default : XDefault addr_std_fixed := { 
  	 default := ( default , default ) } .
Global Instance OrderInfo_default : XDefault OrderInfo := { 
  	 default := ( default , default , default , default , default , default ) } .
Global Instance OrderRet_default : XDefault OrderRet := { 
  	 default := ( default , default , default ) } .
Global Instance dealer_default : XDefault dealer := { 
  	 default := ( default , default , default , default , default , default , default , default ) } .
Global Instance FLeXSellArgsAddrs_default : XDefault FLeXSellArgsAddrs := { 
  	 default := ( default , default ) } .
Global Instance Tip3Config_default : XDefault Tip3Config := { 
  	 default := ( default , default , default , default , default ) } .
Global Instance FLeXSellArgs_default : XDefault FLeXSellArgs := { 
  	 default := ( default , default , default , default , default , default , default , default , default , default ) } .
Global Instance FLeXBuyArgs_default : XDefault FLeXBuyArgs := { 
  	 default := ( default , default , default , default , default , default , default , default , default , default ) } .
Global Instance FLeXXchgArgs_default : XDefault FLeXXchgArgs := { 
  	 default := ( default , default , default , default , default , default , default , default , default , default , default , default , default ) } .
Global Instance FLeXCancelArgs_default : XDefault FLeXCancelArgs := { 
  	 default := ( default , default , default , default , default , default , default ) } .
Global Instance FLeXXchgCancelArgs_default : XDefault FLeXXchgCancelArgs := { 
  	 default := ( default , default , default , default , default , default , default , default ) } .
Global Instance FLeXClient_default : XDefault FLeXClient := { 
  	 default := ( default , default , default , default , default , default , default ) } .
Global Instance FLeX_default : XDefault FLeX := { 
  	 default := ( default , default , default , default , default , default , default , default , default ) } .
Global Instance process_ret_default : XDefault process_ret := { 
  	 default := ( default , default , default , default , default ) } .
Global Instance SellArgs_default : XDefault SellArgs := { 
  	 default := ( default , default ) } .
Global Instance DetailsInfo_default : XDefault DetailsInfo := { 
  	 default := ( default , default , default , default ) } . 
Global Instance Price_default : XDefault Price := { 
  	 default := ( default , default , default , default , default , default , default , default , default , default , default ) } .
Global Instance RationalPrice_default : XDefault RationalPrice := { 
  	 default := ( default , default ) } .
Global Instance PayloadArgs_default : XDefault PayloadArgs := { 
  	 default := ( default , default , default , default ) } .
Global Instance OrderInfoXchg_default : XDefault OrderInfoXchg := { 
  	 default := ( default , default , default , default , default , default , default ) } .
Global Instance DetailsInfoXchg_default : XDefault DetailsInfoXchg := { 
  	 default := ( default , default , default , default , default ) } .
Global Instance PriceXchg_default : XDefault PriceXchg := { 
  	 default := ( default , default , default , default , default , default , default , default , default , default , default , default , default , default ) } .
Global Instance DTradingPair_default : XDefault DTradingPair := { 
  	 default := ( default , default , default ) } .
Global Instance DXchgPair_default : XDefault DXchgPair := { 
  	 default := ( default , default , default , default ) } .
Global Instance VMCommit_default : XDefault VMCommit := { 
  	 default := ( default , default , default , default ) } .
Global Instance LocalState_default : XDefault LocalState := { 
  	 default := ( default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default ,
                  default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default , default) } .
Global Instance Ledger_default : XDefault Ledger := { 
  	 default := ( default , default , default , default , default , default , default ) } .

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
Notation " 'fst41' x " := ( fst ( fst40 x ) ) (at level 60, right associativity).
Notation " 'fst42' x " := ( fst ( fst41 x ) ) (at level 60, right associativity).
Notation " 'fst43' x " := ( fst ( fst42 x ) ) (at level 60, right associativity).
Notation " 'fst44' x " := ( fst ( fst43 x ) ) (at level 60, right associativity).
Notation " 'fst45' x " := ( fst ( fst44 x ) ) (at level 60, right associativity).
Notation " 'fst46' x " := ( fst ( fst45 x ) ) (at level 60, right associativity).
Notation " 'fst47' x " := ( fst ( fst46 x ) ) (at level 60, right associativity).
Notation " 'fst48' x " := ( fst ( fst47 x ) ) (at level 60, right associativity).
Notation " 'fst49' x " := ( fst ( fst48 x ) ) (at level 60, right associativity).
Notation " 'fst50' x " := ( fst ( fst49 x ) ) (at level 60, right associativity).
Notation " 'fst51' x " := ( fst ( fst50 x ) ) (at level 60, right associativity).
Notation " 'fst52' x " := ( fst ( fst51 x ) ) (at level 60, right associativity).
Notation " 'fst53' x " := ( fst ( fst52 x ) ) (at level 60, right associativity).
Notation " 'fst54' x " := ( fst ( fst53 x ) ) (at level 60, right associativity).
Notation " 'fst55' x " := ( fst ( fst54 x ) ) (at level 60, right associativity).
Notation " 'fst56' x " := ( fst ( fst55 x ) ) (at level 60, right associativity).
Notation " 'fst57' x " := ( fst ( fst56 x ) ) (at level 60, right associativity).
Notation " 'fst58' x " := ( fst ( fst57 x ) ) (at level 60, right associativity).
Notation " 'fst59' x " := ( fst ( fst58 x ) ) (at level 60, right associativity).
Notation " 'fst60' x " := ( fst ( fst59 x ) ) (at level 60, right associativity).
Notation " 'fst61' x " := ( fst ( fst60 x ) ) (at level 60, right associativity).
Notation " 'fst62' x " := ( fst ( fst61 x ) ) (at level 60, right associativity).
Notation " 'fst63' x " := ( fst ( fst62 x ) ) (at level 60, right associativity).
Notation " 'fst64' x " := ( fst ( fst63 x ) ) (at level 60, right associativity).
Notation " 'fst65' x " := ( fst ( fst64 x ) ) (at level 60, right associativity).
Notation " 'fst66' x " := ( fst ( fst65 x ) ) (at level 60, right associativity).
Notation " 'fst67' x " := ( fst ( fst66 x ) ) (at level 60, right associativity).
Notation " 'fst68' x " := ( fst ( fst67 x ) ) (at level 60, right associativity).
Notation " 'fst69' x " := ( fst ( fst68 x ) ) (at level 60, right associativity).
Notation " 'fst70' x " := ( fst ( fst69 x ) ) (at level 60, right associativity).
Notation " 'fst71' x " := ( fst ( fst70 x ) ) (at level 60, right associativity).
Notation " 'fst72' x " := ( fst ( fst71 x ) ) (at level 60, right associativity).
Notation " 'fst73' x " := ( fst ( fst72 x ) ) (at level 60, right associativity).
Notation " 'fst74' x " := ( fst ( fst73 x ) ) (at level 60, right associativity).
Notation " 'fst75' x " := ( fst ( fst74 x ) ) (at level 60, right associativity).
Notation " 'fst76' x " := ( fst ( fst75 x ) ) (at level 60, right associativity).
Notation " 'fst77' x " := ( fst ( fst76 x ) ) (at level 60, right associativity).
Notation " 'fst78' x " := ( fst ( fst77 x ) ) (at level 60, right associativity).
Notation " 'fst79' x " := ( fst ( fst78 x ) ) (at level 60, right associativity).
Notation " 'fst80' x " := ( fst ( fst79 x ) ) (at level 60, right associativity).
Notation " 'fst81' x " := ( fst ( fst80 x ) ) (at level 60, right associativity).
Notation " 'fst82' x " := ( fst ( fst81 x ) ) (at level 60, right associativity).
Notation " 'fst83' x " := ( fst ( fst82 x ) ) (at level 60, right associativity).
Notation " 'fst84' x " := ( fst ( fst83 x ) ) (at level 60, right associativity).
Notation " 'fst85' x " := ( fst ( fst84 x ) ) (at level 60, right associativity).
Notation " 'fst86' x " := ( fst ( fst85 x ) ) (at level 60, right associativity).
Notation " 'fst87' x " := ( fst ( fst86 x ) ) (at level 60, right associativity).
Notation " 'fst88' x " := ( fst ( fst87 x ) ) (at level 60, right associativity).
Notation " 'fst89' x " := ( fst ( fst88 x ) ) (at level 60, right associativity).
Notation " 'fst90' x " := ( fst ( fst89 x ) ) (at level 60, right associativity).
Notation " 'fst91' x " := ( fst ( fst90 x ) ) (at level 60, right associativity).
Notation " 'fst92' x " := ( fst ( fst91 x ) ) (at level 60, right associativity).
Notation " 'fst93' x " := ( fst ( fst92 x ) ) (at level 60, right associativity).
Notation " 'fst94' x " := ( fst ( fst93 x ) ) (at level 60, right associativity).
Notation " 'fst95' x " := ( fst ( fst94 x ) ) (at level 60, right associativity).
Notation " 'fst96' x " := ( fst ( fst95 x ) ) (at level 60, right associativity).
Notation " 'fst97' x " := ( fst ( fst96 x ) ) (at level 60, right associativity).
Notation " 'fst98' x " := ( fst ( fst97 x ) ) (at level 60, right associativity).
Notation " 'fst99' x " := ( fst ( fst98 x ) ) (at level 60, right associativity).
Notation " 'fst100' x " := ( fst ( fst99 x ) ) (at level 60, right associativity).
(* 3 *) Definition FLeXXchgCfgs_field_type f : Type :=  
match f with 
 | FLeXXchgCfgs_ι_major_tip3cfg => XMaybe (* XReference *) Tip3Config | FLeXXchgCfgs_ι_minor_tip3cfg => XMaybe (* XReference *) Tip3Config end .
(* 4 *) Definition FLeXXchgCfgs_get (f: FLeXXchgCfgsFields )(r: FLeXXchgCfgs ) :  FLeXXchgCfgs_field_type f := 
 match f with 
 | FLeXXchgCfgs_ι_major_tip3cfg => fst1 r 
 | FLeXXchgCfgs_ι_minor_tip3cfg => snd r 
 end .
(* 5 *) Coercion FLeXXchgCfgs_get : FLeXXchgCfgsFields >-> Funclass .
(* 6 *) Definition FLeXXchgCfgs_set (f: FLeXXchgCfgsFields ) 
(v: FLeXXchgCfgs_field_type f) (r: FLeXXchgCfgs ): FLeXXchgCfgs  :=
  match f, v with | FLeXXchgCfgs_ι_major_tip3cfg , v' => ( v' , snd r ) 
 | FLeXXchgCfgs_ι_minor_tip3cfg , v' => ( fst1 r , v' ) 
 end .
(* 7 *) Global Instance FLeXXchgCfgs_PruvendoRecord : PruvendoRecord FLeXXchgCfgs FLeXXchgCfgsFields :=
{
  field_type := FLeXXchgCfgs_field_type; 
  getPruvendoRecord := @FLeXXchgCfgs_get ;
  setPruvendoRecord := @FLeXXchgCfgs_set ;
} .
(* 3 *) Definition TickTock_field_type f : Type :=  
match f with | TickTock_ι_tick => XBool | TickTock_ι_tock => XBool end .
(* 4 *) Definition TickTock_get (f: TickTockFields )(r: TickTock ) :  TickTock_field_type f := 
 match f , r with 
 | TickTock_ι_tick , (r1,r2) => r1 
 | TickTock_ι_tock , (r1,r2)  => r2 
 end .
(* 5 *) Coercion TickTock_get : TickTockFields >-> Funclass .
(* 6 *) Definition TickTock_set (f: TickTockFields ) 
(v: TickTock_field_type f) (r: TickTock ): TickTock  :=
  match f, v with 
 | TickTock_ι_tick , v' => ( v' , snd r ) 
 | TickTock_ι_tock , v' => ( fst1 r , v' ) 
 end .
(* 7 *) Global Instance TickTock_PruvendoRecord : PruvendoRecord TickTock TickTockFields :=
{
  field_type := TickTock_field_type; 
  getPruvendoRecord := @TickTock_get ;
  setPruvendoRecord := @TickTock_set ;
} .
(* 3 *) Definition allowance_info_field_type f : Type :=  
match f with | allowance_info_ι_spender => XAddress | allowance_info_ι_remainingTokens => XInteger256 end .
(* 4 *) Definition allowance_info_get (f: allowance_infoFields )(r: allowance_info ) :  allowance_info_field_type f := 
 match f with | allowance_info_ι_spender => fst1 r 
 | allowance_info_ι_remainingTokens => snd r 
 end .
(* 5 *) Coercion allowance_info_get : allowance_infoFields >-> Funclass .
(* 6 *) Definition allowance_info_set (f: allowance_infoFields ) 
(v: allowance_info_field_type f) (r: allowance_info ): allowance_info  :=
  match f, v with | allowance_info_ι_spender , v' => ( v' , snd r ) 
 | allowance_info_ι_remainingTokens , v' => ( fst1 r , v' ) 
 end .
(* 7 *) Global Instance allowance_info_PruvendoRecord : PruvendoRecord allowance_info allowance_infoFields :=
{
  field_type := allowance_info_field_type; 
  getPruvendoRecord := @allowance_info_get ;
  setPruvendoRecord := @allowance_info_set ;
} .
(* 3 *) Definition StateInit_field_type f : Type :=  
match f with 
| StateInit_ι_split_depth => XMaybe XInteger8 
| StateInit_ι_special => XMaybe TickTock 
| StateInit_ι_code => XMaybe TvmCell 
| StateInit_ι_data => XMaybe TvmCell 
| StateInit_ι_library => XMaybe TvmCell 
end .
(* 4 *) Definition StateInit_get (f: StateInitFields )(r: StateInit ) :  StateInit_field_type f := 
 match f with | StateInit_ι_split_depth => fst4 r 
 | StateInit_ι_special => snd ( fst3 r ) 
 | StateInit_ι_code => snd ( fst2 r ) 
 | StateInit_ι_data => snd ( fst1 r ) 
 | StateInit_ι_library => snd r 
 end .
(* 5 *) Coercion StateInit_get : StateInitFields >-> Funclass .
(* 6 *) Definition StateInit_set (f: StateInitFields ) 
(v: StateInit_field_type f) (r: StateInit ): StateInit  :=
  match f, v with | StateInit_ι_split_depth , v' => ( v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | StateInit_ι_special , v' => ( fst4 r , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | StateInit_ι_code , v' => ( fst4 r , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | StateInit_ι_data , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | StateInit_ι_library , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance StateInit_PruvendoRecord : PruvendoRecord StateInit StateInitFields :=
{
  field_type := StateInit_field_type; 
  getPruvendoRecord := @StateInit_get ;
  setPruvendoRecord := @StateInit_set ;
} .
(* 3 *) Definition DTONTokenWallet_field_type f : Type :=  
match f with | DTONTokenWallet_ι_name_ => XList XInteger8 | DTONTokenWallet_ι_symbol_ => XList XInteger8 | DTONTokenWallet_ι_decimals_ => XInteger8 | DTONTokenWallet_ι_balance_ => XInteger128 | DTONTokenWallet_ι_root_public_key_ => XInteger256 | DTONTokenWallet_ι_wallet_public_key_ => XInteger256 | DTONTokenWallet_ι_root_address_ => XAddress | DTONTokenWallet_ι_owner_address_ => XMaybe XAddress | DTONTokenWallet_ι_code_ => TvmCell | DTONTokenWallet_ι_allowance_ => XMaybe allowance_info | DTONTokenWallet_ι_workchain_id_ => XInteger8 end .
(* 4 *) Definition DTONTokenWallet_get (f: DTONTokenWalletFields )(r: DTONTokenWallet ) :  DTONTokenWallet_field_type f := 
 match f with | DTONTokenWallet_ι_name_ => fst10 r 
 | DTONTokenWallet_ι_symbol_ => snd ( fst9 r ) 
 | DTONTokenWallet_ι_decimals_ => snd ( fst8 r ) 
 | DTONTokenWallet_ι_balance_ => snd ( fst7 r ) 
 | DTONTokenWallet_ι_root_public_key_ => snd ( fst6 r ) 
 | DTONTokenWallet_ι_wallet_public_key_ => snd ( fst5 r ) 
 | DTONTokenWallet_ι_root_address_ => snd ( fst4 r ) 
 | DTONTokenWallet_ι_owner_address_ => snd ( fst3 r ) 
 | DTONTokenWallet_ι_code_ => snd ( fst2 r ) 
 | DTONTokenWallet_ι_allowance_ => snd ( fst1 r ) 
 | DTONTokenWallet_ι_workchain_id_ => snd r 
 end .
(* 5 *) Coercion DTONTokenWallet_get : DTONTokenWalletFields >-> Funclass .
(* 6 *) Definition DTONTokenWallet_set (f: DTONTokenWalletFields ) 
(v: DTONTokenWallet_field_type f) (r: DTONTokenWallet ): DTONTokenWallet  :=
  match f, v with | DTONTokenWallet_ι_name_ , v' => ( v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DTONTokenWallet_ι_symbol_ , v' => ( fst10 r , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DTONTokenWallet_ι_decimals_ , v' => ( fst10 r , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DTONTokenWallet_ι_balance_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DTONTokenWallet_ι_root_public_key_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DTONTokenWallet_ι_wallet_public_key_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DTONTokenWallet_ι_root_address_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DTONTokenWallet_ι_owner_address_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | DTONTokenWallet_ι_code_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | DTONTokenWallet_ι_allowance_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | DTONTokenWallet_ι_workchain_id_ , v' => ( fst10 r , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance DTONTokenWallet_PruvendoRecord : PruvendoRecord DTONTokenWallet DTONTokenWalletFields :=
{
  field_type := DTONTokenWallet_field_type; 
  getPruvendoRecord := @DTONTokenWallet_get ;
  setPruvendoRecord := @DTONTokenWallet_set ;
} .
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
match f with 
 | dealer_ι_tip3root_ => XAddress | dealer_ι_notify_addr_ => XInteger16 (* IFLeXNotifyPtr *) | dealer_ι_price_ => XInteger128 | dealer_ι_deals_limit_ => XInteger | dealer_ι_tons_cfg_ => TonsConfig | dealer_ι_sells_amount_ => XInteger128 | dealer_ι_sells_ => XMaybe (* XQueue *) OrderInfo | dealer_ι_buys_amount_ => XInteger128 | dealer_ι_buys_ => XMaybe (* XQueue *) OrderInfo | dealer_ι_ret_ => XMaybe OrderRet end .
(* 4 *) Definition dealer_get (f: dealerFields )(r: dealer ) :  dealer_field_type f := 
 match f  with 
 | dealer_ι_tip3root_ => fst9 r 
 | dealer_ι_notify_addr_ => snd ( fst8 r ) 
 | dealer_ι_price_ => snd ( fst7 r ) 
 | dealer_ι_deals_limit_ => snd ( fst6 r ) 
 | dealer_ι_tons_cfg_ => snd ( fst5 r ) 
 | dealer_ι_sells_amount_ => snd ( fst4 r ) 
 | dealer_ι_sells_ => snd ( fst3 r ) 
 | dealer_ι_buys_amount_ => snd ( fst2 r ) 
 | dealer_ι_buys_ => snd ( fst1 r ) 
 | dealer_ι_ret_ => snd r 
 end .
(* 5 *) Coercion dealer_get : dealerFields >-> Funclass .
(* 6 *) Definition dealer_set (f: dealerFields ) 
(v: dealer_field_type f) (r: dealer ): dealer  :=
  match f, v with | dealer_ι_tip3root_ , v' => ( v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_notify_addr_ , v' => ( fst9 r , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_price_ , v' => ( fst9 r , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_deals_limit_ , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_tons_cfg_ , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_sells_amount_ , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_sells_ , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | dealer_ι_buys_amount_ , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | dealer_ι_buys_ , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | dealer_ι_ret_ , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
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
match f with 
 | FLeXSellArgs_ι_price => XInteger128 | FLeXSellArgs_ι_amount => XInteger128 | FLeXSellArgs_ι_lend_finish_time => XInteger32 | FLeXSellArgs_ι_min_amount => XInteger128 | FLeXSellArgs_ι_deals_limit => XInteger8 | FLeXSellArgs_ι_tons_value => XInteger128 | FLeXSellArgs_ι_price_code => TvmCell | FLeXSellArgs_ι_addrs => XMaybe (* XReference *) FLeXSellArgsAddrs | FLeXSellArgs_ι_tip3_code => TvmCell | FLeXSellArgs_ι_tip3cfg => XMaybe (* XReference *) Tip3Config end .
(* 4 *) Definition FLeXSellArgs_get (f: FLeXSellArgsFields )(r: FLeXSellArgs ) :  FLeXSellArgs_field_type f := 
 match f with 
 | FLeXSellArgs_ι_price => fst9 r 
 | FLeXSellArgs_ι_amount => snd ( fst8 r ) 
 | FLeXSellArgs_ι_lend_finish_time => snd ( fst7 r ) 
 | FLeXSellArgs_ι_min_amount => snd ( fst6 r ) 
 | FLeXSellArgs_ι_deals_limit => snd ( fst5 r ) 
 | FLeXSellArgs_ι_tons_value => snd ( fst4 r ) 
 | FLeXSellArgs_ι_price_code => snd ( fst3 r ) 
 | FLeXSellArgs_ι_addrs => snd ( fst2 r ) 
 | FLeXSellArgs_ι_tip3_code => snd ( fst1 r ) 
 | FLeXSellArgs_ι_tip3cfg => snd r 
 end .
(* 5 *) Coercion FLeXSellArgs_get : FLeXSellArgsFields >-> Funclass .
(* 6 *) Definition FLeXSellArgs_set (f: FLeXSellArgsFields ) 
(v: FLeXSellArgs_field_type f) (r: FLeXSellArgs ): FLeXSellArgs  :=
  match f, v with | FLeXSellArgs_ι_price , v' => ( v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_amount , v' => ( fst9 r , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_lend_finish_time , v' => ( fst9 r , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_min_amount , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_deals_limit , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_tons_value , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_price_code , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_addrs , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXSellArgs_ι_tip3_code , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXSellArgs_ι_tip3cfg , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .

(* 7 *) Global Instance FLeXSellArgs_PruvendoRecord : PruvendoRecord FLeXSellArgs FLeXSellArgsFields :=
{
  field_type := FLeXSellArgs_field_type; 
  getPruvendoRecord := @FLeXSellArgs_get ;
  setPruvendoRecord := @FLeXSellArgs_set ;
} .

(* 3 *) Definition FLeXBuyArgs_field_type f : Type :=  
match f with 
 | FLeXBuyArgs_ι_price => XInteger128 | FLeXBuyArgs_ι_amount => XInteger128 | FLeXBuyArgs_ι_order_finish_time => XInteger32 | FLeXBuyArgs_ι_min_amount => XInteger128 | FLeXBuyArgs_ι_deals_limit => XInteger8 | FLeXBuyArgs_ι_deploy_value => XInteger128 | FLeXBuyArgs_ι_price_code => TvmCell | FLeXBuyArgs_ι_my_tip3_addr => XAddress | FLeXBuyArgs_ι_tip3_code => TvmCell | FLeXBuyArgs_ι_tip3cfg => XMaybe (* XReference *) Tip3Config end .
(* 4 *) Definition FLeXBuyArgs_get (f: FLeXBuyArgsFields )(r: FLeXBuyArgs ) :  FLeXBuyArgs_field_type f := 
 match f  with 
 | FLeXBuyArgs_ι_price => fst9 r 
 | FLeXBuyArgs_ι_amount => snd ( fst8 r ) 
 | FLeXBuyArgs_ι_order_finish_time => snd ( fst7 r ) 
 | FLeXBuyArgs_ι_min_amount => snd ( fst6 r ) 
 | FLeXBuyArgs_ι_deals_limit => snd ( fst5 r ) 
 | FLeXBuyArgs_ι_deploy_value => snd ( fst4 r ) 
 | FLeXBuyArgs_ι_price_code => snd ( fst3 r ) 
 | FLeXBuyArgs_ι_my_tip3_addr => snd ( fst2 r ) 
 | FLeXBuyArgs_ι_tip3_code => snd ( fst1 r ) 
 | FLeXBuyArgs_ι_tip3cfg => snd r 
 end .
(* 5 *) Coercion FLeXBuyArgs_get : FLeXBuyArgsFields >-> Funclass .
(* 6 *) Definition FLeXBuyArgs_set (f: FLeXBuyArgsFields ) 
(v: FLeXBuyArgs_field_type f) (r: FLeXBuyArgs ): FLeXBuyArgs  :=
  match f, v with | FLeXBuyArgs_ι_price , v' => ( v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_amount , v' => ( fst9 r , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_order_finish_time , v' => ( fst9 r , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_min_amount , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_deals_limit , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_deploy_value , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_price_code , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_my_tip3_addr , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXBuyArgs_ι_tip3_code , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXBuyArgs_ι_tip3cfg , v' => ( fst9 r , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .

(* 7 *) Global Instance FLeXBuyArgs_PruvendoRecord : PruvendoRecord FLeXBuyArgs FLeXBuyArgsFields :=
{
  field_type := FLeXBuyArgs_field_type; 
  getPruvendoRecord := @FLeXBuyArgs_get ;
  setPruvendoRecord := @FLeXBuyArgs_set ;
} .
 
(* 3 *) Definition FLeXXchgArgs_field_type f : Type :=  
match f with 
 | FLeXXchgArgs_ι_sell => XBool | FLeXXchgArgs_ι_price_num => XInteger128 | FLeXXchgArgs_ι_price_denum => XInteger128 | FLeXXchgArgs_ι_amount => XInteger128 | FLeXXchgArgs_ι_lend_amount => XInteger128 | FLeXXchgArgs_ι_lend_finish_time => XInteger32 | FLeXXchgArgs_ι_min_amount => XInteger128 | FLeXXchgArgs_ι_deals_limit => XInteger8 | FLeXXchgArgs_ι_tons_value => XInteger128 | FLeXXchgArgs_ι_xchg_price_code => TvmCell | FLeXXchgArgs_ι_addrs => XMaybe (* XReference *) FLeXSellArgsAddrs | FLeXXchgArgs_ι_tip3_code => TvmCell | FLeXXchgArgs_ι_tip3cfgs => XMaybe (* XReference *) FLeXXchgCfgs end .
(* 4 *) Definition FLeXXchgArgs_get (f: FLeXXchgArgsFields )(r: FLeXXchgArgs ) :  FLeXXchgArgs_field_type f := 
 match f with 
 | FLeXXchgArgs_ι_sell => fst12 r 
 | FLeXXchgArgs_ι_price_num => snd ( fst11 r ) 
 | FLeXXchgArgs_ι_price_denum => snd ( fst10 r ) 
 | FLeXXchgArgs_ι_amount => snd ( fst9 r ) 
 | FLeXXchgArgs_ι_lend_amount => snd ( fst8 r ) 
 | FLeXXchgArgs_ι_lend_finish_time => snd ( fst7 r ) 
 | FLeXXchgArgs_ι_min_amount => snd ( fst6 r ) 
 | FLeXXchgArgs_ι_deals_limit => snd ( fst5 r ) 
 | FLeXXchgArgs_ι_tons_value => snd ( fst4 r ) 
 | FLeXXchgArgs_ι_xchg_price_code => snd ( fst3 r ) 
 | FLeXXchgArgs_ι_addrs => snd ( fst2 r ) 
 | FLeXXchgArgs_ι_tip3_code => snd ( fst1 r ) 
 | FLeXXchgArgs_ι_tip3cfgs => snd r 
 end .
(* 5 *) Coercion FLeXXchgArgs_get : FLeXXchgArgsFields >-> Funclass .
(* 6 *) Definition FLeXXchgArgs_set (f: FLeXXchgArgsFields ) 
(v: FLeXXchgArgs_field_type f) (r: FLeXXchgArgs ): FLeXXchgArgs  :=
  match f, v with | FLeXXchgArgs_ι_sell , v' => ( v' , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_price_num , v' => ( fst12 r , v' , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_price_denum , v' => ( fst12 r , snd ( fst11 r ) , v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_amount , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_lend_amount , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_lend_finish_time , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_min_amount , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_deals_limit , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_tons_value , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_xchg_price_code , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_addrs , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXXchgArgs_ι_tip3_code , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXXchgArgs_ι_tip3cfgs , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .

(* 7 *) Global Instance FLeXXchgArgs_PruvendoRecord : PruvendoRecord FLeXXchgArgs FLeXXchgArgsFields :=
{
  field_type := FLeXXchgArgs_field_type; 
  getPruvendoRecord := @FLeXXchgArgs_get ;
  setPruvendoRecord := @FLeXXchgArgs_set ;
} .

(* 3 *) Definition FLeXCancelArgs_field_type f : Type :=  
match f with 
| FLeXCancelArgs_ι_price => XInteger128 
| FLeXCancelArgs_ι_min_amount => XInteger128 
| FLeXCancelArgs_ι_deals_limit => XInteger8 
| FLeXCancelArgs_ι_value => XInteger128 
| FLeXCancelArgs_ι_price_code => TvmCell 
| FLeXCancelArgs_ι_tip3_code => TvmCell 
| FLeXCancelArgs_ι_tip3cfg => XMaybe (* R *) Tip3Config
 end .

(* 4 *) Definition FLeXCancelArgs_get (f: FLeXCancelArgsFields )(r: FLeXCancelArgs ) :  FLeXCancelArgs_field_type f := 
 match f with 
 | FLeXCancelArgs_ι_price => fst6 r 
 | FLeXCancelArgs_ι_min_amount => snd ( fst5 r ) 
 | FLeXCancelArgs_ι_deals_limit => snd ( fst4 r ) 
 | FLeXCancelArgs_ι_value => snd ( fst3 r ) 
 | FLeXCancelArgs_ι_price_code => snd ( fst2 r ) 
 | FLeXCancelArgs_ι_tip3_code => snd ( fst1 r ) 
 | FLeXCancelArgs_ι_tip3cfg => snd r
 end .
(* 5 *) Coercion FLeXCancelArgs_get : FLeXCancelArgsFields >-> Funclass .
(* 6 *) Definition FLeXCancelArgs_set (f: FLeXCancelArgsFields ) 
(v: FLeXCancelArgs_field_type f) (r: FLeXCancelArgs ): FLeXCancelArgs  :=
  match f, v with | FLeXCancelArgs_ι_price , v' => ( v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_min_amount , v' => ( fst6 r , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_deals_limit , v' => ( fst6 r , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_value , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_price_code , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXCancelArgs_ι_tip3_code , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXCancelArgs_ι_tip3cfg , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
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
(* 3 *) Definition FLeXClient_field_type f : Type :=  
match f with | FLeXClient_ι_owner_ => XInteger256 | FLeXClient_ι_trading_pair_code_ => TvmCell | FLeXClient_ι_xchg_pair_code_ => TvmCell | FLeXClient_ι_workchain_id_ => XInteger8 | FLeXClient_ι_tons_cfg_ => TonsConfig | FLeXClient_ι_flex_ => XAddress | FLeXClient_ι_notify_addr_ => XAddress end .
(* 4 *) Definition FLeXClient_get (f: FLeXClientFields )(r: FLeXClient ) :  FLeXClient_field_type f := 
 match f with | FLeXClient_ι_owner_ => fst6 r 
 | FLeXClient_ι_trading_pair_code_ => snd ( fst5 r ) 
 | FLeXClient_ι_xchg_pair_code_ => snd ( fst4 r ) 
 | FLeXClient_ι_workchain_id_ => snd ( fst3 r ) 
 | FLeXClient_ι_tons_cfg_ => snd ( fst2 r ) 
 | FLeXClient_ι_flex_ => snd ( fst1 r ) 
 | FLeXClient_ι_notify_addr_ => snd r 
 end .
(* 5 *) Coercion FLeXClient_get : FLeXClientFields >-> Funclass .
(* 6 *) Definition FLeXClient_set (f: FLeXClientFields ) 
(v: FLeXClient_field_type f) (r: FLeXClient ): FLeXClient  :=
  match f, v with | FLeXClient_ι_owner_ , v' => ( v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXClient_ι_trading_pair_code_ , v' => ( fst6 r , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXClient_ι_xchg_pair_code_ , v' => ( fst6 r , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXClient_ι_workchain_id_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeXClient_ι_tons_cfg_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeXClient_ι_flex_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeXClient_ι_notify_addr_ , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance FLeXClient_PruvendoRecord : PruvendoRecord FLeXClient FLeXClientFields :=
{
  field_type := FLeXClient_field_type; 
  getPruvendoRecord := @FLeXClient_get ;
  setPruvendoRecord := @FLeXClient_set ;
} .
(* 3 *) Definition FLeX_field_type f : Type :=  
match f with | FLeX_ι_deployer_pubkey_ => XInteger256 | FLeX_ι_tons_cfg_ => TonsConfig | FLeX_ι_pair_code_ => XMaybe TvmCell | FLeX_ι_xchg_pair_code_ => XMaybe TvmCell | FLeX_ι_price_code_ => XMaybe TvmCell | FLeX_ι_xchg_price_code_ => XMaybe TvmCell | FLeX_ι_min_amount_ => XInteger128 | FLeX_ι_deals_limit_ => XInteger8 | FLeX_ι_notify_addr_ => XAddress end .
(* 4 *) Definition FLeX_get (f: FLeXFields )(r: FLeX ) :  FLeX_field_type f := 
 match f with | FLeX_ι_deployer_pubkey_ => fst8 r 
 | FLeX_ι_tons_cfg_ => snd ( fst7 r ) 
 | FLeX_ι_pair_code_ => snd ( fst6 r ) 
 | FLeX_ι_xchg_pair_code_ => snd ( fst5 r ) 
 | FLeX_ι_price_code_ => snd ( fst4 r ) 
 | FLeX_ι_xchg_price_code_ => snd ( fst3 r ) 
 | FLeX_ι_min_amount_ => snd ( fst2 r ) 
 | FLeX_ι_deals_limit_ => snd ( fst1 r ) 
 | FLeX_ι_notify_addr_ => snd r 
 end .
(* 5 *) Coercion FLeX_get : FLeXFields >-> Funclass .
(* 6 *) Definition FLeX_set (f: FLeXFields ) 
(v: FLeX_field_type f) (r: FLeX ): FLeX  :=
  match f, v with | FLeX_ι_deployer_pubkey_ , v' => ( v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_tons_cfg_ , v' => ( fst8 r , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_pair_code_ , v' => ( fst8 r , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_xchg_pair_code_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_price_code_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_xchg_price_code_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_min_amount_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | FLeX_ι_deals_limit_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | FLeX_ι_notify_addr_ , v' => ( fst8 r , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance FLeX_PruvendoRecord : PruvendoRecord FLeX FLeXFields :=
{
  field_type := FLeX_field_type; 
  getPruvendoRecord := @FLeX_get ;
  setPruvendoRecord := @FLeX_set ;
} .

(* 3 *) Definition process_ret_field_type f : Type :=  
match f with 
 | process_ret_ι_sells_amount => XInteger128 | process_ret_ι_sells_ => XMaybe (* XQueue *) OrderInfo | process_ret_ι_buys_amount => XInteger128 | process_ret_ι_buys_ => XMaybe (* XQueue *) OrderInfo | process_ret_ι_ret_ => XMaybe OrderRet end .
(* 4 *) Definition process_ret_get (f: process_retFields )(r: process_ret ) :  process_ret_field_type f := 
 match f with 
 | process_ret_ι_sells_amount => fst4 r 
 | process_ret_ι_sells_ => snd ( fst3 r ) 
 | process_ret_ι_buys_amount => snd ( fst2 r ) 
 | process_ret_ι_buys_ => snd ( fst1 r ) 
 | process_ret_ι_ret_ => snd r 
 end .
(* 5 *) Coercion process_ret_get : process_retFields >-> Funclass .
(* 6 *) Definition process_ret_set (f: process_retFields ) 
(v: process_ret_field_type f) (r: process_ret ): process_ret  :=
  match f, v with | process_ret_ι_sells_amount , v' => ( v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | process_ret_ι_sells_ , v' => ( fst4 r , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | process_ret_ι_buys_amount , v' => ( fst4 r , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | process_ret_ι_buys_ , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | process_ret_ι_ret_ , v' => ( fst4 r , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
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

(* 3 *) Definition Price_field_type f : Type :=  
match f with 
 | Price_ι_price_ => XInteger128 | Price_ι_sells_amount_ => XInteger128 | Price_ι_buys_amount_ => XInteger128 | Price_ι_flex_ => addr_std_fixed | Price_ι_min_amount_ => XInteger128 | Price_ι_deals_limit_ => XInteger8 | Price_ι_notify_addr_ => XInteger16 (* handle<IFLeXNotify> *) | Price_ι_workchain_id_ => XInteger8 | Price_ι_tons_cfg_ => TonsConfig | Price_ι_tip3_code_ => TvmCell | Price_ι_tip3cfg_ => Tip3Config | Price_ι_sells_ => XMaybe (* XQueue *) OrderInfo | Price_ι_buys_ => XMaybe (* XQueue *) OrderInfo end .
(* 4 *) Definition Price_get (f: PriceFields )(r: Price ) :  Price_field_type f := 
 match f with 
 | Price_ι_price_ => fst12 r 
 | Price_ι_sells_amount_ => snd ( fst11 r ) 
 | Price_ι_buys_amount_ => snd ( fst10 r ) 
 | Price_ι_flex_ => snd ( fst9 r ) 
 | Price_ι_min_amount_ => snd ( fst8 r ) 
 | Price_ι_deals_limit_ => snd ( fst7 r ) 
 | Price_ι_notify_addr_ => snd ( fst6 r ) 
 | Price_ι_workchain_id_ => snd ( fst5 r ) 
 | Price_ι_tons_cfg_ => snd ( fst4 r ) 
 | Price_ι_tip3_code_ => snd ( fst3 r ) 
 | Price_ι_tip3cfg_ => snd ( fst2 r ) 
 | Price_ι_sells_ => snd ( fst1 r ) 
 | Price_ι_buys_ => snd r 
 end .
(* 5 *) Coercion Price_get : PriceFields >-> Funclass .
(* 6 *) Definition Price_set (f: PriceFields ) 
(v: Price_field_type f) (r: Price ): Price  :=
  match f, v with | Price_ι_price_ , v' => ( v' , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_sells_amount_ , v' => ( fst12 r , v' , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_buys_amount_ , v' => ( fst12 r , snd ( fst11 r ) , v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_flex_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_min_amount_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_deals_limit_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_notify_addr_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_workchain_id_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_tons_cfg_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_tip3_code_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Price_ι_tip3cfg_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | Price_ι_sells_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | Price_ι_buys_ , v' => ( fst12 r , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .

(* 7 *) Global Instance Price_PruvendoRecord : PruvendoRecord Price PriceFields :=
{
  field_type := Price_field_type; 
  getPruvendoRecord := @Price_get ;
  setPruvendoRecord := @Price_set ;
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

(* 3 *) Definition PriceXchg_field_type f : Type :=  
match f with 
 | PriceXchg_ι_price_ => RationalPrice | PriceXchg_ι_sells_amount_ => XInteger128 | PriceXchg_ι_buys_amount_ => XInteger128 | PriceXchg_ι_flex_ => addr_std_fixed | PriceXchg_ι_min_amount_ => XInteger128 | PriceXchg_ι_deals_limit_ => XInteger8 | PriceXchg_ι_notify_addr_ => XMaybe XInteger16 (* IFLeXNotifyPtr *) | PriceXchg_ι_workchain_id_ => XInteger8 | PriceXchg_ι_tons_cfg_ => TonsConfig | PriceXchg_ι_tip3_code_ => TvmCell | PriceXchg_ι_major_tip3cfg_ => Tip3Config | PriceXchg_ι_minor_tip3cfg_ => Tip3Config | PriceXchg_ι_sells_ => XMaybe (* XBigQueue *) OrderInfoXchg | PriceXchg_ι_buys_ => XMaybe (* XBigQueue *) OrderInfoXchg end .
(* 4 *) Definition PriceXchg_get (f: PriceXchgFields )(r: PriceXchg ) :  PriceXchg_field_type f := 
 match f with 
 | PriceXchg_ι_price_ => fst13 r 
 | PriceXchg_ι_sells_amount_ => snd ( fst12 r ) 
 | PriceXchg_ι_buys_amount_ => snd ( fst11 r ) 
 | PriceXchg_ι_flex_ => snd ( fst10 r ) 
 | PriceXchg_ι_min_amount_ => snd ( fst9 r ) 
 | PriceXchg_ι_deals_limit_ => snd ( fst8 r ) 
 | PriceXchg_ι_notify_addr_ => snd ( fst7 r ) 
 | PriceXchg_ι_workchain_id_ => snd ( fst6 r ) 
 | PriceXchg_ι_tons_cfg_ => snd ( fst5 r ) 
 | PriceXchg_ι_tip3_code_ => snd ( fst4 r ) 
 | PriceXchg_ι_major_tip3cfg_ => snd ( fst3 r ) 
 | PriceXchg_ι_minor_tip3cfg_ => snd ( fst2 r ) 
 | PriceXchg_ι_sells_ => snd ( fst1 r ) 
 | PriceXchg_ι_buys_ => snd r 
 end .
(* 5 *) Coercion PriceXchg_get : PriceXchgFields >-> Funclass .
(* 6 *) Definition PriceXchg_set (f: PriceXchgFields ) 
(v: PriceXchg_field_type f) (r: PriceXchg ): PriceXchg  :=
  match f, v with | PriceXchg_ι_price_ , v' => ( v' , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_sells_amount_ , v' => ( fst13 r , v' , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_buys_amount_ , v' => ( fst13 r , snd ( fst12 r ) , v' , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_flex_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_min_amount_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_deals_limit_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_notify_addr_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_workchain_id_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_tons_cfg_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_tip3_code_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_major_tip3cfg_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_minor_tip3cfg_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | PriceXchg_ι_sells_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | PriceXchg_ι_buys_ , v' => ( fst13 r , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .



(* 7 *) Global Instance PriceXchg_PruvendoRecord : PruvendoRecord PriceXchg PriceXchgFields :=
{
  field_type := PriceXchg_field_type; 
  getPruvendoRecord := @PriceXchg_get ;
  setPruvendoRecord := @PriceXchg_set ;
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
match f with | VMCommit_ι_FLeX => FLeX | VMCommit_ι_FLeXClient => FLeXClient | VMCommit_ι_Price => Price | VMCommit_ι_PriceXchg => PriceXchg end .
(* 4 *) Definition VMCommit_get (f: VMCommitFields )(r: VMCommit ) :  VMCommit_field_type f := 
 match f with | VMCommit_ι_FLeX => fst3 r 
 | VMCommit_ι_FLeXClient => snd ( fst2 r ) 
 | VMCommit_ι_Price => snd ( fst1 r ) 
 | VMCommit_ι_PriceXchg => snd r 
 end .
(* 5 *) Coercion VMCommit_get : VMCommitFields >-> Funclass .
(* 6 *) Definition VMCommit_set (f: VMCommitFields ) 
(v: VMCommit_field_type f) (r: VMCommit ): VMCommit  :=
  match f, v with | VMCommit_ι_FLeX , v' => ( v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | VMCommit_ι_FLeXClient , v' => ( fst3 r , v' , snd ( fst1 r ) , snd r ) 
 | VMCommit_ι_Price , v' => ( fst3 r , snd ( fst2 r ) , v' , snd r ) 
 | VMCommit_ι_PriceXchg , v' => ( fst3 r , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance VMCommit_PruvendoRecord : PruvendoRecord VMCommit VMCommitFields :=
{
  field_type := VMCommit_field_type; 
  getPruvendoRecord := @VMCommit_get ;
  setPruvendoRecord := @VMCommit_set ;
} .
 
(* 3 *) Definition LocalState_field_type f : Type :=  
match f with | LocalState_ι_uint256 => XHMap (string*nat) XInteger256 | LocalState_ι_cell => XHMap (string*nat) TvmCell | LocalState_ι_TonsConfig => XHMap (string*nat) TonsConfig | LocalState_ι_address => XHMap (string*nat) XAddress | LocalState_ι_uint128 => XHMap (string*nat) XInteger128 | LocalState_ι_StateInit => XHMap (string*nat) StateInit | LocalState_ι_DTradingPair => XHMap (string*nat) DTradingPair | LocalState_ι_handle_ITradingPair_ => XHMap (string*nat) XInteger16 (* handle_ITradingPair_ *) | LocalState_ι_DXchgPair => XHMap (string*nat) DXchgPair | LocalState_ι_handle_IXchgPair_ => XHMap (string*nat) XInteger16 (* handle_IXchgPair_ *) | LocalState_ι_parse_FLeXSellArgs_ => XHMap (string*nat) XInteger16 (* parse_FLeXSellArgs_ *) | LocalState_ι_handle_IPrice_ => XHMap (string*nat) XInteger16 (* handle_IPrice_ *) | LocalState_ι_SellArgs => XHMap (string*nat) SellArgs | LocalState_ι_parse_FLeXBuyArgs_ => XHMap (string*nat) XInteger16 (* parse_FLeXBuyArgs_ *) | LocalState_ι_parse_FLeXCancelArgs_ => XHMap (string*nat) XInteger16 (* parse_FLeXCancelArgs_ *) | LocalState_ι_parse_FLeXXchgCancelArgs_ => XHMap (string*nat) XInteger16 (* parse_FLeXXchgCancelArgs_ *) | LocalState_ι_handle_IPriceXchg_ => XHMap (string*nat) XInteger16 (* handle_IPriceXchg_ *) | LocalState_ι_bool_t => XHMap (string*nat) XBool | LocalState_ι_parse_FLeXXchgArgs_ => XHMap (string*nat) XInteger16 (* parse_FLeXXchgArgs_ *) | LocalState_ι_PayloadArgs => XHMap (string*nat) PayloadArgs | LocalState_ι_handle_ITONTokenWallet_ => XHMap (string*nat) XInteger16 (* handle_ITONTokenWallet_ *) | LocalState_ι_uint8 => XHMap (string*nat) XInteger8 | LocalState_ι_Tip3Config => XHMap (string*nat) Tip3Config | LocalState_ι_DPrice => XHMap (string*nat) Price | LocalState_ι_DPriceXchg => XHMap (string*nat) PriceXchg | LocalState_ι_tuple_address_address => XHMap (string*nat) (XAddress*XAddress) | LocalState_ι_uint32 => XHMap (string*nat) XInteger32 | LocalState_ι_unsigned => XHMap (string*nat) XInteger | LocalState_ι_OrderInfo => XHMap (string*nat) OrderInfo | LocalState_ι_int => XHMap (string*nat) XInteger | LocalState_ι_optional_uint128_ => XHMap (string*nat) (XMaybe XInteger128) | LocalState_ι_bool => XHMap (string*nat) XBool | LocalState_ι_optional_OrderInfoWithIdx_ => XHMap (string*nat) (XMaybe (XInteger*OrderInfo)) | LocalState_ι_queue_OrderInfo_ => XHMap (string*nat) XInteger16 (* queue_OrderInfo_ *) | LocalState_ι_pair_unsigned_OrderInfo_ => XHMap (string*nat) (XInteger*OrderInfo) | LocalState_ι_uint256Index => XHMap string nat | LocalState_ι_cellIndex => XHMap string nat | LocalState_ι_TonsConfigIndex => XHMap string nat | LocalState_ι_addressIndex => XHMap string nat | LocalState_ι_uint128Index => XHMap string nat | LocalState_ι_StateInitIndex => XHMap string nat | LocalState_ι_DTradingPairIndex => XHMap string nat | LocalState_ι_handle_ITradingPair_Index => XHMap string nat | LocalState_ι_DXchgPairIndex => XHMap string nat | LocalState_ι_handle_IXchgPair_Index => XHMap string nat | LocalState_ι_parse_FLeXSellArgs_Index => XHMap string nat | LocalState_ι_handle_IPrice_Index => XHMap string nat | LocalState_ι_SellArgsIndex => XHMap string nat | LocalState_ι_parse_FLeXBuyArgs_Index => XHMap string nat | LocalState_ι_parse_FLeXCancelArgs_Index => XHMap string nat | LocalState_ι_parse_FLeXXchgCancelArgs_Index => XHMap string nat | LocalState_ι_handle_IPriceXchg_Index => XHMap string nat | LocalState_ι_bool_tIndex => XHMap string nat | LocalState_ι_parse_FLeXXchgArgs_Index => XHMap string nat | LocalState_ι_PayloadArgsIndex => XHMap string nat | LocalState_ι_handle_ITONTokenWallet_Index => XHMap string nat | LocalState_ι_uint8Index => XHMap string nat | LocalState_ι_Tip3ConfigIndex => XHMap string nat | LocalState_ι_DPriceIndex => XHMap string nat | LocalState_ι_DPriceXchgIndex => XHMap string nat | LocalState_ι_tuple_address_addressIndex => XHMap string nat | LocalState_ι_uint32Index => XHMap string nat | LocalState_ι_unsignedIndex => XHMap string nat | LocalState_ι_OrderInfoIndex => XHMap string nat | LocalState_ι_intIndex => XHMap string nat | LocalState_ι_optional_uint128_Index => XHMap string nat | LocalState_ι_boolIndex => XHMap string nat | LocalState_ι_optional_OrderInfoWithIdx_Index => XHMap string nat | LocalState_ι_queue_OrderInfo_Index => XHMap string nat | LocalState_ι_pair_unsigned_OrderInfo_Index => XHMap string nat end .
(* 4 *) Definition LocalState_get (f: LocalStateFields )(r: LocalState ) :  LocalState_field_type f := 
 match f with | LocalState_ι_uint256 => fst69 r 
 | LocalState_ι_cell => snd ( fst68 r ) 
 | LocalState_ι_TonsConfig => snd ( fst67 r ) 
 | LocalState_ι_address => snd ( fst66 r ) 
 | LocalState_ι_uint128 => snd ( fst65 r ) 
 | LocalState_ι_StateInit => snd ( fst64 r ) 
 | LocalState_ι_DTradingPair => snd ( fst63 r ) 
 | LocalState_ι_handle_ITradingPair_ => snd ( fst62 r ) 
 | LocalState_ι_DXchgPair => snd ( fst61 r ) 
 | LocalState_ι_handle_IXchgPair_ => snd ( fst60 r ) 
 | LocalState_ι_parse_FLeXSellArgs_ => snd ( fst59 r ) 
 | LocalState_ι_handle_IPrice_ => snd ( fst58 r ) 
 | LocalState_ι_SellArgs => snd ( fst57 r ) 
 | LocalState_ι_parse_FLeXBuyArgs_ => snd ( fst56 r ) 
 | LocalState_ι_parse_FLeXCancelArgs_ => snd ( fst55 r ) 
 | LocalState_ι_parse_FLeXXchgCancelArgs_ => snd ( fst54 r ) 
 | LocalState_ι_handle_IPriceXchg_ => snd ( fst53 r ) 
 | LocalState_ι_bool_t => snd ( fst52 r ) 
 | LocalState_ι_parse_FLeXXchgArgs_ => snd ( fst51 r ) 
 | LocalState_ι_PayloadArgs => snd ( fst50 r ) 
 | LocalState_ι_handle_ITONTokenWallet_ => snd ( fst49 r ) 
 | LocalState_ι_uint8 => snd ( fst48 r ) 
 | LocalState_ι_Tip3Config => snd ( fst47 r ) 
 | LocalState_ι_DPrice => snd ( fst46 r ) 
 | LocalState_ι_DPriceXchg => snd ( fst45 r ) 
 | LocalState_ι_tuple_address_address => snd ( fst44 r ) 
 | LocalState_ι_uint32 => snd ( fst43 r ) 
 | LocalState_ι_unsigned => snd ( fst42 r ) 
 | LocalState_ι_OrderInfo => snd ( fst41 r ) 
 | LocalState_ι_int => snd ( fst40 r ) 
 | LocalState_ι_optional_uint128_ => snd ( fst39 r ) 
 | LocalState_ι_bool => snd ( fst38 r ) 
 | LocalState_ι_optional_OrderInfoWithIdx_ => snd ( fst37 r ) 
 | LocalState_ι_queue_OrderInfo_ => snd ( fst36 r ) 
 | LocalState_ι_pair_unsigned_OrderInfo_ => snd ( fst35 r ) 
 | LocalState_ι_uint256Index => snd ( fst34 r ) 
 | LocalState_ι_cellIndex => snd ( fst33 r ) 
 | LocalState_ι_TonsConfigIndex => snd ( fst32 r ) 
 | LocalState_ι_addressIndex => snd ( fst31 r ) 
 | LocalState_ι_uint128Index => snd ( fst30 r ) 
 | LocalState_ι_StateInitIndex => snd ( fst29 r ) 
 | LocalState_ι_DTradingPairIndex => snd ( fst28 r ) 
 | LocalState_ι_handle_ITradingPair_Index => snd ( fst27 r ) 
 | LocalState_ι_DXchgPairIndex => snd ( fst26 r ) 
 | LocalState_ι_handle_IXchgPair_Index => snd ( fst25 r ) 
 | LocalState_ι_parse_FLeXSellArgs_Index => snd ( fst24 r ) 
 | LocalState_ι_handle_IPrice_Index => snd ( fst23 r ) 
 | LocalState_ι_SellArgsIndex => snd ( fst22 r ) 
 | LocalState_ι_parse_FLeXBuyArgs_Index => snd ( fst21 r ) 
 | LocalState_ι_parse_FLeXCancelArgs_Index => snd ( fst20 r ) 
 | LocalState_ι_parse_FLeXXchgCancelArgs_Index => snd ( fst19 r ) 
 | LocalState_ι_handle_IPriceXchg_Index => snd ( fst18 r ) 
 | LocalState_ι_bool_tIndex => snd ( fst17 r ) 
 | LocalState_ι_parse_FLeXXchgArgs_Index => snd ( fst16 r ) 
 | LocalState_ι_PayloadArgsIndex => snd ( fst15 r ) 
 | LocalState_ι_handle_ITONTokenWallet_Index => snd ( fst14 r ) 
 | LocalState_ι_uint8Index => snd ( fst13 r ) 
 | LocalState_ι_Tip3ConfigIndex => snd ( fst12 r ) 
 | LocalState_ι_DPriceIndex => snd ( fst11 r ) 
 | LocalState_ι_DPriceXchgIndex => snd ( fst10 r ) 
 | LocalState_ι_tuple_address_addressIndex => snd ( fst9 r ) 
 | LocalState_ι_uint32Index => snd ( fst8 r ) 
 | LocalState_ι_unsignedIndex => snd ( fst7 r ) 
 | LocalState_ι_OrderInfoIndex => snd ( fst6 r ) 
 | LocalState_ι_intIndex => snd ( fst5 r ) 
 | LocalState_ι_optional_uint128_Index => snd ( fst4 r ) 
 | LocalState_ι_boolIndex => snd ( fst3 r ) 
 | LocalState_ι_optional_OrderInfoWithIdx_Index => snd ( fst2 r ) 
 | LocalState_ι_queue_OrderInfo_Index => snd ( fst1 r ) 
 | LocalState_ι_pair_unsigned_OrderInfo_Index => snd r 
 end .
(* 5 *) Coercion LocalState_get : LocalStateFields >-> Funclass .
(* 6 *) Definition LocalState_set (f: LocalStateFields ) 
(v: LocalState_field_type f) (r: LocalState ): LocalState  :=
  match f, v with 
 | LocalState_ι_uint256 , v' => ( v' , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_cell , v' => ( fst69 r , v' , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_TonsConfig , v' => ( fst69 r , snd ( fst68 r ) , v' , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_address , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , v' , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint128 , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , v' , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_StateInit , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , v' , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DTradingPair , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , v' , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_ITradingPair_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , v' , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DXchgPair , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , v' , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_IXchgPair_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , v' , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXSellArgs_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , v' , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_IPrice_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , v' , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_SellArgs , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , v' , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXBuyArgs_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , v' , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXCancelArgs_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , v' , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXXchgCancelArgs_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , v' , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_IPriceXchg_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , v' , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_bool_t , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , v' , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXXchgArgs_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , v' , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_PayloadArgs , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , v' , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_ITONTokenWallet_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , v' , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint8 , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , v' , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_Tip3Config , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , v' , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DPrice , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , v' , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DPriceXchg , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , v' , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_tuple_address_address , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , v' , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint32 , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , v' , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_unsigned , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , v' , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_OrderInfo , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , v' , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_int , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , v' , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_optional_uint128_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , v' , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_bool , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , v' , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_optional_OrderInfoWithIdx_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , v' , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_queue_OrderInfo_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , v' , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_pair_unsigned_OrderInfo_ , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , v' , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint256Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , v' , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_cellIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , v' , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_TonsConfigIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , v' , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_addressIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , v' , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint128Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , v' , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_StateInitIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , v' , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DTradingPairIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , v' , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_ITradingPair_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , v' , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DXchgPairIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , v' , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_IXchgPair_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , v' , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXSellArgs_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , v' , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_IPrice_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , v' , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_SellArgsIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , v' , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXBuyArgs_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , v' , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXCancelArgs_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , v' , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXXchgCancelArgs_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , v' , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_IPriceXchg_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , v' , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_bool_tIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , v' , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_parse_FLeXXchgArgs_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , v' , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_PayloadArgsIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , v' , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_handle_ITONTokenWallet_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , v' , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint8Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , v' , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_Tip3ConfigIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , v' , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DPriceIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , v' , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_DPriceXchgIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , v' , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_tuple_address_addressIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , v' , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_uint32Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , v' , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_unsignedIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , v' , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_OrderInfoIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_intIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_optional_uint128_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_boolIndex , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_optional_OrderInfoWithIdx_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | LocalState_ι_queue_OrderInfo_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | LocalState_ι_pair_unsigned_OrderInfo_Index , v' => ( fst69 r , snd ( fst68 r ) , snd ( fst67 r ) , snd ( fst66 r ) , snd ( fst65 r ) , snd ( fst64 r ) , snd ( fst63 r ) , snd ( fst62 r ) , snd ( fst61 r ) , snd ( fst60 r ) , snd ( fst59 r ) , snd ( fst58 r ) , snd ( fst57 r ) , snd ( fst56 r ) , snd ( fst55 r ) , snd ( fst54 r ) , snd ( fst53 r ) , snd ( fst52 r ) , snd ( fst51 r ) , snd ( fst50 r ) , snd ( fst49 r ) , snd ( fst48 r ) , snd ( fst47 r ) , snd ( fst46 r ) , snd ( fst45 r ) , snd ( fst44 r ) , snd ( fst43 r ) , snd ( fst42 r ) , snd ( fst41 r ) , snd ( fst40 r ) , snd ( fst39 r ) , snd ( fst38 r ) , snd ( fst37 r ) , snd ( fst36 r ) , snd ( fst35 r ) , snd ( fst34 r ) , snd ( fst33 r ) , snd ( fst32 r ) , snd ( fst31 r ) , snd ( fst30 r ) , snd ( fst29 r ) , snd ( fst28 r ) , snd ( fst27 r ) , snd ( fst26 r ) , snd ( fst25 r ) , snd ( fst24 r ) , snd ( fst23 r ) , snd ( fst22 r ) , snd ( fst21 r ) , snd ( fst20 r ) , snd ( fst19 r ) , snd ( fst18 r ) , snd ( fst17 r ) , snd ( fst16 r ) , snd ( fst15 r ) , snd ( fst14 r ) , snd ( fst13 r ) , snd ( fst12 r ) , snd ( fst11 r ) , snd ( fst10 r ) , snd ( fst9 r ) , snd ( fst8 r ) , snd ( fst7 r ) , snd ( fst6 r ) , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance LocalState_PruvendoRecord : PruvendoRecord LocalState LocalStateFields :=
{
  field_type := LocalState_field_type; 
  getPruvendoRecord := @LocalState_get ;
  setPruvendoRecord := @LocalState_set ;
} .



(* 3 *) Definition Ledger_field_type f : Type :=  
match f with | Ledger_ι_FLeX => FLeX | Ledger_ι_FLeXClient => FLeXClient | Ledger_ι_Price => Price | Ledger_ι_PriceXchg => PriceXchg | Ledger_ι_VMCommit => VMCommit | Ledger_ι_LocalState => LocalState | Ledger_ι_LocalStateCopy => LocalState end .
(* 4 *) Definition Ledger_get (f: LedgerFieldsI )(r: Ledger ) :  Ledger_field_type f := 
 match f with | Ledger_ι_FLeX => fst6 r 
 | Ledger_ι_FLeXClient => snd ( fst5 r ) 
 | Ledger_ι_Price => snd ( fst4 r ) 
 | Ledger_ι_PriceXchg => snd ( fst3 r ) 
 | Ledger_ι_VMCommit => snd ( fst2 r ) 
 | Ledger_ι_LocalState => snd ( fst1 r ) 
 | Ledger_ι_LocalStateCopy => snd r 
 end .
(* 5 *) Coercion Ledger_get : LedgerFieldsI >-> Funclass .
(* 6 *) Definition Ledger_set (f: LedgerFields ) 
(v: Ledger_field_type f) (r: Ledger ): Ledger  :=
  match f, v with | Ledger_ι_FLeX , v' => ( v' , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Ledger_ι_FLeXClient , v' => ( fst6 r , v' , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Ledger_ι_Price , v' => ( fst6 r , snd ( fst5 r ) , v' , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Ledger_ι_PriceXchg , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , v' , snd ( fst2 r ) , snd ( fst1 r ) , snd r ) 
 | Ledger_ι_VMCommit , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , v' , snd ( fst1 r ) , snd r ) 
 | Ledger_ι_LocalState , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , v' , snd r ) 
 | Ledger_ι_LocalStateCopy , v' => ( fst6 r , snd ( fst5 r ) , snd ( fst4 r ) , snd ( fst3 r ) , snd ( fst2 r ) , snd ( fst1 r ) , v' ) 
 end .
(* 7 *) Global Instance Ledger_PruvendoRecord : PruvendoRecord Ledger LedgerFields :=
{
  field_type := Ledger_field_type; 
  getPruvendoRecord := @Ledger_get ;
  setPruvendoRecord := @Ledger_set ;
} .


Definition T1 := FLeX .
Definition T2 := FLeXClient .
Definition T3 := Price .
Definition T4 := PriceXchg .
Definition T5 := VMCommit .
Definition T6 := LocalState .
Definition T7 := LocalState .

 
 Definition projEmbed_T1 : Ledger -> T1 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_FLeX. 
 Definition injEmbed_T1 : T1 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_FLeX. 
 
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
 


 
 Definition projEmbed_T2 : Ledger -> T2 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_FLeXClient. 
 Definition injEmbed_T2 : T2 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_FLeXClient. 
 
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
 


 
 Definition projEmbed_T3 : Ledger -> T3 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_Price. 
 Definition injEmbed_T3 : T3 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_Price. 
 
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
 


 
 Definition projEmbed_T4 : Ledger -> T4 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_PriceXchg. 
 Definition injEmbed_T4 : T4 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_PriceXchg. 
 
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
 


 
 Definition projEmbed_T5 : Ledger -> T5 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_VMCommit. 
 Definition injEmbed_T5 : T5 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_VMCommit. 
 
 Lemma projinj_T5 : forall ( t : T5 ) ( s : Ledger ), projEmbed_T5 ( injEmbed_T5 t s ) = t . 
 Proof. 
 intros. auto. 
 Qed. 
 
 Lemma injproj_T5 : forall ( s : Ledger ) , injEmbed_T5 ( projEmbed_T5 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T5 : forall ( t1 t2 : T5 ) ( s : Ledger ) , 
 injEmbed_T5 t1 ( injEmbed_T5 t2 s) = 
 injEmbed_T5 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT5 : EmbeddedType Ledger T5 := 
 { 
 projEmbed := projEmbed_T5 ; 
 injEmbed := injEmbed_T5 ; 
 projinj := projinj_T5 ; 
 injproj := injproj_T5 ; 
 injinj := injinj_T5 ; 
 } . 
 


 
 Definition projEmbed_T6 : Ledger -> T6 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalState. 
 Definition injEmbed_T6 : T6 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalState. 
 
 Lemma projinj_T6 : forall ( t : T6 ) ( s : Ledger ), projEmbed_T6 ( injEmbed_T6 t s ) = t . 
 Proof. 
 intros. auto. 
 Qed. 
 
 Lemma injproj_T6 : forall ( s : Ledger ) , injEmbed_T6 ( projEmbed_T6 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T6 : forall ( t1 t2 : T6 ) ( s : Ledger ) , 
 injEmbed_T6 t1 ( injEmbed_T6 t2 s) = 
 injEmbed_T6 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT6 : EmbeddedType Ledger T6 := 
 { 
 projEmbed := projEmbed_T6 ; 
 injEmbed := injEmbed_T6 ; 
 projinj := projinj_T6 ; 
 injproj := injproj_T6 ; 
 injinj := injinj_T6 ; 
 } . 
 


 
 Definition projEmbed_T7 : Ledger -> T7 := getPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalStateCopy. 
 Definition injEmbed_T7 : T7 -> Ledger -> Ledger := setPruvendoRecord (PruvendoRecord := Ledger_PruvendoRecord) Ledger_ι_LocalStateCopy. 
 
 Lemma projinj_T7 : forall ( t : T7 ) ( s : Ledger ), projEmbed_T7 ( injEmbed_T7 t s ) = t . 
 Proof. 
 intros. auto. 
 Qed. 
 
 Lemma injproj_T7 : forall ( s : Ledger ) , injEmbed_T7 ( projEmbed_T7 s ) s = s . 
 Proof. 
 intros. 
 destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 
 Lemma injinj_T7 : forall ( t1 t2 : T7 ) ( s : Ledger ) , 
 injEmbed_T7 t1 ( injEmbed_T7 t2 s) = 
 injEmbed_T7 t1 s . 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 
 
 Global Instance embeddedT7 : EmbeddedType Ledger T7 := 
 { 
 projEmbed := projEmbed_T7 ; 
 injEmbed := injEmbed_T7 ; 
 projinj := projinj_T7 ; 
 injproj := injproj_T7 ; 
 injinj := injinj_T7 ; 
 } . 
 



Lemma injcommute_T1_T2: 
               forall ( u : T2 ) ( t : T1 ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT2) u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT2) u s ) ).
Proof.
 intros.  auto.
Qed.

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


Lemma injcommute_T1xT2xT3xT4_T5 : 
               forall ( u : T5 ) ( t :  (((T1 * T2)%xprod* T3)%xprod* T4)%xprod ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT5) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT5) u s ) ).
Proof.
 intros. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4_T5 : 
@InjectCommutableStates Ledger (((T1 * T2)%xprod* T3)%xprod* T4)%xprod T5 := 
{
  embeddedTypeU := embeddedT5 ;

  injcommute := injcommute_T1xT2xT3xT4_T5 
}.

Definition embeddedProduct_T1xT2xT3xT4_T5 := 
           @embeddedProduct Ledger (((T1 * T2)%xprod* T3)%xprod* T4)%xprod T5
  
           InjectCommutableStates_T1xT2xT3xT4_T5.

Existing Instance embeddedProduct_T1xT2xT3xT4_T5 . 


Lemma injcommute_T1xT2xT3xT4xT5_T6 : 
               forall ( u : T6 ) ( t :  ((((T1 * T2)%xprod* T3)%xprod* T4)%xprod* T5)%xprod ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT6) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT6) u s ) ).
Proof.
 intros. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5_T6 : 
@InjectCommutableStates Ledger ((((T1 * T2)%xprod* T3)%xprod* T4)%xprod* T5)%xprod T6 := 
{
  embeddedTypeU := embeddedT6 ;

  injcommute := injcommute_T1xT2xT3xT4xT5_T6 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5_T6 := 
           @embeddedProduct Ledger ((((T1 * T2)%xprod* T3)%xprod* T4)%xprod* T5)%xprod T6
  
           InjectCommutableStates_T1xT2xT3xT4xT5_T6.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5_T6 . 


Lemma injcommute_T1xT2xT3xT4xT5xT6_T7 : 
               forall ( u : T7 ) ( t :  (((((T1 * T2)%xprod* T3)%xprod* T4)%xprod* T5)%xprod* T6)%xprod ) 
                      ( s:Ledger ), 
      ( injEmbed (EmbeddedType:=embeddedT7) u ( injEmbed t s ) ) = 
      ( injEmbed t ( injEmbed (EmbeddedType:=embeddedT7) u s ) ).
Proof.
 intros. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6_T7 : 
@InjectCommutableStates Ledger (((((T1 * T2)%xprod* T3)%xprod* T4)%xprod* T5)%xprod* T6)%xprod T7 := 
{
  embeddedTypeU := embeddedT7 ;

  injcommute := injcommute_T1xT2xT3xT4xT5xT6_T7 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6_T7 := 
           @embeddedProduct Ledger (((((T1 * T2)%xprod* T3)%xprod* T4)%xprod* T5)%xprod* T6)%xprod T7
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6_T7.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6_T7 . 


 
 Lemma fullState_T1xT2xT3xT4xT5xT6_T7 : forall s s0, 
 injEmbed ( T := ((((((T1 * T2)%xprod * T3)%xprod * T4)%xprod * T5)%xprod * T6)%xprod * T7)%xprod ) 
 ( projEmbed s ) ( injEmbed ( T := T7 ) ( projEmbed s ) s0 ) = s. 
 Proof. 
 intros. destruct s. 
 repeat match goal with 
 | p : _ * _ |- _ => destruct p 
 end. auto. 
 Qed. 

Instance FullState_T1xT2xT3xT4xT5xT6_T7 : 
 FullState Ledger (((((T1 * T2)%xprod * T3)%xprod * T4)%xprod * T5)%xprod * T6)%xprod T7 := 
 { 
 injComm := InjectCommutableStates_T1xT2xT3xT4xT5xT6_T7 ; 
 fullState := fullState_T1xT2xT3xT4xT5xT6_T7 
 } . 
 

Local Open Scope solidity_scope.
Notation "'↑ε7' m ":= (liftEmbeddedState ( H := embeddedT7 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε6' m ":= (liftEmbeddedState ( H := embeddedT6 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε5' m ":= (liftEmbeddedState ( H := embeddedT5 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε4' m ":= (liftEmbeddedState ( H := embeddedT4 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε3' m ":= (liftEmbeddedState ( H := embeddedT3 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε2' m ":= (liftEmbeddedState ( H := embeddedT2 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.
Notation "'↑ε1' m ":= (liftEmbeddedState ( H := embeddedT1 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.

Notation "'↑7' m ":= (liftEmbeddedState ( H := embeddedT7 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑6' m ":= (liftEmbeddedState ( H := embeddedT6 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑5' m ":= (liftEmbeddedState ( H := embeddedT5 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑4' m ":= (liftEmbeddedState ( H := embeddedT4 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑3' m ":= (liftEmbeddedState ( H := embeddedT3 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑2' m ":= (liftEmbeddedState ( H := embeddedT2 ) ( m ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑1' m ":= (liftEmbeddedState ( H := embeddedT1 ) ( m ) ) (at level 10, left associativity): solidity_scope.

Notation "'↑↑7' m ":= (liftEmbeddedState ( H := embeddedT7 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑6' m ":= (liftEmbeddedState ( H := embeddedT6 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑5' m ":= (liftEmbeddedState ( H := embeddedT5 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑4' m ":= (liftEmbeddedState ( H := embeddedT4 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑3' m ":= (liftEmbeddedState ( H := embeddedT3 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑2' m ":= (liftEmbeddedState ( H := embeddedT2 ) ) (at level 10, left associativity): solidity_scope.
Notation "'↑↑1' m ":= (liftEmbeddedState ( H := embeddedT1 ) ) (at level 10, left associativity): solidity_scope.

Notation "'↑0' m " := ( liftEmbeddedState ( H :=  embeddedProduct_T1xT2xT3xT4xT5xT6_T7 ) ( m )) (at level 10, left associativity): solidity_scope.
Notation "'↑↑0'" := ( liftEmbeddedState ( H :=  embeddedProduct_T1xT2xT3xT4xT5xT6_T7 )) (at level 32, left associativity): solidity_scope.
Notation " ↓ m " := ( callEmbeddedStateAdj m default (H0 :=  FullState_T1xT2xT3xT4xT5xT6_T7 ) ) (at level 31, left associativity): solidity_scope.
Global Instance iso_T1 : IsoTypes T1 (field_type (R:=Ledger) Ledger_ι_FLeX) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T2 : IsoTypes T2 (field_type (R:=Ledger) Ledger_ι_FLeXClient) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T3 : IsoTypes T3 (field_type (R:=Ledger) Ledger_ι_Price) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T4 : IsoTypes T4 (field_type (R:=Ledger) Ledger_ι_PriceXchg) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T5 : IsoTypes T5 (field_type (R:=Ledger) Ledger_ι_VMCommit) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T6 : IsoTypes T6 (field_type (R:=Ledger) Ledger_ι_LocalState) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Global Instance iso_T7 : IsoTypes T7 (field_type (R:=Ledger) Ledger_ι_LocalStateCopy) :=
{
  x2y := Datatypes.id;
  y2x := Datatypes.id;
  x2x := eq_refl;
  y2y := eq_refl
}.

Definition  FLeX_ι_tons_cfg_TonsConfig  :
 PruvendoRecord (field_type (R:=FLeX) 
                 FLeX_ι_tons_cfg_ ) TonsConfigFields := 
  TonsConfig_PruvendoRecord.

Existing Instance FLeX_ι_tons_cfg_TonsConfig.
(* Existing Instance Ledger_PruvendoRecord.  *)
 
Definition  FLeXClient_ι_tons_cfg_TonsConfig  :
 PruvendoRecord (field_type (R:=FLeXClient) 
                 FLeXClient_ι_tons_cfg_ ) TonsConfigFields := 
  TonsConfig_PruvendoRecord.

Existing Instance FLeXClient_ι_tons_cfg_TonsConfig.
(* Existing Instance Ledger_PruvendoRecord.  *)

Definition  Price_ι_flex_addr_std_fixed  :
 PruvendoRecord (field_type (R:=Price) 
                 Price_ι_flex_ ) addr_std_fixedFields := 
  addr_std_fixed_PruvendoRecord.

Existing Instance Price_ι_flex_addr_std_fixed.
(* Existing Instance Ledger_PruvendoRecord.  *)

Definition  Price_ι_tons_cfg_TonsConfig  :
 PruvendoRecord (field_type (R:=Price) 
                 Price_ι_tons_cfg_ ) TonsConfigFields := 
  TonsConfig_PruvendoRecord.

Existing Instance Price_ι_tons_cfg_TonsConfig.
(* Existing Instance Ledger_PruvendoRecord.  *)

Definition  PriceXchg_ι_price_RationalPrice  :
 PruvendoRecord (field_type (R:=PriceXchg) 
                 PriceXchg_ι_price_ ) RationalPriceFields := 
  RationalPrice_PruvendoRecord.

Existing Instance PriceXchg_ι_price_RationalPrice.
(* Existing Instance Ledger_PruvendoRecord.  *)

Definition  PriceXchg_ι_flex_addr_std_fixed  :
 PruvendoRecord (field_type (R:=PriceXchg) 
                 PriceXchg_ι_flex_ ) addr_std_fixedFields := 
  addr_std_fixed_PruvendoRecord.

Existing Instance PriceXchg_ι_flex_addr_std_fixed.
(* Existing Instance Ledger_PruvendoRecord.  *)

Compute field_type (R:=PriceXchg) 
                 PriceXchg_ι_tons_cfg_ .

Definition  PriceXchg_ι_tons_cfg_TonsConfig  :
 PruvendoRecord (field_type (R:=PriceXchg) 
                 PriceXchg_ι_tons_cfg_ ) TonsConfigFields := 
  TonsConfig_PruvendoRecord.

Existing Instance PriceXchg_ι_tons_cfg_TonsConfig.
(* Existing Instance Ledger_PruvendoRecord.  *)

Compute field_type (R:=PriceXchg) 
                 PriceXchg_ι_minor_tip3cfg_ .

Definition  PriceXchg_ι_minor_tip3cfg_Tip3Config  :
 PruvendoRecord (field_type (R:=PriceXchg) 
                 PriceXchg_ι_minor_tip3cfg_ ) Tip3ConfigFields := 
  Tip3Config_PruvendoRecord.

Existing Instance PriceXchg_ι_minor_tip3cfg_Tip3Config.

Definition  PriceXchg_ι_major_tip3cfg_Tip3Config  :
 PruvendoRecord (field_type (R:=PriceXchg) 
                 PriceXchg_ι_major_tip3cfg_ ) Tip3ConfigFields := 
  Tip3Config_PruvendoRecord.
Existing Instance PriceXchg_ι_major_tip3cfg_Tip3Config.
Existing Instance Ledger_PruvendoRecord.  

(***************************************************************)

Class Countable (X: Type) :=
{
   rength : nat;
   rth : nat -> X -> {t: Type & t}
}.

Program Instance CountablePair0 : forall X Y, Countable (X*Y).
Next Obligation.
exact 2%nat.
Defined.
Next Obligation.
destruct H.
refine (existT id X x).
refine (existT id Y y).
Defined.
Fail Next Obligation.

Program Instance CountablePair_Next : forall X`{Countable X} Y, Countable (X*Y) .
Next Obligation.
exact (S rength).
Defined.
Next Obligation.
remember (Nat.ltb H0 rength).
destruct b.
refine (rth  H0 x).
refine (existT id Y y).
Defined.
Fail Next Obligation.

Existing Instance CountablePair_Next | 0.
Existing Instance CountablePair0 | 100.

Opaque FLeXP.

Lemma Ledger1Type_eq: forall (l: Ledger), projT1 (rth 0 l) = FLeX.
Proof.
   intros.
   compute.
   destruct l.
   repeat destruct p.
   reflexivity.  
Defined.

Lemma Ledger2Type_eq: forall (l: Ledger), projT1 (rth 1 l) = FLeXClient.
Proof.
   intros.
   compute.
   destruct l.
   repeat destruct p.
   reflexivity.  
Defined.

Lemma Ledger3Type_eq: forall (l: Ledger), projT1 (rth 2 l) = Price.
Proof.
   intros.
   compute.
   destruct l.
   repeat destruct p.
   reflexivity.  
Defined.

Lemma Ledger4Type_eq: forall (l: Ledger), projT1 (rth 3 l) = PriceXchg.
Proof.
   intros.
   compute.
   destruct l.
   repeat destruct p.
   reflexivity.  
Defined.

Definition Ledger1Type (l: Ledger) := projT1 (rth 0 l).
Definition Ledger2Type (l: Ledger) := projT1 (rth 1 l).
Definition Ledger3Type (l: Ledger) := projT1 (rth 2 l).
Definition Ledger4Type (l: Ledger) := projT1 (rth 3 l).

Definition Ledger1TypeFLeX : forall (l:Ledger), Ledger1Type l -> FLeX.
intros.
unfold Ledger1Type in X.
rewrite Ledger1Type_eq in X.
exact X.
Defined.

Definition Ledger2TypeFLeXClient : forall l, Ledger2Type l -> FLeXClient.
intros.
unfold Ledger2Type in X.
rewrite Ledger2Type_eq in X.
exact X.
Defined.

Definition Ledger3TypePrice : forall l, Ledger3Type l -> Price.
intros.
unfold Ledger3Type in X.
rewrite Ledger3Type_eq in X.
exact X.
Defined.

Definition Ledger4TypePriceXchg : forall l, Ledger4Type l -> PriceXchg.
intros.
unfold Ledger4Type in X.
rewrite Ledger4Type_eq in X.
exact X.
Defined.

Coercion Ledger1TypeFLeX       : Ledger1Type >-> FLeX.
Coercion Ledger2TypeFLeXClient : Ledger2Type >-> FLeXClient.
Coercion Ledger3TypePrice      : Ledger3Type >-> Price.
Coercion Ledger4TypePriceXchg  : Ledger4Type >-> PriceXchg.

Notation "r ₁" := ((projT2 (rth 0 r) : Ledger1Type r) : FLeX) (at level 10).
Notation "r ₂" := ((projT2 (rth 1 r) : Ledger2Type r) : FLeXClient) (at level 10).
Notation "r ₃" := ((projT2 (rth 2 r) : Ledger3Type r) : Price) (at level 10).
Notation "r ₄" := ((projT2 (rth 3 r) : Ledger4Type r) : PriceXchg) (at level 10).

Transparent FLeXP.

Definition LedgerPruvendoRecord := Ledger_PruvendoRecord.
Definition LedgerLocalState := LocalState.
Definition LedgerLocalFields := LocalStateFields.
Definition LedgerLocalPruvendoRecord := LocalState_PruvendoRecord.
Definition LocalEmbedded := embeddedT7.
Definition LocalCopyEmbedded := embeddedT6.
Definition LocalDefault := LocalState_default.
Definition Ledger_LocalState := Ledger_ι_LocalState.
Definition Ledger_LocalStateCopy := Ledger_ι_LocalStateCopy.
Definition iso_local := iso_T7.

Lemma LedgerFieldsDec: forall (m1 m2: LedgerFields), {m1=m2}+{m1<>m2}.
Proof.
  intros.
  decide equality.
Defined.

Lemma LocalCopySameType: field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_LocalState = 
field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_LocalStateCopy.
Proof.
  reflexivity.
Defined.


(****************************************************************************)
Definition  LocalState_ι_uint256Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_uint256Index l.

Definition  LocalState_ι_uint256Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_uint256Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_uint256Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_uint256Index_Embedded_projEmbed (LocalState_ι_uint256Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_uint256Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_uint256Index_Embedded_injEmbed (LocalState_ι_uint256Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_uint256Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_uint256Index_Embedded_injEmbed t1 (LocalState_ι_uint256Index_Embedded_injEmbed t2 s) = LocalState_ι_uint256Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_uint256Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_uint256Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_uint256Index_Embedded_injEmbed;
  projinj := LocalState_ι_uint256Index_Embedded_projinj;
  injproj := LocalState_ι_uint256Index_Embedded_injproj;
  injinj := LocalState_ι_uint256Index_Embedded_injinj
}.

Definition  LocalState_ι_cellIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_cellIndex l.

Definition  LocalState_ι_cellIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_cellIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_cellIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_cellIndex_Embedded_projEmbed (LocalState_ι_cellIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_cellIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_cellIndex_Embedded_injEmbed (LocalState_ι_cellIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_cellIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_cellIndex_Embedded_injEmbed t1 (LocalState_ι_cellIndex_Embedded_injEmbed t2 s) = LocalState_ι_cellIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

eldsDec: forall (m1 m2: LedgerFields), {m1=m2}+{m1<>m2}.
Proof.
  intros.
  decide equality.
Defined.

Lemma LocalCopySameType: field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_LocalState = 
field_type (PruvendoRecord:=LedgerPruvendoRecord) Ledger_LocalStateCopy.
Proof.
  reflexivity.
Global Instance LocalState_ι_cellIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_cellIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_cellIndex_Embedded_injEmbed;
  projinj := LocalState_ι_cellIndex_Embedded_projinj;
  injproj := LocalState_ι_cellIndex_Embedded_injproj;
  injinj := LocalState_ι_cellIndex_Embedded_injinj
}.
Definition  LocalState_ι_TonsConfigIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_TonsConfigIndex l.

Definition  LocalState_ι_TonsConfigIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_TonsConfigIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_TonsConfigIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_TonsConfigIndex_Embedded_projEmbed (LocalState_ι_TonsConfigIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_TonsConfigIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_TonsConfigIndex_Embedded_injEmbed (LocalState_ι_TonsConfigIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_TonsConfigIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_TonsConfigIndex_Embedded_injEmbed t1 (LocalState_ι_TonsConfigIndex_Embedded_injEmbed t2 s) = LocalState_ι_TonsConfigIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_TonsConfigIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_TonsConfigIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_TonsConfigIndex_Embedded_injEmbed;
  projinj := LocalState_ι_TonsConfigIndex_Embedded_projinj;
  injproj := LocalState_ι_TonsConfigIndex_Embedded_injproj;
  injinj := LocalState_ι_TonsConfigIndex_Embedded_injinj
}.
Definition  LocalState_ι_addressIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_addressIndex l.

Definition  LocalState_ι_addressIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_addressIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_addressIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_addressIndex_Embedded_projEmbed (LocalState_ι_addressIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_addressIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_addressIndex_Embedded_injEmbed (LocalState_ι_addressIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_addressIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_addressIndex_Embedded_injEmbed t1 (LocalState_ι_addressIndex_Embedded_injEmbed t2 s) = LocalState_ι_addressIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_addressIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_addressIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_addressIndex_Embedded_injEmbed;
  projinj := LocalState_ι_addressIndex_Embedded_projinj;
  injproj := LocalState_ι_addressIndex_Embedded_injproj;
  injinj := LocalState_ι_addressIndex_Embedded_injinj
}.
Definition  LocalState_ι_uint128Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_uint128Index l.

Definition  LocalState_ι_uint128Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_uint128Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_uint128Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_uint128Index_Embedded_projEmbed (LocalState_ι_uint128Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_uint128Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_uint128Index_Embedded_injEmbed (LocalState_ι_uint128Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_uint128Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_uint128Index_Embedded_injEmbed t1 (LocalState_ι_uint128Index_Embedded_injEmbed t2 s) = LocalState_ι_uint128Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_uint128Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_uint128Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_uint128Index_Embedded_injEmbed;
  projinj := LocalState_ι_uint128Index_Embedded_projinj;
  injproj := LocalState_ι_uint128Index_Embedded_injproj;
  injinj := LocalState_ι_uint128Index_Embedded_injinj
}.
Definition  LocalState_ι_StateInitIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_StateInitIndex l.

Definition  LocalState_ι_StateInitIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_StateInitIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_StateInitIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_StateInitIndex_Embedded_projEmbed (LocalState_ι_StateInitIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_StateInitIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_StateInitIndex_Embedded_injEmbed (LocalState_ι_StateInitIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_StateInitIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_StateInitIndex_Embedded_injEmbed t1 (LocalState_ι_StateInitIndex_Embedded_injEmbed t2 s) = LocalState_ι_StateInitIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_StateInitIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_StateInitIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_StateInitIndex_Embedded_injEmbed;
  projinj := LocalState_ι_StateInitIndex_Embedded_projinj;
  injproj := LocalState_ι_StateInitIndex_Embedded_injproj;
  injinj := LocalState_ι_StateInitIndex_Embedded_injinj
}.
Definition  LocalState_ι_DTradingPairIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_DTradingPairIndex l.

Definition  LocalState_ι_DTradingPairIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_DTradingPairIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_DTradingPairIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_DTradingPairIndex_Embedded_projEmbed (LocalState_ι_DTradingPairIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_DTradingPairIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_DTradingPairIndex_Embedded_injEmbed (LocalState_ι_DTradingPairIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_DTradingPairIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_DTradingPairIndex_Embedded_injEmbed t1 (LocalState_ι_DTradingPairIndex_Embedded_injEmbed t2 s) = LocalState_ι_DTradingPairIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_DTradingPairIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_DTradingPairIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_DTradingPairIndex_Embedded_injEmbed;
  projinj := LocalState_ι_DTradingPairIndex_Embedded_projinj;
  injproj := LocalState_ι_DTradingPairIndex_Embedded_injproj;
  injinj := LocalState_ι_DTradingPairIndex_Embedded_injinj
}.
Definition  LocalState_ι_handle_ITradingPair_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_handle_ITradingPair_Index l.

Definition  LocalState_ι_handle_ITradingPair_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_handle_ITradingPair_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_handle_ITradingPair_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_handle_ITradingPair_Index_Embedded_projEmbed (LocalState_ι_handle_ITradingPair_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_handle_ITradingPair_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_handle_ITradingPair_Index_Embedded_injEmbed (LocalState_ι_handle_ITradingPair_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_handle_ITradingPair_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_handle_ITradingPair_Index_Embedded_injEmbed t1 (LocalState_ι_handle_ITradingPair_Index_Embedded_injEmbed t2 s) = LocalState_ι_handle_ITradingPair_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_handle_ITradingPair_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_handle_ITradingPair_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_handle_ITradingPair_Index_Embedded_injEmbed;
  projinj := LocalState_ι_handle_ITradingPair_Index_Embedded_projinj;
  injproj := LocalState_ι_handle_ITradingPair_Index_Embedded_injproj;
  injinj := LocalState_ι_handle_ITradingPair_Index_Embedded_injinj
}.
Definition  LocalState_ι_DXchgPairIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_DXchgPairIndex l.

Definition  LocalState_ι_DXchgPairIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_DXchgPairIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_DXchgPairIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_DXchgPairIndex_Embedded_projEmbed (LocalState_ι_DXchgPairIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_DXchgPairIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_DXchgPairIndex_Embedded_injEmbed (LocalState_ι_DXchgPairIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_DXchgPairIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_DXchgPairIndex_Embedded_injEmbed t1 (LocalState_ι_DXchgPairIndex_Embedded_injEmbed t2 s) = LocalState_ι_DXchgPairIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_DXchgPairIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_DXchgPairIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_DXchgPairIndex_Embedded_injEmbed;
  projinj := LocalState_ι_DXchgPairIndex_Embedded_projinj;
  injproj := LocalState_ι_DXchgPairIndex_Embedded_injproj;
  injinj := LocalState_ι_DXchgPairIndex_Embedded_injinj
}.
Definition  LocalState_ι_handle_IXchgPair_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_handle_IXchgPair_Index l.

Definition  LocalState_ι_handle_IXchgPair_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_handle_IXchgPair_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_handle_IXchgPair_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_handle_IXchgPair_Index_Embedded_projEmbed (LocalState_ι_handle_IXchgPair_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_handle_IXchgPair_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_handle_IXchgPair_Index_Embedded_injEmbed (LocalState_ι_handle_IXchgPair_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_handle_IXchgPair_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_handle_IXchgPair_Index_Embedded_injEmbed t1 (LocalState_ι_handle_IXchgPair_Index_Embedded_injEmbed t2 s) = LocalState_ι_handle_IXchgPair_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_handle_IXchgPair_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_handle_IXchgPair_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_handle_IXchgPair_Index_Embedded_injEmbed;
  projinj := LocalState_ι_handle_IXchgPair_Index_Embedded_projinj;
  injproj := LocalState_ι_handle_IXchgPair_Index_Embedded_injproj;
  injinj := LocalState_ι_handle_IXchgPair_Index_Embedded_injinj
}.
Definition  LocalState_ι_parse_FLeXSellArgs_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_parse_FLeXSellArgs_Index l.

Definition  LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_parse_FLeXSellArgs_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_parse_FLeXSellArgs_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_parse_FLeXSellArgs_Index_Embedded_projEmbed (LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injEmbed (LocalState_ι_parse_FLeXSellArgs_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injEmbed t1 (LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injEmbed t2 s) = LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_parse_FLeXSellArgs_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_parse_FLeXSellArgs_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injEmbed;
  projinj := LocalState_ι_parse_FLeXSellArgs_Index_Embedded_projinj;
  injproj := LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injproj;
  injinj := LocalState_ι_parse_FLeXSellArgs_Index_Embedded_injinj
}.
Definition  LocalState_ι_handle_IPrice_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_handle_IPrice_Index l.

Definition  LocalState_ι_handle_IPrice_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_handle_IPrice_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_handle_IPrice_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_handle_IPrice_Index_Embedded_projEmbed (LocalState_ι_handle_IPrice_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_handle_IPrice_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_handle_IPrice_Index_Embedded_injEmbed (LocalState_ι_handle_IPrice_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_handle_IPrice_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_handle_IPrice_Index_Embedded_injEmbed t1 (LocalState_ι_handle_IPrice_Index_Embedded_injEmbed t2 s) = LocalState_ι_handle_IPrice_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_handle_IPrice_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_handle_IPrice_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_handle_IPrice_Index_Embedded_injEmbed;
  projinj := LocalState_ι_handle_IPrice_Index_Embedded_projinj;
  injproj := LocalState_ι_handle_IPrice_Index_Embedded_injproj;
  injinj := LocalState_ι_handle_IPrice_Index_Embedded_injinj
}.
Definition  LocalState_ι_SellArgsIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_SellArgsIndex l.

Definition  LocalState_ι_SellArgsIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_SellArgsIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_SellArgsIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_SellArgsIndex_Embedded_projEmbed (LocalState_ι_SellArgsIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_SellArgsIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_SellArgsIndex_Embedded_injEmbed (LocalState_ι_SellArgsIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_SellArgsIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_SellArgsIndex_Embedded_injEmbed t1 (LocalState_ι_SellArgsIndex_Embedded_injEmbed t2 s) = LocalState_ι_SellArgsIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_SellArgsIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_SellArgsIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_SellArgsIndex_Embedded_injEmbed;
  projinj := LocalState_ι_SellArgsIndex_Embedded_projinj;
  injproj := LocalState_ι_SellArgsIndex_Embedded_injproj;
  injinj := LocalState_ι_SellArgsIndex_Embedded_injinj
}.
Definition  LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_parse_FLeXBuyArgs_Index l.

Definition  LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_parse_FLeXBuyArgs_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_projEmbed (LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injEmbed (LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injEmbed t1 (LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injEmbed t2 s) = LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_parse_FLeXBuyArgs_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injEmbed;
  projinj := LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_projinj;
  injproj := LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injproj;
  injinj := LocalState_ι_parse_FLeXBuyArgs_Index_Embedded_injinj
}.
Definition  LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_parse_FLeXCancelArgs_Index l.

Definition  LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_parse_FLeXCancelArgs_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_projEmbed (LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injEmbed (LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injEmbed t1 (LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injEmbed t2 s) = LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_parse_FLeXCancelArgs_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injEmbed;
  projinj := LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_projinj;
  injproj := LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injproj;
  injinj := LocalState_ι_parse_FLeXCancelArgs_Index_Embedded_injinj
}.
Definition  LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_parse_FLeXXchgCancelArgs_Index l.

Definition  LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_parse_FLeXXchgCancelArgs_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_projEmbed (LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injEmbed (LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injEmbed t1 (LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injEmbed t2 s) = LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injEmbed;
  projinj := LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_projinj;
  injproj := LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injproj;
  injinj := LocalState_ι_parse_FLeXXchgCancelArgs_Index_Embedded_injinj
}.
Definition  LocalState_ι_handle_IPriceXchg_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_handle_IPriceXchg_Index l.

Definition  LocalState_ι_handle_IPriceXchg_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_handle_IPriceXchg_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_handle_IPriceXchg_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_handle_IPriceXchg_Index_Embedded_projEmbed (LocalState_ι_handle_IPriceXchg_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_handle_IPriceXchg_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_handle_IPriceXchg_Index_Embedded_injEmbed (LocalState_ι_handle_IPriceXchg_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_handle_IPriceXchg_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_handle_IPriceXchg_Index_Embedded_injEmbed t1 (LocalState_ι_handle_IPriceXchg_Index_Embedded_injEmbed t2 s) = LocalState_ι_handle_IPriceXchg_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_handle_IPriceXchg_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_handle_IPriceXchg_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_handle_IPriceXchg_Index_Embedded_injEmbed;
  projinj := LocalState_ι_handle_IPriceXchg_Index_Embedded_projinj;
  injproj := LocalState_ι_handle_IPriceXchg_Index_Embedded_injproj;
  injinj := LocalState_ι_handle_IPriceXchg_Index_Embedded_injinj
}.
Definition  LocalState_ι_bool_tIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_bool_tIndex l.

Definition  LocalState_ι_bool_tIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_bool_tIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_bool_tIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_bool_tIndex_Embedded_projEmbed (LocalState_ι_bool_tIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_bool_tIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_bool_tIndex_Embedded_injEmbed (LocalState_ι_bool_tIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_bool_tIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_bool_tIndex_Embedded_injEmbed t1 (LocalState_ι_bool_tIndex_Embedded_injEmbed t2 s) = LocalState_ι_bool_tIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_bool_tIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_bool_tIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_bool_tIndex_Embedded_injEmbed;
  projinj := LocalState_ι_bool_tIndex_Embedded_projinj;
  injproj := LocalState_ι_bool_tIndex_Embedded_injproj;
  injinj := LocalState_ι_bool_tIndex_Embedded_injinj
}.
Definition  LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_parse_FLeXXchgArgs_Index l.

Definition  LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_parse_FLeXXchgArgs_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_projEmbed (LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injEmbed (LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injEmbed t1 (LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injEmbed t2 s) = LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_parse_FLeXXchgArgs_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injEmbed;
  projinj := LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_projinj;
  injproj := LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injproj;
  injinj := LocalState_ι_parse_FLeXXchgArgs_Index_Embedded_injinj
}.
Definition  LocalState_ι_PayloadArgsIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_PayloadArgsIndex l.

Definition  LocalState_ι_PayloadArgsIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_PayloadArgsIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_PayloadArgsIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_PayloadArgsIndex_Embedded_projEmbed (LocalState_ι_PayloadArgsIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_PayloadArgsIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_PayloadArgsIndex_Embedded_injEmbed (LocalState_ι_PayloadArgsIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_PayloadArgsIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_PayloadArgsIndex_Embedded_injEmbed t1 (LocalState_ι_PayloadArgsIndex_Embedded_injEmbed t2 s) = LocalState_ι_PayloadArgsIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_PayloadArgsIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_PayloadArgsIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_PayloadArgsIndex_Embedded_injEmbed;
  projinj := LocalState_ι_PayloadArgsIndex_Embedded_projinj;
  injproj := LocalState_ι_PayloadArgsIndex_Embedded_injproj;
  injinj := LocalState_ι_PayloadArgsIndex_Embedded_injinj
}.
Definition  LocalState_ι_handle_ITONTokenWallet_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_handle_ITONTokenWallet_Index l.

Definition  LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_handle_ITONTokenWallet_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_handle_ITONTokenWallet_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_handle_ITONTokenWallet_Index_Embedded_projEmbed (LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injEmbed (LocalState_ι_handle_ITONTokenWallet_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injEmbed t1 (LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injEmbed t2 s) = LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_handle_ITONTokenWallet_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_handle_ITONTokenWallet_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injEmbed;
  projinj := LocalState_ι_handle_ITONTokenWallet_Index_Embedded_projinj;
  injproj := LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injproj;
  injinj := LocalState_ι_handle_ITONTokenWallet_Index_Embedded_injinj
}.
Definition  LocalState_ι_uint8Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_uint8Index l.

Definition  LocalState_ι_uint8Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_uint8Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_uint8Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_uint8Index_Embedded_projEmbed (LocalState_ι_uint8Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_uint8Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_uint8Index_Embedded_injEmbed (LocalState_ι_uint8Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_uint8Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_uint8Index_Embedded_injEmbed t1 (LocalState_ι_uint8Index_Embedded_injEmbed t2 s) = LocalState_ι_uint8Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_uint8Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_uint8Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_uint8Index_Embedded_injEmbed;
  projinj := LocalState_ι_uint8Index_Embedded_projinj;
  injproj := LocalState_ι_uint8Index_Embedded_injproj;
  injinj := LocalState_ι_uint8Index_Embedded_injinj
}.
Definition  LocalState_ι_Tip3ConfigIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_Tip3ConfigIndex l.

Definition  LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_Tip3ConfigIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_Tip3ConfigIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_Tip3ConfigIndex_Embedded_projEmbed (LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_Tip3ConfigIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed (LocalState_ι_Tip3ConfigIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_Tip3ConfigIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed t1 (LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed t2 s) = LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_Tip3ConfigIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_Tip3ConfigIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_Tip3ConfigIndex_Embedded_injEmbed;
  projinj := LocalState_ι_Tip3ConfigIndex_Embedded_projinj;
  injproj := LocalState_ι_Tip3ConfigIndex_Embedded_injproj;
  injinj := LocalState_ι_Tip3ConfigIndex_Embedded_injinj
}.
Definition  LocalState_ι_DPriceIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_DPriceIndex l.

Definition  LocalState_ι_DPriceIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_DPriceIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_DPriceIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_DPriceIndex_Embedded_projEmbed (LocalState_ι_DPriceIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_DPriceIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_DPriceIndex_Embedded_injEmbed (LocalState_ι_DPriceIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_DPriceIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_DPriceIndex_Embedded_injEmbed t1 (LocalState_ι_DPriceIndex_Embedded_injEmbed t2 s) = LocalState_ι_DPriceIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_DPriceIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_DPriceIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_DPriceIndex_Embedded_injEmbed;
  projinj := LocalState_ι_DPriceIndex_Embedded_projinj;
  injproj := LocalState_ι_DPriceIndex_Embedded_injproj;
  injinj := LocalState_ι_DPriceIndex_Embedded_injinj
}.
Definition  LocalState_ι_DPriceXchgIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_DPriceXchgIndex l.

Definition  LocalState_ι_DPriceXchgIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_DPriceXchgIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_DPriceXchgIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_DPriceXchgIndex_Embedded_projEmbed (LocalState_ι_DPriceXchgIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_DPriceXchgIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_DPriceXchgIndex_Embedded_injEmbed (LocalState_ι_DPriceXchgIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_DPriceXchgIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_DPriceXchgIndex_Embedded_injEmbed t1 (LocalState_ι_DPriceXchgIndex_Embedded_injEmbed t2 s) = LocalState_ι_DPriceXchgIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_DPriceXchgIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_DPriceXchgIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_DPriceXchgIndex_Embedded_injEmbed;
  projinj := LocalState_ι_DPriceXchgIndex_Embedded_projinj;
  injproj := LocalState_ι_DPriceXchgIndex_Embedded_injproj;
  injinj := LocalState_ι_DPriceXchgIndex_Embedded_injinj
}.
Definition  LocalState_ι_tuple_address_addressIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_tuple_address_addressIndex l.

Definition  LocalState_ι_tuple_address_addressIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_tuple_address_addressIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_tuple_address_addressIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_tuple_address_addressIndex_Embedded_projEmbed (LocalState_ι_tuple_address_addressIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_tuple_address_addressIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_tuple_address_addressIndex_Embedded_injEmbed (LocalState_ι_tuple_address_addressIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_tuple_address_addressIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_tuple_address_addressIndex_Embedded_injEmbed t1 (LocalState_ι_tuple_address_addressIndex_Embedded_injEmbed t2 s) = LocalState_ι_tuple_address_addressIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_tuple_address_addressIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_tuple_address_addressIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_tuple_address_addressIndex_Embedded_injEmbed;
  projinj := LocalState_ι_tuple_address_addressIndex_Embedded_projinj;
  injproj := LocalState_ι_tuple_address_addressIndex_Embedded_injproj;
  injinj := LocalState_ι_tuple_address_addressIndex_Embedded_injinj
}.
Definition  LocalState_ι_uint32Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_uint32Index l.

Definition  LocalState_ι_uint32Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_uint32Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_uint32Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_uint32Index_Embedded_projEmbed (LocalState_ι_uint32Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_uint32Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_uint32Index_Embedded_injEmbed (LocalState_ι_uint32Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_uint32Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_uint32Index_Embedded_injEmbed t1 (LocalState_ι_uint32Index_Embedded_injEmbed t2 s) = LocalState_ι_uint32Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_uint32Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_uint32Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_uint32Index_Embedded_injEmbed;
  projinj := LocalState_ι_uint32Index_Embedded_projinj;
  injproj := LocalState_ι_uint32Index_Embedded_injproj;
  injinj := LocalState_ι_uint32Index_Embedded_injinj
}.
Definition  LocalState_ι_unsignedIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_unsignedIndex l.

Definition  LocalState_ι_unsignedIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_unsignedIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_unsignedIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_unsignedIndex_Embedded_projEmbed (LocalState_ι_unsignedIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_unsignedIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_unsignedIndex_Embedded_injEmbed (LocalState_ι_unsignedIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_unsignedIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_unsignedIndex_Embedded_injEmbed t1 (LocalState_ι_unsignedIndex_Embedded_injEmbed t2 s) = LocalState_ι_unsignedIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_unsignedIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_unsignedIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_unsignedIndex_Embedded_injEmbed;
  projinj := LocalState_ι_unsignedIndex_Embedded_projinj;
  injproj := LocalState_ι_unsignedIndex_Embedded_injproj;
  injinj := LocalState_ι_unsignedIndex_Embedded_injinj
}.
Definition  LocalState_ι_OrderInfoIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_OrderInfoIndex l.

Definition  LocalState_ι_OrderInfoIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_OrderInfoIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_OrderInfoIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_OrderInfoIndex_Embedded_projEmbed (LocalState_ι_OrderInfoIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_OrderInfoIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_OrderInfoIndex_Embedded_injEmbed (LocalState_ι_OrderInfoIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_OrderInfoIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_OrderInfoIndex_Embedded_injEmbed t1 (LocalState_ι_OrderInfoIndex_Embedded_injEmbed t2 s) = LocalState_ι_OrderInfoIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_OrderInfoIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_OrderInfoIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_OrderInfoIndex_Embedded_injEmbed;
  projinj := LocalState_ι_OrderInfoIndex_Embedded_projinj;
  injproj := LocalState_ι_OrderInfoIndex_Embedded_injproj;
  injinj := LocalState_ι_OrderInfoIndex_Embedded_injinj
}.
Definition  LocalState_ι_intIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_intIndex l.

Definition  LocalState_ι_intIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_intIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_intIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_intIndex_Embedded_projEmbed (LocalState_ι_intIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_intIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_intIndex_Embedded_injEmbed (LocalState_ι_intIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_intIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_intIndex_Embedded_injEmbed t1 (LocalState_ι_intIndex_Embedded_injEmbed t2 s) = LocalState_ι_intIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_intIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_intIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_intIndex_Embedded_injEmbed;
  projinj := LocalState_ι_intIndex_Embedded_projinj;
  injproj := LocalState_ι_intIndex_Embedded_injproj;
  injinj := LocalState_ι_intIndex_Embedded_injinj
}.
Definition  LocalState_ι_optional_uint128_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_optional_uint128_Index l.

Definition  LocalState_ι_optional_uint128_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_optional_uint128_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_optional_uint128_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_optional_uint128_Index_Embedded_projEmbed (LocalState_ι_optional_uint128_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_optional_uint128_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_optional_uint128_Index_Embedded_injEmbed (LocalState_ι_optional_uint128_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_optional_uint128_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_optional_uint128_Index_Embedded_injEmbed t1 (LocalState_ι_optional_uint128_Index_Embedded_injEmbed t2 s) = LocalState_ι_optional_uint128_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_optional_uint128_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_optional_uint128_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_optional_uint128_Index_Embedded_injEmbed;
  projinj := LocalState_ι_optional_uint128_Index_Embedded_projinj;
  injproj := LocalState_ι_optional_uint128_Index_Embedded_injproj;
  injinj := LocalState_ι_optional_uint128_Index_Embedded_injinj
}.
Definition  LocalState_ι_boolIndex_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_boolIndex l.

Definition  LocalState_ι_boolIndex_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_boolIndex := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_boolIndex_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_boolIndex_Embedded_projEmbed (LocalState_ι_boolIndex_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_boolIndex_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_boolIndex_Embedded_injEmbed (LocalState_ι_boolIndex_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_boolIndex_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_boolIndex_Embedded_injEmbed t1 (LocalState_ι_boolIndex_Embedded_injEmbed t2 s) = LocalState_ι_boolIndex_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_boolIndex_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_boolIndex_Embedded_projEmbed;
	injEmbed := LocalState_ι_boolIndex_Embedded_injEmbed;
  projinj := LocalState_ι_boolIndex_Embedded_projinj;
  injproj := LocalState_ι_boolIndex_Embedded_injproj;
  injinj := LocalState_ι_boolIndex_Embedded_injinj
}.
Definition  LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_optional_OrderInfoWithIdx_Index l.

Definition  LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_optional_OrderInfoWithIdx_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_projEmbed (LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injEmbed (LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injEmbed t1 (LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injEmbed t2 s) = LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injEmbed;
  projinj := LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_projinj;
  injproj := LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injproj;
  injinj := LocalState_ι_optional_OrderInfoWithIdx_Index_Embedded_injinj
}.
Definition  LocalState_ι_queue_OrderInfo_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_queue_OrderInfo_Index l.

Definition  LocalState_ι_queue_OrderInfo_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_queue_OrderInfo_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_queue_OrderInfo_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_queue_OrderInfo_Index_Embedded_projEmbed (LocalState_ι_queue_OrderInfo_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_queue_OrderInfo_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_queue_OrderInfo_Index_Embedded_injEmbed (LocalState_ι_queue_OrderInfo_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_queue_OrderInfo_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_queue_OrderInfo_Index_Embedded_injEmbed t1 (LocalState_ι_queue_OrderInfo_Index_Embedded_injEmbed t2 s) = LocalState_ι_queue_OrderInfo_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_queue_OrderInfo_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_queue_OrderInfo_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_queue_OrderInfo_Index_Embedded_injEmbed;
  projinj := LocalState_ι_queue_OrderInfo_Index_Embedded_projinj;
  injproj := LocalState_ι_queue_OrderInfo_Index_Embedded_injproj;
  injinj := LocalState_ι_queue_OrderInfo_Index_Embedded_injinj
}.
Definition  LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_projEmbed (l:LedgerLocalState ) : XHMap string nat := 
  LocalState_ι_pair_unsigned_OrderInfo_Index l.

Definition  LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injEmbed (m: XHMap string nat) (l: LedgerLocalState) : LedgerLocalState := 
  {$$ l with  LocalState_ι_pair_unsigned_OrderInfo_Index := m $$}.

Print EmbeddedType.  

Lemma LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_projinj : forall (t : XHMap string nat) (s : LedgerLocalState), LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_projEmbed (LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injEmbed t s) = t.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.

Lemma LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injproj : forall s : LedgerLocalState, LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injEmbed (LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_projEmbed s) s = s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.  

Lemma LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injinj : forall (t1 t2 : XHMap string nat) (s : LedgerLocalState),
LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injEmbed t1 (LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injEmbed t2 s) = LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injEmbed t1 s.
Proof.
  intros.
  destruct s.
  repeat destruct p.
  reflexivity.
Defined.


Global Instance LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded : EmbeddedType LedgerLocalState (XHMap string nat) :=
{
  projEmbed := LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_projEmbed;
	injEmbed := LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injEmbed;
  projinj := LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_projinj;
  injproj := LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injproj;
  injinj := LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded_injinj
}.
(****************************************************************************)

Class LocalStateField (X:Type): Type := 
{
    local_index_embedded:> EmbeddedType LedgerLocalState (XHMap string nat) ;
    local_state_field: LedgerLocalFields;
    local_field_type_correct: field_type (PruvendoRecord:=LedgerLocalPruvendoRecord) local_state_field = XHMap (string*nat)%type X;
}.    

Global Instance LocalStateField_XBool: LocalStateField XBool :=
{
  local_index_embedded := LocalState_ι_boolIndex_Embedded ;
  local_state_field := LocalState_ι_bool_t ; 
  local_field_type_correct := eq_refl
}.

Global Instance LocalStateField_XInteger: LocalStateField XInteger :=
{
  local_index_embedded := LocalState_ι_intIndex_Embedded;
  local_state_field := LocalState_ι_int; 
  local_field_type_correct := eq_refl
}.


Global Instance LocalState_ι_uint256: LocalStateField XInteger256 :=
{
  local_index_embedded := LocalState_ι_uint256Index_Embedded;
  local_state_field := LocalState_ι_uint256; 
  local_field_type_correct := eq_refl
}.

Global Instance LocalState_ι_cell: LocalStateField TvmCell :=
{
  local_index_embedded := LocalState_ι_cellIndex_Embedded;
  local_state_field := LocalState_ι_cell; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_TonsConfig: LocalStateField TonsConfig :=
{
  local_index_embedded := LocalState_ι_TonsConfigIndex_Embedded;
  local_state_field := LocalState_ι_TonsConfig; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_address: LocalStateField XAddress :=
{
  local_index_embedded := LocalState_ι_addressIndex_Embedded;
  local_state_field := LocalState_ι_address; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_uint128Index: LocalStateField XInteger128 :=
{
  local_index_embedded := LocalState_ι_uint128Index_Embedded;
  local_state_field := LocalState_ι_uint128; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_StateInitIndex: LocalStateField StateInit :=
{
  local_index_embedded := LocalState_ι_StateInitIndex_Embedded;
  local_state_field := LocalState_ι_StateInit; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_DTradingPairIndex: LocalStateField DTradingPair :=
{
  local_index_embedded := LocalState_ι_DTradingPairIndex_Embedded;
  local_state_field := LocalState_ι_DTradingPair; 
  local_field_type_correct := eq_refl
}.



(* Global Instance LocalState_ι_hndlITradingPairIndex: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_hndlITradingPairIndex_Embedded;
  local_state_field := LocalState_ι_hndlITradingPairIndex; 
  local_field_type_correct := eq_refl
}. *)



Global Instance LocalState_ι_DXchgPairIndex: LocalStateField DXchgPair :=
{
  local_index_embedded := LocalState_ι_DXchgPairIndex_Embedded;
  local_state_field := LocalState_ι_DXchgPair; 
  local_field_type_correct := eq_refl
}.



(* Global Instance LocalState_ι_hndlIXchgPairIndex: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_hndlIXchgPairIndex_Embedded;
  local_state_field := LocalState_ι_hndlIXchgPairIndex; 
  local_field_type_correct := eq_refl
}.
 *)


Global Instance LocalState_ι_prsFLeXSellArgsIndex: LocalStateField FLeXSellArgs :=
{
  local_index_embedded := LocalState_ι_prsFLeXSellArgsIndex_Embedded;
  local_state_field := LocalState_ι_prsFLeXSellArgsIndex; 
  local_field_type_correct := eq_refl
}.



(* Global Instance LocalState_ι_hndlIPriceIndex: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_hndlIPriceIndex_Embedded;
  local_state_field := LocalState_ι_hndlIPriceIndex; 
  local_field_type_correct := eq_refl
}. *)



Global Instance LocalState_ι_SellArgsIndex: LocalStateField SellArgs :=
{
  local_index_embedded := LocalState_ι_SellArgsIndex_Embedded;
  local_state_field := LocalState_ι_SellArgs; 
  local_field_type_correct := eq_refl
}.



(* Global Instance LocalState_ι_prsFLeXBuyArgsIndex: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_prsFLeXBuyArgsIndex_Embedded;
  local_state_field := LocalState_ι_prsFLeXBuyArgsIndex; 
  local_field_type_correct := eq_refl
}. *)



(* Global Instance LocalState_ι_prsFLeXCancelArgsIndex: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_prsFLeXCancelArgsIndex_Embedded;
  local_state_field := LocalState_ι_prsFLeXCancelArgsIndex; 
  local_field_type_correct := eq_refl
}. *)



(* Global Instance LocalState_ι_prsFLeXXchgCancelArgsIndex: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_prsFLeXXchgCancelArgsIndex_Embedded;
  local_state_field := LocalState_ι_prsFLeXXchgCancelArgsIndex; 
  local_field_type_correct := eq_refl
}. *)



(* Global Instance LocalState_ι_hndlIPriceXchgIndex: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_hndlIPriceXchgIndex_Embedded;
  local_state_field := LocalState_ι_hndlIPriceXchgIndex; 
  local_field_type_correct := eq_refl
}. *)



Global Instance LocalState_ι_bool_tIndex: LocalStateField XBool :=
{
  local_index_embedded := LocalState_ι_bool_tIndex_Embedded;
  local_state_field := LocalState_ι_bool_t; 
  local_field_type_correct := eq_refl
}.



(* Global Instance LocalState_ι_prsFLeXXchgArgsIndex: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_prsFLeXXchgArgsIndex_Embedded;
  local_state_field := LocalState_ι_prsFLeXXchgArgsIndex; 
  local_field_type_correct := eq_refl
}. *)



Global Instance LocalState_ι_PayloadArgsIndex: LocalStateField PayloadArgs :=
{
  local_index_embedded := LocalState_ι_PayloadArgsIndex_Embedded;
  local_state_field := LocalState_ι_PayloadArgs; 
  local_field_type_correct := eq_refl
}.



(* Global Instance LocalState_ι_hndlITONTokenWalletIndex: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_hndlITONTokenWalletIndex_Embedded;
  local_state_field := LocalState_ι_hndlITONTokenWalletIndex; 
  local_field_type_correct := eq_refl
}. *)



Global Instance LocalState_ι_uint8Index: LocalStateField XInteger8 :=
{
  local_index_embedded := LocalState_ι_uint8Index_Embedded;
  local_state_field := LocalState_ι_uint8; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_Tip3ConfigIndex: LocalStateField Tip3Config :=
{
  local_index_embedded := LocalState_ι_Tip3ConfigIndex_Embedded;
  local_state_field := LocalState_ι_Tip3Config; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_DPriceIndex: LocalStateField Price :=
{
  local_index_embedded := LocalState_ι_DPriceIndex_Embedded;
  local_state_field := LocalState_ι_DPrice; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_DPriceXchgIndex: LocalStateField PriceXchg :=
{
  local_index_embedded := LocalState_ι_DPriceXchgIndex_Embedded;
  local_state_field := LocalState_ι_DPriceXchg; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_uint32Index: LocalStateField XInteger32 :=
{
  local_index_embedded := LocalState_ι_uint32Index_Embedded;
  local_state_field := LocalState_ι_uint32; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_unsignedIndex: LocalStateField XInteger :=
{
  local_index_embedded := LocalState_ι_unsignedIndex_Embedded;
  local_state_field := LocalState_ι_unsigned; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_OrderInfoIndex: LocalStateField OrderInfo :=
{
  local_index_embedded := LocalState_ι_OrderInfoIndex_Embedded;
  local_state_field := LocalState_ι_OrderInfo; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_intIndex: LocalStateField XInteger :=
{
  local_index_embedded := LocalState_ι_intIndex_Embedded;
  local_state_field := LocalState_ι_int; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_optional_uint128_Index: LocalStateField (XMaybe XInteger128) :=
{
  local_index_embedded := LocalState_ι_optional_uint128_Index_Embedded;
  local_state_field := LocalState_ι_optional_uint128_; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_boolIndex: LocalStateField XBool :=
{
  local_index_embedded := LocalState_ι_boolIndex_Embedded;
  local_state_field := LocalState_ι_bool; 
  local_field_type_correct := eq_refl
}.



(* Global Instance LocalState_ι_optOrderInfoWithIdxIndex: LocalStateField (XMaybe (XInteger*OrderInfo)) :=
{
  local_index_embedded := LocalState_ι_optOrderInfoWithIdxIndex_Embedded;
  local_state_field := LocalState_ι_optOrderInfoWithIdx; 
  local_field_type_correct := eq_refl
}. *)



Global Instance LocalState_ι_pair_unsigned_OrderInfo_Index: LocalStateField (XInteger*OrderInfo) :=
{
  local_index_embedded := LocalState_ι_pair_unsigned_OrderInfo_Index_Embedded;
  local_state_field := LocalState_ι_pair_unsigned_OrderInfo_; 
  local_field_type_correct := eq_refl
}.



(* Global Instance LocalState_ι_optOrderRetIndex: LocalStateField (XMaybe OrderRet) :=
{
  local_index_embedded := LocalState_ι_optOrderRetIndex_Embedded;
  local_state_field := LocalState_ι_optOrderRet; 
  local_field_type_correct := eq_refl
}. *)



(* Global Instance LocalState_ι_optaddressIndex: LocalStateField (XMaybe XAddress) :=
{
  local_index_embedded := LocalState_ι_optaddressIndex_Embedded;
  local_state_field := LocalState_ι_optaddress; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_optOrderInfoXchg
Index: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_optOrderInfoXchg
Index_Embedded;
  local_state_field := LocalState_ι_optOrderInfoXchg
Index; 
  local_field_type_correct := eq_refl
}.



Global Instance LocalState_ι_optOrderInfoXchgWithIdx
Index: LocalStateField ***** :=
{
  local_index_embedded := LocalState_ι_optOrderInfoXchgWithIdx
Index_Embedded;
  local_state_field := LocalState_ι_optOrderInfoXchgWithIdx
Index; 
  local_field_type_correct := eq_refl
}.
 *)



End LedgerClass .
