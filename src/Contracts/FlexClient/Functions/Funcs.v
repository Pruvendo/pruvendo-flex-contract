Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
From elpi Require Import elpi.
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Contracts.FlexClient.Ledger.
Require Import Contracts.FlexClient.Functions.FuncSig.
Require Import Contracts.FlexClient.Functions.FuncNotations.
Require Import Contracts.FlexClient.Interface.


Elpi Command AddLocalState.

Elpi Accumulate lp:{{

main [Name , Term, LocalStateFieldT] :-
  trm TrmInternal = Term,
  trm LocalStateField = LocalStateFieldT,
  str NameStr = Name,
  N is NameStr ^ "_j",
  coq.env.add-axiom N  (app [LocalStateField , TrmInternal]) _ , 
  coq.locate  N GR, 
  coq.TC.declare-instance GR 0,
  coq.say TrmInternal.
main _ :- coq.error "usage: AddLocalState <name> <term> <LocalStateField>".

}}.

Elpi Typecheck.
Elpi Export AddLocalState.

Module Type Has_Internal.

Parameter Internal : bool .
Parameter TIP3_ENABLE_EXTERNAL : bool .

End Has_Internal.


Module Funcs (ha : Has_Internal)(dc : ConstsTypesSig XTypesModule StateMonadModule) . 
Import ha.
 
Module Export FuncNotationsModuleForFuncs := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.CommonNotationsModule.

Module FuncsInternal <: SpecModuleForFuncNotations.SpecSig. 
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.
Local Open Scope ucpp_scope.

Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.

Locate "_ && _".

(* inline cell prepare_persistent_data(persistent_data_header_t<IContract, ReplayAttackProtection> persistent_data_header,
                                    DContract base) {
  using namespace schema;
  auto data_tup = to_std_tuple(base);
  if constexpr (persistent_header_info<IContract, ReplayAttackProtection>::non_empty) {
    auto data_tup_combined = std::tuple_cat(std::make_tuple(bool_t(false), persistent_data_header), data_tup);
    auto chain_tup = make_chain_tuple(data_tup_combined);
    return build(chain_tup).make_cell();
  } else {
    auto data_tup_combined = std::tuple_cat(std::make_tuple(bool_t(false)), data_tup);
    auto chain_tup = make_chain_tuple(data_tup_combined);
    return build(chain_tup).make_cell();
  }
} *)
Definition prepare_persistent_data { X Y } (persistent_data_header : X) 
                                           (base : Y): UExpression XCell false .
 refine {{ return_ {} }} .  
Defined .

Definition prepare_persistent_data_right { X Y a1 a2 }  
                                    ( persistent_data_header : URValue ( X ) a1 ) 
                                    ( base : URValue ( Y ) a2 ) 
               : URValue ( XCell ) (orb a2 a1) := 
 wrapURExpression (ursus_call_with_args ( LedgerableWithArgs:= λ2 ) prepare_persistent_data 
persistent_data_header base ) . 
 
 Notation " 'prepare_persistent_data_' '(' a ',' b ')' " := 
 ( prepare_persistent_data_right 
 a b ) 
 (in custom URValue at level 0 , 
   a custom URValue at level 0 
 , b custom URValue at level 0 ) : ursus_scope . 

  
Definition constructor ( pubkey : ( uint256 ) ) ( trading_pair_code : ( XCell ) ) ( xchg_pair_code : ( XCell ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( (#{pubkey}) != 0 ) , error_code::zero_owner_pubkey ) ; { _ } }} . 
 	 	 refine {{ _owner_ := #{pubkey} ; { _ } }} . 
 	 	 refine {{ _trading_pair_code_ := #{ trading_pair_code } ; { _ } }} . 
 	 	 refine {{ _xchg_pair_code_ := #{ xchg_pair_code } ; { _ } }} . 
 	 	 refine {{ _workchain_id_ := {} (* Std :: get < addr_std > ( Address { tvm_myaddr ( ) } . val ( ) ) . workchain_id *) ; { _ } }} . 
 	 	 refine {{ _flex_ := {} (* Address :: make_std ( 0 , 0 ) *) }} . 
 Defined .
 
Definition constructor_left { R a1 a2 a3 }  
( pubkey : URValue ( uint256 ) a1 ) 
( trading_pair_code : URValue ( XCell ) a2 ) 
( xchg_pair_code : URValue ( XCell ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) constructor 
 pubkey trading_pair_code xchg_pair_code ) . 
 
 Notation " 'constructor_' '(' pubkey trading_pair_code xchg_pair_code ')' " := 
 ( constructor_left 
 pubkey trading_pair_code xchg_pair_code ) 
 (in custom ULValue at level 0 , pubkey custom URValue at level 0 
 , trading_pair_code custom URValue at level 0 
 , xchg_pair_code custom URValue at level 0 ) : ursus_scope .

 Definition setFlexCfg 
( tons_cfg : ( TonsConfigLRecord ) ) 
( flex : ( XAddress ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( int_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _tons_cfg_ := #{ tons_cfg } ; { _ } }} . 
 	 	 refine {{ _flex_ := #{ flex }  }} . 
 Defined . 
 
 Definition setFlexCfg_left { R a1 a2 }  ( tons_cfg : URValue ( TonsConfigLRecord ) a1 )
 ( flex : URValue ( XAddress ) a2 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) setFlexCfg 
 tons_cfg flex ) . 
 
 Notation " 'setFlexCfg_' '(' tons_cfg flex ')' " := 
 ( setFlexCfg_left 
 tons_cfg flex ) 
 (in custom ULValue at level 0 , tons_cfg custom URValue at level 0 
 , flex custom URValue at level 0 ) : ursus_scope . 
 

 Definition setExtWalletCode ( ext_wallet_code : ( XCell ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( int_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _ext_wallet_code_ ->set ( #{ ext_wallet_code } ) }} . 
 Defined . 
 
 Definition setExtWalletCode_left { R a1 }  ( ext_wallet_code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setExtWalletCode 
 ext_wallet_code ) . 
 
 Notation " 'setExtWalletCode_' '(' ext_wallet_code ')' " := 
 ( setExtWalletCode_left 
 ext_wallet_code ) 
 (in custom ULValue at level 0 , ext_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
 Definition setFlexWalletCode ( flex_wallet_code : ( XCell ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( int_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _flex_wallet_code_ ->set (  #{ flex_wallet_code } ) }} . 
 Defined . 
  Definition setFlexWalletCode_left { R a1 }  ( flex_wallet_code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setFlexWalletCode 
 flex_wallet_code ) . 
 
 Notation " 'setFlexWalletCode_' '(' flex_wallet_code ')' " := 
 ( setFlexWalletCode_left 
 flex_wallet_code ) 
 (in custom ULValue at level 0 , flex_wallet_code custom URValue at level 0 ) : ursus_scope . 
  
 Definition setFlexWrapperCode ( flex_wrapper_code : ( XCell ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( int_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _flex_wrapper_code_  ->set (  #{ flex_wrapper_code } ) }} . 
 Defined . 
 
 Definition setFlexWrapperCode_left { R a1 }  ( flex_wrapper_code : URValue ( XCell ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) setFlexWrapperCode 
 flex_wrapper_code ) . 
 
 Notation " 'setFlexWrapperCode_' '(' flex_wrapper_code ')' " := 
 ( setFlexWrapperCode_left 
 flex_wrapper_code ) 
 (in custom ULValue at level 0 , flex_wrapper_code custom URValue at level 0 ) : ursus_scope .


(* std::pair<StateInit, uint256> prepare_trading_pair_state_init_and_addr(DTradingPair pair_data, cell pair_code) {
  cell pair_data_cl = prepare_persistent_data<ITradingPair, void, DTradingPair>({}, pair_data);
  StateInit pair_init {
    /*split_depth*/{}, /*special*/{},
(*     pair_code, pair_data_cl, /*library*/{} *)
  };
  cell pair_init_cl = build(pair_init).make_cell();
  return { pair_init, uint256(tvm_hash(pair_init_cl)) };
} *)

Definition prepare_trading_pair_state_init_and_addr ( pair_data : DTradingPairLRecord ) 
                                                    ( pair_code : XCell  ) 
                           : UExpression (StateInitLRecord # uint256) false .
 	 	 refine {{ new 'pair_data_cl : XCell @ "pair_data_cl" :=  
                       prepare_persistent_data_ ( {} , #{pair_data} ) ; { _ } }} .
                       Check || [$
                       {} ⇒ { StateInit_ι_split_depth } ;
                       {} ⇒ { StateInit_ι_special } ;
                       ( #{pair_code} ) -> set () ⇒ {StateInit_ι_code} ;
                       ( !{pair_data_cl} ) -> set () ⇒ {StateInit_ι_data} ;
                       {} ⇒ {StateInit_ι_library}
                  $] ||.
 	 	 refine {{ new 'pair_init : StateInitLRecord @ "pair_init" := {}
                   (* [$
                         {} ⇒ { StateInit_ι_split_depth } ;
                         {} ⇒ { StateInit_ι_special } ;
                         ( #{pair_code} ) -> set () ⇒ {StateInit_ι_code} ;
                         ( !{pair_data_cl} ) -> set () ⇒ {StateInit_ι_data} ;
                         {} ⇒ {StateInit_ι_library}
                    $] *) ; { _ } }}.
 	 	 refine {{ new 'pair_init_cl : XCell @ "pair_init_cl" := {} (* build(pair_init).make_cell() *) ; { _ } }} .
 	 	 refine {{ return_ [ !{pair_init} , {} (* tvm_hash(pair_init_cl) *) ] }} .
Defined.

Definition prepare_trading_pair_state_init_and_addr_right {b1 b2} 
(x0: URValue DTradingPairLRecord b1 ) 
(x1: URValue XCell b2 ) 
: URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) prepare_trading_pair_state_init_and_addr x0 x1).    

Notation " 'prepare_trading_pair_state_init_and_addr_' '(' x0 ',' x1 ')' " := (prepare_trading_pair_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.


 Definition deployTradingPair ( tip3_root : ( XAddress ) ) ( deploy_min_value : ( uint128 ) ) 
( deploy_value : ( uint128 ) ) ( min_trade_amount : ( uint128 ) ) ( notify_addr : ( XAddress ) ) : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( int_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} .
 	 	 refine {{ new 'pair_data : (DTradingPairLRecord ) @ "pair_data" :=  
 	 	        [$ _flex_ ⇒ { DTradingPair_ι_flex_addr_ } ; 
               (#{ tip3_root }) ⇒ { DTradingPair_ι_tip3_root_ } ; 
                 0 ⇒ { DTradingPair_ι_notify_addr_ }  
               $] ; { _ } }} . 
      refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) @ ("state_init", "std_addr") :=
            prepare_trading_pair_state_init_and_addr_ ( !{ pair_data } , _trading_pair_code_ )  ; { _ } }} . 
 	 	 refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {} ; { _ } }} . 
 	 	             (*  ITradingPairPtr ( Address :: make_std ( workchain_id_ , std_addr ) )  *) 
(*  	 	 refine {{ trade_pair.deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( min_trade_amount , deploy_min_value , notify_addr ) ; { _ } }} .  *)
 	 	 refine {{ return_  !{trade_pair} }} . 
 Defined . 

 Definition deployTradingPair_right { a1 a2 a3 a4 a5 }  ( tip3_root : URValue ( XAddress ) a1 ) ( deploy_min_value : URValue ( uint128 ) a2 ) ( deploy_value : URValue ( uint128 ) a3 ) ( min_trade_amount : URValue ( uint128 ) a4 ) ( notify_addr : URValue ( XAddress ) a5 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) deployTradingPair 
 tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ) . 
 
 Notation " 'deployTradingPair_' '(' tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ')' " := 
 ( deployTradingPair_right 
 tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

Definition prepare_xchg_pair_state_init_and_addr ( pair_data : DXchgPairLRecord ) 
                                                    ( pair_code : XCell  ) 
                           : UExpression (StateInitLRecord # uint256) false .
 	 	 refine {{ new 'pair_data_cl : XCell @ "pair_data_cl" :=  
                      prepare_persistent_data_ ( {} , #{pair_data} ) ; { _ } }} .
 	 	 refine {{ new 'pair_init : StateInitLRecord @ "pair_init" :=
                   [$
                         {} ⇒ { StateInit_ι_split_depth } ;
                         {} ⇒ { StateInit_ι_special } ;
                         ( #{pair_code} ) -> set () ⇒ {StateInit_ι_code} ;
                         ( !{pair_data_cl} ) -> set () ⇒ {StateInit_ι_data} ;
                         {} ⇒ {StateInit_ι_library}
                    $] ; { _ } }}.
 	 	 refine {{ new 'pair_init_cl : XCell @ "pair_init_cl" := {} (* build(pair_init).make_cell() *) ; { _ } }} .
 	 	 refine {{ return_ [ !{pair_init} , {} (* tvm_hash(pair_init_cl) *) ] }} .
Defined.

Definition prepare_xchg_pair_state_init_and_addr_right {b1 b2} 
(x0: URValue DXchgPairLRecord b1 ) 
(x1: URValue XCell b2 ) 
: URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) := 
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) prepare_xchg_pair_state_init_and_addr x0 x1).    

Notation " 'prepare_xchg_pair_state_init_and_addr_' '(' x0 ',' x1 ')' " := (prepare_xchg_pair_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.

Definition deployXchgPair ( tip3_major_root : ( address_t ) ) 
                           ( tip3_minor_root : ( address_t ) ) 
                           ( deploy_min_value : ( uint128 ) ) 
                           ( deploy_value : ( uint128 ) ) 
                           ( min_trade_amount : ( uint128 ) ) 
                           ( notify_addr : ( address_t ) ) 
                            : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} .
 	 	 refine {{ new 'pair_data : ( DXchgPairLRecord ) @ "pair_data" :=  
               	 	 [$  (* _flex_  ⇒ { DXchgPair_ι_flex_addr_ } ; *) 
                      (#{ tip3_major_root }) ⇒ { DXchgPair_ι_tip3_major_root_ } ; 
                      (#{ tip3_minor_root }) ⇒ { DXchgPair_ι_tip3_minor_root_ } ; 
                      0 ⇒ { DXchgPair_ι_notify_addr_ }
                          $] ; { _ } }} . 
      refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) @ ("state_init", "std_addr") :=
           prepare_xchg_pair_state_init_and_addr_ ( !{ pair_data } , _xchg_pair_code_ )  ; { _ } }} .   
 	 	 refine {{ new 'trade_pair : ( XAddress ) @ "trade_pair" := {} ; { _ } }} . 
 	 	 refine {{ { trade_pair } := {} (* IXchgPairPtr ( Address :: make_std ( workchain_id_ , std_addr ) ) *) ; { _ } }} . 
(*  	 	 refine {{ trade_pair.deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . onDeploy ( min_trade_amount , deploy_min_value , notify_addr ) ; { _ } }} .  *)
 	 	 refine {{ return_ !{trade_pair} }} . 
 Defined .
 
 Definition deployXchgPair_right { a1 a2 a3 a4 a5 a6 }  ( tip3_major_root : URValue ( address_t ) a1 ) ( tip3_minor_root : URValue ( address_t ) a2 ) ( deploy_min_value : URValue ( uint128 ) a3 ) ( deploy_value : URValue ( uint128 ) a4 ) ( min_trade_amount : URValue ( uint128 ) a5 ) ( notify_addr : URValue ( address_t ) a6 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) deployXchgPair 
 tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ) . 
 
 Notation " 'deployXchgPair_' '(' tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ')' " := 
 ( deployXchgPair_right 
 tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

(* std::pair<StateInit, uint256> prepare_price_state_init_and_addr(DPrice price_data, cell price_code) {
  cell price_data_cl = prepare_persistent_data<IPrice, void, DPrice>({}, price_data);
  StateInit price_init {
    /*split_depth*/{}, /*special*/{},
    price_code, price_data_cl, /*library*/{}
  };
  cell price_init_cl = build(price_init).make_cell();
  return { price_init, uint256(tvm_hash(price_init_cl)) };
} *)

Definition prepare_price_state_init_and_addr ( price_data : DPriceLRecord ) 
                                             ( price_code : XCell ) 
                           : UExpression (StateInitLRecord # uint256) false .
 	 	 refine {{ new 'price_data_cl : XCell @ "price_data_cl" :=  
                       prepare_persistent_data_ ( {}, #{price_data} ) ; { _ } }} .
 	 	 refine {{ new 'price_init : StateInitLRecord @ "pair_init" :=
                   [$
                         {} ⇒ { StateInit_ι_split_depth } ;
                         {} ⇒ { StateInit_ι_special } ;
                         ( #{price_code} ) -> set () ⇒ {StateInit_ι_code} ;
                         ( !{price_data_cl} ) -> set () ⇒ {StateInit_ι_data} ;
                         {} ⇒ {StateInit_ι_library}
                    $] ; { _ } }}.
 	 	 refine {{ new 'price_init_cl : XCell @ "price_init_cl" := {} (* build(price_init).make_cell() *) ; { _ } }} .
 	 	 refine {{ return_ [ !{price_init} , {} (* tvm_hash(price_init_cl) *) ] }} .
Defined.

Definition prepare_price_state_init_and_addr_right {b1 b2} 
(x0: URValue DPriceLRecord b1 ) 
(x1: URValue XCell b2 ) 
: URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) prepare_price_state_init_and_addr x0 x1).    

Notation " 'prepare_price_state_init_and_addr_' '(' x0 ',' x1 ')' " := 
                                         (prepare_price_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.

(* std::tuple<StateInit, address, uint256> preparePrice(
      uint128 price, uint128 min_amount, uint8 deals_limit, cell tip3_code, Tip3Config tip3cfg,
      cell price_code, address_t notify_addr) const {
    DPrice price_data {
      .price_ = price,
      .sells_amount_ = uint128(0),
      .buys_amount_ = uint128(0),
      .flex_ = flex_,
      .min_amount_ = min_amount,
      .deals_limit_ = deals_limit,
      .notify_addr_ = IFlexNotifyPtr(notify_addr),
      .workchain_id_ = workchain_id_,
      .tons_cfg_ = tons_cfg_,
      .tip3_code_ = tip3_code,
      .tip3cfg_ = tip3cfg,
      .sells_ = {},
      .buys_ = {}
    };
    auto [state_init, std_addr] = prepare_price_state_init_and_addr(price_data, price_code);
    auto addr = address::make_std(workchain_id_, std_addr);
    return { state_init, addr, std_addr };
  } *)

Definition preparePrice (price min_amount : uint128 ) (deals_limit : uint8 )
                        (tip3_code: XCell  )
                        (tip3cfg: Tip3ConfigLRecord ) (price_code: XCell  )
                        (notify_addr: XAddress  )
: UExpression (StateInitLRecord # (XAddress # uint256)) false .  
 	 	 refine {{ new 'price_data : DPriceLRecord @ "price_data" :=
        [$
           (#{price})  ⇒ { DPrice_ι_price_ } ;
           0  ⇒ { DPrice_ι_sells_amount_ } ;
           0  ⇒ { DPrice_ι_buys_amount_ } ;
          (*  _flex_  ⇒ { DPrice_ι_flex_ } ; *)
           (#{min_amount})  ⇒ { DPrice_ι_min_amount_ } ;
           (#{deals_limit})  ⇒ { DPrice_ι_deals_limit_ } ;
           (#{notify_addr})  ⇒ { DPrice_ι_notify_addr_ } ;
           _workchain_id_  ⇒ { DPrice_ι_workchain_id_ } ;
           _tons_cfg_  ⇒ { DPrice_ι_tons_cfg_ } ;
           (#{tip3_code})  ⇒ { DPrice_ι_tip3_code_ } ;
           (#{tip3cfg})  ⇒ { DPrice_ι_tip3cfg_ } ;
           {}  ⇒ { DPrice_ι_sells_ } ;
           {}  ⇒ { DPrice_ι_buys_ }
         $] ; { _ } }} .
      refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) @ ("state_init", "std_addr") :=
           prepare_price_state_init_and_addr_ ( !{ price_data } , #{price_code} ) ; { _ } }} .   
 	 	 refine {{ new 'addr : XAddress @ "addr" := {} (* address::make_std(workchain_id_, std_addr) *) ; { _ } }} .
 	 	 refine {{ return_ [ !{state_init} , !{addr} , !{std_addr} ] }} .
Defined.

Definition preparePrice_right {b1 b2 b3 b4 b5 b6 b7} 
(x0: URValue uint128 b1 ) 
(x1: URValue uint128 b2 ) 
(x2: URValue uint8 b3 ) 
(x3: URValue XCell b4 ) 
(x4: URValue Tip3ConfigLRecord b5 ) 
(x5: URValue XCell b6 ) 
(x6: URValue XAddress b7)
: URValue (StateInitLRecord # (XAddress # uint256)) (orb(orb(orb(orb(orb(orb b7 b6) b5) b4)b3) b2) b1) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ7) preparePrice x0 x1 x2 x3 x4 x5 x6 ).    

Notation " 'preparePrice_' '(' x0 ',' x1 , x2 ',' x3 , x4 ',' x5 ',' x6 ')' " := 
                                         (preparePrice_right x0 x1 x2 x3 x4 x5 x6)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0,
    x2 custom URValue at level 0,
    x3 custom URValue at level 0,
    x4 custom URValue at level 0,
    x5 custom URValue at level 0,
    x6 custom URValue at level 0 ) : ursus_scope.

 Definition deployPriceWithSell 
( price : ( uint128 ) ) 
( amount : ( uint128 ) ) 
( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) 
( tons_value : ( uint128 ) ) 
( price_code : ( XCell ) ) 
( my_tip3_addr : ( XAddress ) ) 
( receive_wallet : ( XAddress ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( XAddress ) ) 
: UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
      refine {{ new ( 'state_init : StateInitLRecord , 
                      'addr : XAddress ,
                      'std_addr : uint256 ) @ ("state_init", "addr" , "std_addr") :=
                 preparePrice_ ( #{price} , #{min_amount} , #{deals_limit} , 
                                 _flex_wallet_code_ ->  get () , #{tip3cfg} ,
                                        #{price_code} , #{notify_addr} ) ; { _ } }} .
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {} (* IPricePtr ( addr ) *); { _ } }} . 
 	 	 refine {{ new 'deploy_init_cl : ( XCell ) @ "deploy_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ { deploy_init_cl } := {} (* build ( { state_init } ) . endc ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'sell_args : ( SellArgsLRecord ) @ "sell_args" :=
                   [$ (#{amount}) ⇒ {SellArgs_ι_amount} ;
             (#{receive_wallet}) ⇒ { SellArgs_ι_receive_wallet }  
                    $] ; { _ } }} .
 	 	 refine {{ new 'payload : ( XCell ) @ "payload" := {} ; { _ } }} . 
 	 	 refine {{ { payload } := {} (* build ( { sell_args } ) . endc ( ) *) ; { _ } }} . 
     refine {{ new 'my_tip3 : ( XAddress ) @ "my_tip3" := #{ my_tip3_addr } ; { _ } }} .
 (* 	 	 refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . lendOwnership ( address { tvm_myaddr ( ) } , uint128 ( 0 ) , std_addr , amount , lend_finish_time , deploy_init_cl , payload ) ; { _ } }} . *)
 	 	 refine {{ return_ !{price_addr} }} . 
 Defined .

 Definition deployPriceWithSell_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 }  
( price : URValue ( uint128 ) a1 ) 
( amount : URValue ( uint128 ) a2 ) 
( lend_finish_time : URValue ( uint32 ) a3 ) 
( min_amount : URValue ( uint128 ) a4 ) 
( deals_limit : URValue ( uint8 ) a5 ) 
( tons_value : URValue ( uint128 ) a6 ) 
( price_code : URValue ( XCell ) a7 ) 
( my_tip3_addr : URValue ( XAddress ) a8 ) 
( receive_wallet : URValue ( XAddress ) a9 ) 
( tip3cfg : URValue ( Tip3ConfigLRecord ) a10 ) 
( notify_addr : URValue ( XAddress ) a11 ) 
: URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ11 ) deployPriceWithSell 
 price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceWithSell_' '(' price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ')' " := 
 ( deployPriceWithSell_right 
 price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , receive_wallet custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

 Definition deployPriceWithBuy ( price : ( uint128 ) ) ( amount : ( uint128 ) ) 
( order_finish_time : ( uint32 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( deploy_value : ( uint128 ) ) ( price_code : ( XCell ) ) ( my_tip3_addr : ( address_t ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ) : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
      refine {{ new ( 'state_init : StateInitLRecord , 
                      'addr : XAddress ,
                      'std_addr : uint256 ) @ ("state_init", "addr" , "std_addr") :=
                 preparePrice_ ( #{price} , #{min_amount} , #{deals_limit} , _flex_wallet_code_ -> get () , #{tip3cfg} ,
                       #{price_code} , #{notify_addr} ) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr":= {} ; { _ } }} . 
 (*	 refine {{ price_addr.deploy ( state_init , Grams ( deploy_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . buyTip3 ( amount , my_tip3_addr , order_finish_time ) ; { _ } }} . *)
 	 	 refine {{ return_ !{price_addr} }} . 
 Defined . 
 
 Definition deployPriceWithBuy_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  ( price : URValue ( uint128 ) a1 ) ( amount : URValue ( uint128 ) a2 ) ( order_finish_time : URValue ( uint32 ) a3 ) ( min_amount : URValue ( uint128 ) a4 ) ( deals_limit : URValue ( uint8 ) a5 ) ( deploy_value : URValue ( uint128 ) a6 ) ( price_code : URValue ( XCell ) a7 ) ( my_tip3_addr : URValue ( address_t ) a8 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a9 ) ( notify_addr : URValue ( address_t ) a10 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ10 ) deployPriceWithBuy 
 price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceWithBuy_' '(' price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ')' " := 
 ( deployPriceWithBuy_right 
 price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 
 , order_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , deploy_value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

 Definition cancelSellOrder ( price : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( value : ( uint128 ) ) ( price_code : ( XCell ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
      refine {{ new ( 'state_init : StateInitLRecord , 
                      'addr : XAddress ,
                      'std_addr : uint256 ) @ ("state_init", "addr" , "std_addr") :=
             preparePrice_ ( #{price} , #{min_amount} , #{deals_limit} , _flex_wallet_code_ -> get () , #{tip3cfg} , 
                            #{price_code} , #{notify_addr} ) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {}  ; { _ } }} . 
(*  	 	 refine {{ price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelSell ( ) ; { _ } }} .  *)
refine {{ {price_addr} := !{price_addr} }} .
 Defined .

 Definition cancelSellOrder_left { R a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue ( uint128 ) a1 ) ( min_amount : URValue ( uint128 ) a2 ) ( deals_limit : URValue ( uint8 ) a3 ) ( value : URValue ( uint128 ) a4 ) ( price_code : URValue ( XCell ) a5 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) ( notify_addr : URValue ( address_t ) a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancelSellOrder 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) . 
 
 Notation " 'cancelSellOrder_' '(' price min_amount deals_limit value price_code tip3cfg notify_addr ')' " := 
 ( cancelSellOrder_left 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
Definition cancelBuyOrder ( price : ( uint128 ) ) ( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) 
( value : ( uint128 ) ) ( price_code : ( XCell ) ) ( tip3cfg : ( Tip3ConfigLRecord ) ) ( notify_addr : ( address_t ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
      refine {{ new ( 'state_init : StateInitLRecord , 
                      'addr : XAddress ,
                      'std_addr : uint256 ) @ ("state_init", "addr" , "std_addr") :=
                  preparePrice_ ( #{price} , #{min_amount} , #{deals_limit} , _flex_wallet_code_ -> get () , 
                             #{tip3cfg} , #{price_code} , #{notify_addr} ) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {}; { _ } }} . 
 	 	 refine {{ {price_addr} := !{price_addr} (* price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelBuy ( ) *) }} . 
 Defined .

  Definition cancelBuyOrder_left { R a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue ( uint128 ) a1 ) ( min_amount : URValue ( uint128 ) a2 ) ( deals_limit : URValue ( uint8 ) a3 ) ( value : URValue ( uint128 ) a4 ) ( price_code : URValue ( XCell ) a5 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) ( notify_addr : URValue ( address_t ) a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) cancelBuyOrder 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) . 
 
 Notation " 'cancelBuyOrder_' '(' price min_amount deals_limit value price_code tip3cfg notify_addr ')' " := 
 ( cancelBuyOrder_left 
 price min_amount deals_limit value price_code tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
(* std::pair<StateInit, uint256> prepare_price_xchg_state_init_and_addr(DPriceXchg price_data, cell price_code) {
  cell price_data_cl = prepare_persistent_data<IPriceXchg, void, DPriceXchg>({}, price_data);
  StateInit price_init {
    /*split_depth*/{}, /*special*/{},
    price_code, price_data_cl, /*library*/{}
  };
  cell price_init_cl = build(price_init).make_cell();
  return { price_init, uint256(tvm_hash(price_init_cl)) };
} *)
Definition prepare_price_xchg_state_init_and_addr ( price_data : DPriceXchgLRecord ) 
                                             ( price_code : XCell ) 
                           : UExpression (StateInitLRecord # uint256) false .
 	 	 refine {{ new 'price_data_cl : XCell @ "price_data_cl" :=  
                       prepare_persistent_data_ ( {} , #{price_data} )  ; { _ } }} .
 	 	 refine {{ new 'price_init : StateInitLRecord @ "pair_init" :=
                   [$
                         {} ⇒ { StateInit_ι_split_depth } ;
                         {} ⇒ { StateInit_ι_special } ;
                         (#{price_code} ) -> set () ⇒ {StateInit_ι_code} ;
                         ( !{price_data_cl} ) -> set () ⇒ {StateInit_ι_data} ;
                         {} ⇒ {StateInit_ι_library}
                    $] ; { _ } }}.
 	 	 refine {{ new 'price_init_cl : XCell @ "price_init_cl" := {} (* build(price_init).make_cell() *) ; { _ } }} .
 	 	 refine {{ return_ [ !{price_init} , {} (* tvm_hash(price_init_cl) *) ] }} .
Defined.

Definition prepare_price_xchg_state_init_and_addr_right {b1 b2} 
(x0: URValue DPriceXchgLRecord b1 ) 
(x1: URValue XCell b2 ) 
: URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) prepare_price_xchg_state_init_and_addr x0 x1).    

Notation " 'prepare_price_xchg_state_init_and_addr_' '(' x0 ',' x1 ')' " := 
                                         (prepare_price_xchg_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.

 Definition preparePriceXchg ( price_num : ( uint128 ) ) 
( price_denum : ( uint128 ) ) ( min_amount : ( uint128 ) ) 
( deals_limit : ( uint8 ) ) ( major_tip3cfg : ( Tip3ConfigLRecord ) ) 
( minor_tip3cfg : ( Tip3ConfigLRecord ) ) ( price_code : ( XCell ) )
 ( notify_addr : ( address_t ) ) 
: UExpression ( StateInitLRecord # ( XAddress # uint256 ) ) false . 
 	 	 refine {{ new 'price_data : ( DPriceXchgLRecord ) @ "price_data" :=  
               [$
                 [$ (#{price_num}) ⇒ {RationalPrice_ι_num} ; 
                    (#{price_denum}) ⇒ {RationalPrice_ι_denum} $] 
                                     ⇒ { DPriceXchg_ι_price_ } ;
               0 ⇒ { DPriceXchg_ι_sells_amount_ } ;
               0 ⇒ { DPriceXchg_ι_buys_amount_ }  ;
             (*   _flex_ ⇒ { DPriceXchg_ι_flex_ } ; *)
               (#{ min_amount }) ⇒ { DPriceXchg_ι_min_amount_ } ;
               (#{ deals_limit }) ⇒ { DPriceXchg_ι_deals_limit_ } ;
               (#{ notify_addr }) ⇒ { DPriceXchg_ι_notify_addr_ } ;
               _workchain_id_ ⇒ { DPriceXchg_ι_workchain_id_ } ;
               _tons_cfg_ ⇒ { DPriceXchg_ι_tons_cfg_ } ;

               ( _flex_wallet_code_ -> get_default () ) ⇒ { DPriceXchg_ι_tip3_code_ } ;

               (#{ major_tip3cfg }) ⇒ { DPriceXchg_ι_major_tip3cfg_ } ; 
               (#{ minor_tip3cfg }) ⇒ { DPriceXchg_ι_minor_tip3cfg_ } ; 
               {} ⇒ { DPriceXchg_ι_sells_ } ; 
               {} ⇒ { DPriceXchg_ι_buys_ }  
                 $] ; { _ } }} . 
      refine {{ new ( 'state_init : StateInitLRecord , 
                      'std_addr : uint256 ) @ ("state_init", "std_addr") :=
          prepare_price_xchg_state_init_and_addr_ ( !{price_data} , #{price_code} ) ; { _ } }} . 
 	 	 refine {{ new 'addr : ( XAddress ) @ "addr" := {} (* Address :: make_std ( workchain_id_ , std_addr ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ state_init } , !{ addr } , !{ std_addr } ]  }} . 
 Defined .

 Definition preparePriceXchg_right { a1 a2 a3 a4 a5 a6 a7 a8 }  ( price_num : URValue ( uint128 ) a1 ) ( price_denum : URValue ( uint128 ) a2 ) ( min_amount : URValue ( uint128 ) a3 ) ( deals_limit : URValue ( uint8 ) a4 ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) a5 ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) a6 ) ( price_code : URValue ( XCell ) a7 ) ( notify_addr : URValue ( address_t ) a8 ) : URValue ( StateInitLRecord # (XAddress # uint256) ) (orb false ( orb ( orb ( orb ( orb ( orb ( orb ( orb a8 a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ8 ) preparePriceXchg 
 price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ) . 
 
 Notation " 'preparePriceXchg_' '(' price_num ',' price_denum ',' min_amount ',' deals_limit ',' major_tip3cfg ',' minor_tip3cfg ',' price_code ',' notify_addr ')' " := 
 ( preparePriceXchg_right 
 price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ) 
 (in custom URValue at level 0 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 
 , price_code custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope .

(* address deployPriceXchg(
    bool_t  sell,
    uint128 price_num,
    uint128 price_denum,
    uint128 amount,
    uint128 lend_amount,
    uint32  lend_finish_time,
    uint128 min_amount,
    uint8   deals_limit,
    uint128 tons_value,
    cell    xchg_price_code,
    address_t my_tip3_addr,
    address_t receive_wallet,
    Tip3Config major_tip3cfg,
    Tip3Config minor_tip3cfg,
    address_t notify_addr
  ) {
    require(msg_pubkey() == owner_, error_code::message_sender_is_not_my_owner);
    require(flex_wallet_code_, error_code::missed_flex_wallet_code);
    tvm_accept();

    auto [state_init, addr, std_addr] =
      preparePriceXchg(price_num, price_denum, min_amount, deals_limit,
                       major_tip3cfg, minor_tip3cfg, xchg_price_code, notify_addr);
    auto price_addr = IPriceXchgPtr(addr);
    cell deploy_init_cl = build(state_init).endc();
    PayloadArgs payload_args = {
      .sell = sell,
      .amount = amount,
      .receive_tip3_wallet = receive_wallet,
      .client_addr = address{tvm_myaddr()}
    };
       cell payload = build(payload_args).endc();

    ITONTokenWalletPtr my_tip3(my_tip3_addr);
    my_tip3(Grams(tons_value.get()), DEFAULT_MSG_FLAGS, false).
      lendOwnership(address{tvm_myaddr()}, uint128(0), std_addr, lend_amount,
                    lend_finish_time, deploy_init_cl, payload);
    return price_addr.get();
  } *)

Definition deployPriceXchg ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( amount : ( uint128 ) ) ( lend_amount : ( uint128 ) ) ( lend_finish_time : ( uint32 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( tons_value : ( uint128 ) ) 
( xchg_price_code : ( XCell ) ) ( my_tip3_addr : ( XAddress ) ) ( receive_wallet : ( XAddress ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( XAddress ) ) : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
      refine {{ new ( 'state_init : StateInitLRecord , 
                      'addr : XAddress ,
                      'std_addr : uint256 ) @ ("state_init", "addr" , "std_addr") 
           := preparePriceXchg_ ( #{price_num} , #{price_denum} , 
              #{min_amount} , #{deals_limit} , #{major_tip3cfg} , #{ minor_tip3cfg} , #{xchg_price_code} , #{notify_addr} ) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {} ; { _ } }} . 
 	 	 refine {{ { price_addr } := !{addr} (* IPriceXchgPtr ( addr ) *) ; { _ } }} . 
 	 	 refine {{ new 'deploy_init_cl : ( XCell ) @ "deploy_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ { deploy_init_cl } := {} (* build ( !{ state_init } ) . endc ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'payload_args : ( PayloadArgsLRecord ) @ "payload_args" :=  
           [$ (#{ sell })  ⇒ { PayloadArgs_ι_sell } ; 
              (#{ amount })  ⇒ { PayloadArgs_ι_amount }(* ; 
              (#{ receive_wallet }) ⇒ { PayloadArgs_ι_receive_tip3_wallet } ;
              ( tvm.address () ) ⇒ { PayloadArgs_ι_client_addr } *) $]  ; { _ } }} . 

 	 	 refine {{ new 'payload : ( XCell ) @ "payload" := {} (* build ( !{ payload_args } ) . endc ( ) *) ; { _ } }} . 
 	 	 refine {{ new 'my_tip3: XAddress @ "my_tip3" := #{ my_tip3_addr } ; { _ } }} . 
(*  	 	 refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . lendOwnership ( address { tvm_myaddr ( ) } , uint128 ( 0 ) , std_addr , lend_amount , lend_finish_time , deploy_init_cl , payload ) ; { _ } }} .  *)
 	 	 refine {{ return_ !{ price_addr } }} . 
 Defined .

 Definition deployPriceXchg_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 }  ( sell : URValue ( XBool ) a1 ) ( price_num : URValue ( uint128 ) a2 ) ( price_denum : URValue ( uint128 ) a3 ) ( amount : URValue ( uint128 ) a4 ) ( lend_amount : URValue ( uint128 ) a5 ) ( lend_finish_time : URValue ( uint32 ) a6 ) ( min_amount : URValue ( uint128 ) a7 ) ( deals_limit : URValue ( uint8 ) a8 ) ( tons_value : URValue ( uint128 ) a9 ) ( xchg_price_code : URValue ( XCell ) a10 ) ( my_tip3_addr : URValue ( address_t ) a11 ) ( receive_wallet : URValue ( address_t ) a12 ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) a13 ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) a14 ) ( notify_addr : URValue ( address_t ) a15 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ15 ) deployPriceXchg 
 sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceXchg_' '(' sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ')' " := 
 ( deployPriceXchg_right 
 sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 
 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , amount custom URValue at level 0 
 , lend_amount custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , tons_value custom URValue at level 0 
 , xchg_price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 
 , receive_wallet custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
 Definition cancelXchgOrder ( sell : ( XBool ) ) ( price_num : ( uint128 ) ) ( price_denum : ( uint128 ) ) 
( min_amount : ( uint128 ) ) ( deals_limit : ( uint8 ) ) ( value : ( uint128 ) ) ( xchg_price_code : ( XCell ) ) 
( major_tip3cfg : ( Tip3ConfigLRecord ) ) ( minor_tip3cfg : ( Tip3ConfigLRecord ) ) 
( notify_addr : ( address_t ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
      refine {{ new ( 'state_init : StateInitLRecord , 
                      'addr : XAddress ,
                      'std_addr : uint256 ) @ ("state_init", "addr" , "std_addr") :=
           preparePriceXchg_ ( #{price_num} , #{price_denum} , #{min_amount} , #{deals_limit} , #{major_tip3cfg} , #{minor_tip3cfg} ,
                               #{xchg_price_code} , #{notify_addr} ) ; { _ } }} . 
 	 	 refine {{ new 'price_addr : ( XAddress ) @ "price_addr" := {} ; { _ } }} . 
 	 	 refine {{ if ( #{ sell } ) then { { _ } } else { { _ } } }} . 
 	 	 	 refine {{ {price_addr} := !{price_addr} (* price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelSell ( )*) }} . 
 	 	 refine {{ {price_addr} := !{price_addr} (* price_addr ( Grams ( value . get ( ) ) , DEFAULT_MSG_FLAGS , false ) . cancelBuy ( ) *) }} . 
 Defined . 
 
 Definition cancelXchgOrder_left { R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  ( sell : URValue ( XBool ) a1 ) ( price_num : URValue ( uint128 ) a2 ) ( price_denum : URValue ( uint128 ) a3 ) ( min_amount : URValue ( uint128 ) a4 ) ( deals_limit : URValue ( uint8 ) a5 ) ( value : URValue ( uint128 ) a6 ) ( xchg_price_code : URValue ( XCell ) a7 ) ( major_tip3cfg : URValue ( Tip3ConfigLRecord ) a8 ) ( minor_tip3cfg : URValue ( Tip3ConfigLRecord ) a9 ) ( notify_addr : URValue ( address_t ) a10 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ10 ) cancelXchgOrder 
 sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ) . 
 
 Notation " 'cancelXchgOrder_' '(' sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ')' " := 
 ( cancelXchgOrder_left 
 sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , sell custom URValue at level 0 
 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 
 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 
 , xchg_price_code custom URValue at level 0 
 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

 Definition transfer ( dest : ( address_t ) ) ( value : ( uint128 ) ) ( bounce : ( XBool ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () (*;  { _ } }} . 
 	 	 refine {{ tvm_transfer ( dest , value . get ( ) , bounce . get ( ) ) ; { _ } *) }} . 
 Defined . 
 
 Definition transfer_left { R a1 a2 a3 }  ( dest : URValue ( address_t ) a1 ) ( value : URValue ( uint128 ) a2 ) ( bounce : URValue ( XBool ) a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) transfer 
 dest value bounce ) . 
 
 Notation " 'transfer_' '(' dest value bounce ')' " := 
 ( transfer_left 
 dest value bounce ) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 
 , value custom URValue at level 0 
 , bounce custom URValue at level 0 ) : ursus_scope . 

(* std::pair<StateInit, uint256> prepare_wallet_state_init_and_addr(TonsConfigFields wallet_data) {
  cell wallet_data_cl =
    prepare_persistent_data<ITONTokenWallet, wallet_replay_protection_t, DTONTokenWallet>(
#ifdef TIP3_ENABLE_EXTERNAL
      wallet_replay_protection_t::init(),
#else
      {},
#endif
      wallet_data);
  StateInit wallet_init {
    /*split_depth*/{}, /*special*/{},
    wallet_data.code_, wallet_data_cl, /*library*/{}
  };
  cell wallet_init_cl = build(wallet_init).make_cell();
  return { wallet_init, uint256(tvm_hash(wallet_init_cl)) };
} *)
Definition prepare_wallet_state_init_and_addr (wallet_data : TonsConfigFields )
 : UExpression ( StateInitLRecord # uint256 ) false .
   
(* refine {{ if ( #{TIP3_ENABLE_EXTERNAL} )
                        then  { { _:UEf } } (* wallet_replay_protection_t::init()  *)
                        else  { { _:UEf } } ; { _ } }}. *)
 	 	 refine {{ new 'wallet_data_cl : XCell @ "price_data_cl" :=  
                       prepare_persistent_data_ ( {} , #{wallet_data} )  ; { _ } }} .
 	 	 refine {{ new 'wallet_init : StateInitLRecord @ "pair_init" :=
                   [$
                         {} ⇒ { StateInit_ι_split_depth } ;
                         {} ⇒ { StateInit_ι_special } ;
                         {} ⇒ {StateInit_ι_code} ;
                         {} ⇒ {StateInit_ι_data} ;
                         {} ⇒ {StateInit_ι_library}
                    $] ; { _ } }}.
 	 	 refine {{ new 'wallet_init_cl : XCell @ "price_init_cl" := {} (* build(wallet_init).make_cell() *) ; { _ } }} .
 	 	 refine {{ return_ [ !{wallet_init} , {} (* tvm_hash(wallet_init_cl) *) ] }} .
Defined.

Definition prepare_wallet_state_init_and_addr_right {b1} 
(x0: URValue TonsConfigFields b1 ) 
: URValue (StateInitLRecord # uint256) ( orb false b1 ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) prepare_wallet_state_init_and_addr x0).    

Notation " 'prepare_wallet_state_init_and_addr_' '(' x0  ')' " := 
                                         (prepare_wallet_state_init_and_addr_right x0)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0) : ursus_scope.

(* std::pair<StateInit, uint256> prepare_wrapper_state_init_and_addr(cell wrapper_code, DWrapper wrapper_data) {
  cell wrapper_data_cl =
    prepare_persistent_data<IWrapper, wrapper_replay_protection_t, DWrapper>(
      wrapper_replay_protection_t::init(), wrapper_data);
  StateInit wrapper_init {
    /*split_depth*/{}, /*special*/{},
    wrapper_code, wrapper_data_cl, /*library*/{}
  };
  cell wrapper_init_cl = build(wrapper_init).make_cell();
  return { wrapper_init, uint256(tvm_hash(wrapper_init_cl)) };
} *)

Definition prepare_wrapper_state_init_and_addr ( wrapper_code : XCell ) 
                                               ( wrapper_data : DWrapperLRecord ) 
                           : UExpression (StateInitLRecord # uint256) false .
 	 	 refine {{ new 'wrapper_data_cl : XCell @ "wrapper_data_cl" :=  
                  prepare_persistent_data_ ( {} ,
      (* wrapper_replay_protection_t::init() *) #{wrapper_data} ) ; { _ } }} .
 	 	 refine {{ new 'wrapper_init : StateInitLRecord @ "pair_init" :=
                   [$
                         {} ⇒ { StateInit_ι_split_depth } ;
                         {} ⇒ { StateInit_ι_special } ;
                         ( #{wrapper_code} ) -> set () ⇒ {StateInit_ι_code} ;
                         ( !{wrapper_data_cl} ) -> set () ⇒ {StateInit_ι_data} ;
                         {} ⇒ {StateInit_ι_library}
                    $] ; { _ } }}.
 	 	 refine {{ new 'wrapper_init_cl : XCell @ "wrapper_init_cl" := {} (* build(wrapper_init).make_cell() *) ; { _ } }} .
 	 	 refine {{ return_ [ !{wrapper_init} , {} (* tvm_hash(wrapper_init_cl) *) ] }} .
Defined.

Definition prepare_wrapper_state_init_and_addr_right {b1 b2} 
(x0: URValue XCell b1 ) 
(x1: URValue DWrapperLRecord b2 ) 
: URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) prepare_wrapper_state_init_and_addr x0 x1).    

Notation " 'prepare_wrapper_state_init_and_addr_' '(' x0 ',' x1 ')' " := 
                                         (prepare_wrapper_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.

 Definition prepare_internal_wallet_state_init_and_addr 
( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  ( uint8 ) )
 ( root_public_key :  ( uint256 ) )
 ( wallet_public_key :  ( uint256 ) ) 
( root_address :  ( XAddress ) ) 
( owner_address :  ( XMaybe XAddress ) ) 
( code :  ( XCell ) ) 
( workchain_id :  ( uint8 ) ) 
: UExpression ( StateInitLRecord * uint256 ) false . 
 	 	 refine {{ new 'wallet_data : ( DTONTokenWalletInternalLRecord ) @ "wallet_data" := 
                 [ #{name} , #{symbol} , #{decimals} , 0 , #{root_public_key} , 
                   #{wallet_public_key} , #{root_address} , #{owner_address} , 
                   {} , #{code} , #{workchain_id} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_data_cl : ( XCell ) @ "wallet_data_cl" := 
               prepare_persistent_data_ ( {} , !{wallet_data} ) ; { _ } }} . 
 	 	 refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 
              [ {} , {} , (#{code}) -> set () , (!{wallet_data_cl}) -> set () , {} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_init_cl : ( XCell ) @ "wallet_init_cl" := {}  
 	 	            (*  build ( !{ wallet_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ wallet_init } , {} (* tvm_hash ( wallet_init_cl ) *) ] }} . 
 Defined . 

 Definition prepare_internal_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  ( name : URValue ( XString ) a1 ) ( symbol : URValue ( XString ) a2 ) ( decimals : URValue ( uint8 ) a3 ) ( root_public_key : URValue ( uint256 ) a4 ) ( wallet_public_key : URValue ( uint256 ) a5 ) ( root_address : URValue ( XAddress ) a6 ) ( owner_address : URValue ( XMaybe XAddress ) a7 ) ( code : URValue ( XCell ) a8 ) ( workchain_id : URValue ( uint8 ) a9 ) : URValue ( StateInitLRecord * uint256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_internal_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_internal_wallet_state_init_and_addr_' '(' name ',' symbol ',' decimals ',' root_public_key ',' wallet_public_key ',' root_address ',' owner_address ',' code ',' workchain_id ')' " := 
 ( prepare_internal_wallet_state_init_and_addr_right 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 
 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 
 , root_public_key custom URValue at level 0 
 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 
 , owner_address custom URValue at level 0 
 , code custom URValue at level 0 
 , workchain_id custom URValue at level 0 ) : ursus_scope . 


Definition deployEmptyFlexWallet ( pubkey : ( uint256 ) ) ( tons_to_wallet : ( uint128 ) ) 
( tip3cfg : ( Tip3ConfigLRecord ) ) : UExpression XAddress true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
     refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) @ ("state_init", "std_addr") :=  
                  prepare_internal_wallet_state_init_and_addr_ 
                     ( (#{tip3cfg}) ^^  Tip3Config.name , 
                       (#{tip3cfg}) ^^  Tip3Config.symbol , 
                       (#{tip3cfg}) ^^  Tip3Config.decimals , 
                       (#{tip3cfg}) ^^  Tip3Config.root_public_key , 
                        #{pubkey} , 
                       (#{tip3cfg}) ^^  Tip3Config.root_address , 
                       (tvm.address ()) -> set () , 
                        _flex_wallet_code_ -> get_default () , 
                        _workchain_id_ ) ; { _ } }} . 
 	 	 refine {{ new 'new_wallet : ( XAddress ) @ "new_wallet" := {} ; { _ } }}.
(*  	 	 refine {{ ITONTokenWalletPtr new_wallet ( address : : make_std ( workchain_id_ , hash_addr ) ) ; { _ } }} . 
 	 	 refine {{ new_wallet.deploy_noop ( init , Grams ( tons_to_wallet . get ( ) ) ) ; { _ } }} . *) 
 	 	 refine {{ return_ !{new_wallet} }} . 
 Defined . 
  
 Definition deployEmptyFlexWallet_right { a1 a2 a3 }  ( pubkey : URValue ( uint256 ) a1 ) ( tons_to_wallet : URValue ( uint128 ) a2 ) ( tip3cfg : URValue ( Tip3ConfigLRecord ) a3 ) : URValue XAddress true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) deployEmptyFlexWallet 
 pubkey tons_to_wallet tip3cfg ) . 
 
 Notation " 'deployEmptyFlexWallet_' '(' pubkey tons_to_wallet tip3cfg ')' " := 
 ( deployEmptyFlexWallet_right 
 pubkey tons_to_wallet tip3cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , tons_to_wallet custom URValue at level 0 
 , tip3cfg custom URValue at level 0 ) : ursus_scope . 

 Definition burnWallet ( tons_value : ( uint128 ) ) ( out_pubkey : ( uint256 ) ) 
( out_internal_owner : ( address_t ) ) ( my_tip3_addr : ( address_t ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ new 'my_tip3 : ( XAddress ) @ "my_tip3" := {} ; { _ } }}.
(*  	 	 refine {{ ITONTokenWalletPtr my_tip3 ( my_tip3_addr ) ; { _ } }} . 
 	 	 refine {{ my_tip3 ( Grams ( tons_value . get ( ) ) ) . burn ( out_pubkey , out_internal_owner )   }} . 
 *) 
refine {{ {my_tip3} := !{my_tip3} }} .
Defined . 
 
 Definition burnWallet_left { R a1 a2 a3 a4 }  ( tons_value : URValue ( uint128 ) a1 ) ( out_pubkey : URValue ( uint256 ) a2 ) ( out_internal_owner : URValue ( address_t ) a3 ) ( my_tip3_addr : URValue ( address_t ) a4 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ4 ) burnWallet 
 tons_value out_pubkey out_internal_owner my_tip3_addr ) . 
 
 Notation " 'burnWallet_' '(' tons_value out_pubkey out_internal_owner my_tip3_addr ')' " := 
 ( burnWallet_left 
 tons_value out_pubkey out_internal_owner my_tip3_addr ) 
 (in custom ULValue at level 0 , tons_value custom URValue at level 0 
 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 ) : ursus_scope . 

 Definition getOwner : UExpression uint256 false . 
 	 	 refine {{ return_ _owner_ }} . 
 Defined . 
 
 Definition getOwner_right  : URValue uint256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwner 
 ) . 

 Notation " 'getOwner_' '(' ')' " := 
 ( getOwner_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope .
 
Definition getFlex : UExpression XAddress false . 
 	 	 refine {{ return_ _flex_ }} . 
 Defined . 
 
Definition getFlex_right  : URValue XAddress false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getFlex 
 ) . 
 
 Notation " 'getFlex_' '(' ')' " := 
 ( getFlex_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition hasExtWalletCode : UExpression XBool false . 
 	 	 refine {{ return_ {} (* ( ~ ( ~ _ext_wallet_code_ ) ) *) }} . 
 Defined . 
 Definition hasExtWalletCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasExtWalletCode 
 ) . 
 
 Notation " 'hasExtWalletCode_' '(' ')' " := 
 ( hasExtWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition hasFlexWalletCode : UExpression XBool false . 
 	 	 refine {{ return_ {} (* bool_t { ! ! flex_wallet_code_ } *) }} . 
 Defined . 

 Definition hasFlexWalletCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasFlexWalletCode 
 ) . 
 
 Notation " 'hasFlexWalletCode_' '(' ')' " := 
 ( hasFlexWalletCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition hasFlexWrapperCode : UExpression XBool false . 
 	 	 refine {{ return_ {} (* bool_t { ! ! flex_wrapper_code_ } *)  }} . 
 Defined . 
 
 Definition hasFlexWrapperCode_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasFlexWrapperCode 
 ) . 
 
 Notation " 'hasFlexWrapperCode_' '(' ')' " := 
 ( hasFlexWrapperCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getPayloadForDeployInternalWallet ( owner_pubkey : ( uint256 ) ) ( owner_addr : ( address_t ) ) 
( tons : ( uint128 ) ) : UExpression XCell false . 
 	 	 refine {{ return_ {} (* build ( FlexDeployWalletArgs { { owner_pubkey } , { owner_addr } , { tons } } ) . endc ( ) *) }} . 
 Defined .
 
 Definition getPayloadForDeployInternalWallet_right { a1 a2 a3 }  ( owner_pubkey : URValue ( uint256 ) a1 ) ( owner_addr : URValue ( address_t ) a2 ) ( tons : URValue ( uint128 ) a3 ) : URValue XCell ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) getPayloadForDeployInternalWallet 
 owner_pubkey owner_addr tons ) . 
 
 Notation " 'getPayloadForDeployInternalWallet_' '(' owner_pubkey owner_addr tons ')' " := 
 ( getPayloadForDeployInternalWallet_right 
 owner_pubkey owner_addr tons ) 
 (in custom URValue at level 0 , owner_pubkey custom URValue at level 0 
 , owner_addr custom URValue at level 0 
 , tons custom URValue at level 0 ) : ursus_scope . 

 Definition _fallback ( msg : ( XCell ) ) ( msg_body : ( XSlice ) ) : UExpression uint false . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 Definition _fallback_right { a1 a2 }  ( msg : URValue ( XCell ) a1 ) ( msg_body : URValue ( XSlice ) a2 ) : URValue uint ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) _fallback 
 msg msg_body ) . 
 
 Notation " '_fallback_' '(' msg msg_body ')' " := 
 ( _fallback_right 
 msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 
 , msg_body custom URValue at level 0 ) : ursus_scope . 

 Definition registerWrapper ( wrapper_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3cfg : ( Tip3ConfigLRecord ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) (* ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ IFlexPtr ( flex_ ) ( Grams ( value . get ( ) ) ) . registerWrapper ( wrapper_pubkey , tip3cfg ) *) }} . 
 Defined . 

 Definition registerTradingPair ( request_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3_root : ( XAddress ) ) ( min_amount : ( uint128 ) ) ( notify_addr : ( XAddress ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () (* ; { _ } }} . 
 	 	 refine {{ IFlexPtr ( flex_ ) ( Grams ( value . get ( ) ) ) . registerTradingPair ( request_pubkey , tip3_root , min_amount , notify_addr ) *) }} . 
 Defined . 

 Definition registerXchgPair ( request_pubkey : ( uint256 ) ) ( value : ( uint128 ) ) ( tip3_major_root : ( XAddress ) ) ( tip3_minor_root : ( XAddress ) ) ( min_amount : ( uint128 ) ) ( notify_addr : ( XAddress ) ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () (*; { _ } }} . 
 	 	 refine {{ IFlexPtr ( flex_ ) ( Grams ( value . get ( ) ) ) . registerXchgPair ( request_pubkey , tip3_major_root , tip3_minor_root , min_amount , notify_addr ) *) }} . 
 Defined . 

End FuncsInternal.
End Funcs.








