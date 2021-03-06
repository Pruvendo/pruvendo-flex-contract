Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.

Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.TvmCells.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.

Require Import FlexClient.Ledger.
Require Import FlexClient.Functions.FuncSig.
Require Import FlexClient.Functions.FuncNotations.
Require Import FlexClient.Interface.

Require Import TradingPair.ClassTypes.
Require Import PriceXchg.ClassTypes.
Require Import XchgPair.ClassTypes.
Require Import Price.ClassTypes.
Require Import Wrapper.ClassTypes.
Require Import TONTokenWallet.ClassTypes.

(*********************************************)
Require Import TradingPair.ClassTypesNotations.
Require Import XchgPair.ClassTypesNotations.
Require Import TONTokenWallet.ClassTypesNotations.
Require Import PriceXchg.ClassTypesNotations.
Require Import Price.ClassTypesNotations.
Require Import Flex.ClassTypesNotations.

(*********************************************)

Module Funcs (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) . 
Import co.
 
Module Export FuncNotationsModuleForFuncs := FuncNotations XTypesModule StateMonadModule dc. 
Module Import TradingPairClassTypesNotations := TradingPair.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule LedgerModuleForFuncSig. 
Module Import XchgPairModuleForFlexClient := XchgPair.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import TONTokenWalletModuleForFlexClient := TONTokenWallet.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import PriceXchgModuleForFlexClient := PriceXchg.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import PriceModuleForFlexClient := Price.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import FlexModuleForFlexClient := Flex.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.

Module FuncsInternal <: SpecModuleForFuncNotations.SpecSig. 
 
Module TradingPairClassTypes := TradingPair.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module XchgPairClassTypes := XchgPair.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module PriceClassTypes := Price.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module WrapperClassTypesModule := Wrapper.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module TONTokenWalletClassTypesModule := TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.
Local Open Scope ucpp_scope.

(*move somewhere*)
Existing Instance LedgerPruvendoRecord.

Definition constructor ( pubkey : uint256 ) ( trading_pair_code : cell ) ( xchg_pair_code : cell ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( (#{pubkey}) != 0 ) , error_code::zero_owner_pubkey ) ; { _ } }} . 
 	 	 refine {{ _owner_ := #{pubkey} ; { _ } }} . 
 	 	 refine {{ _trading_pair_code_ := #{ trading_pair_code } ; { _ } }} . 
 	 	 refine {{ _xchg_pair_code_ := #{ xchg_pair_code } ; { _ } }} . 
 	 	 refine {{ _workchain_id_ := (tvm_myaddr ()) ??? address.workchain_id ; { _ } }} . 
 	 	 refine {{ _flex_ := [ #{0%Z} , 0 ] ; {_} }} . 
     refine {{ return_ {} }}.
 Defined .
 
Definition constructor_left { R a1 a2 a3 }  
                            ( pubkey : URValue uint256 a1 ) 
                            ( trading_pair_code : URValue cell a2 ) 
                            ( xchg_pair_code : URValue cell a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??3 ) constructor pubkey trading_pair_code xchg_pair_code ) . 
 
 Notation " 'constructor_' '(' pubkey trading_pair_code xchg_pair_code ')' " := ( constructor_left pubkey trading_pair_code xchg_pair_code ) 
 (in custom ULValue at level 0 , pubkey custom URValue at level 0 
 , trading_pair_code custom URValue at level 0 , xchg_pair_code custom URValue at level 0 ) : ursus_scope .

Definition setFlexCfg ( tons_cfg : TonsConfigLRecord ) 
                      ( flex : address ) : UExpression PhantomType true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ _tons_cfg_ := #{ tons_cfg } ; { _ } }} . 
  refine {{ _flex_ := #{ flex }  ; {_} }} . 
  refine {{ return_ {} }}. 
Defined . 
 
Definition setFlexCfg_left { R a1 a2 }  ( tons_cfg : URValue ( TonsConfigLRecord ) a1 )
                                        ( flex : URValue address a2 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??2 ) setFlexCfg tons_cfg flex ) . 
 
Notation " 'setFlexCfg_' '(' tons_cfg flex ')' " := ( setFlexCfg_left tons_cfg flex ) 
 (in custom ULValue at level 0 , tons_cfg custom URValue at level 0 
 , flex custom URValue at level 0 ) : ursus_scope . 
 

Definition setExtWalletCode ( ext_wallet_code : cell ) : UExpression PhantomType true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ _ext_wallet_code_ ->set ( #{ ext_wallet_code } ) ; {_} }} . 
  refine {{ return_ {} }}.
Defined . 
 
Definition setExtWalletCode_left { R a1 }  ( ext_wallet_code : URValue cell a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??1 ) setExtWalletCode ext_wallet_code ) . 
 
Notation " 'setExtWalletCode_' '(' ext_wallet_code ')' " := 
 ( setExtWalletCode_left ext_wallet_code ) 
 (in custom ULValue at level 0 , ext_wallet_code custom URValue at level 0 ) : ursus_scope . 
 
Definition setFlexWalletCode ( flex_wallet_code : cell ) : UExpression PhantomType true . 
  refine {{ require_ ( ( msg_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ _flex_wallet_code_ ->set (  #{ flex_wallet_code } ) ; {_} }} . 
  refine {{ return_ {} }}. 
Defined . 

Definition setFlexWalletCode_left { R a1 } ( flex_wallet_code : URValue cell a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??1 ) setFlexWalletCode flex_wallet_code ) . 
 
Notation " 'setFlexWalletCode_' '(' flex_wallet_code ')' " := 
 ( setFlexWalletCode_left flex_wallet_code ) 
 (in custom ULValue at level 0 , flex_wallet_code custom URValue at level 0 ) : ursus_scope . 
  
Definition setFlexWrapperCode ( flex_wrapper_code : cell ) : UExpression PhantomType true . 
  refine {{ require_ ( ( msg_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ _flex_wrapper_code_  ->set (  #{ flex_wrapper_code } ) ; {_} }} . 
  refine {{ return_ {} }}. 
Defined . 
 
Definition setFlexWrapperCode_left { R a1 }  ( flex_wrapper_code : URValue cell a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??1 ) setFlexWrapperCode flex_wrapper_code ) . 
 
Notation " 'setFlexWrapperCode_' '(' flex_wrapper_code ')' " := ( setFlexWrapperCode_left flex_wrapper_code ) 
 (in custom ULValue at level 0 , flex_wrapper_code custom URValue at level 0 ) : ursus_scope .

Definition prepare_trading_pair_state_init_and_addr ( pair_data : TradingPairClassTypes.DTradingPairLRecord ) 
                                                    ( pair_code : cell  ) 
                           : UExpression (StateInitLRecord # uint256) false .
 	 	 refine {{ new 'pair_data_cl : cell @ "pair_data_cl" :=  
                       prepare_persistent_data_ ( {} , #{pair_data} ) ; { _ } }} . 
     refine {{ new 'pair_init : StateInitLRecord @ "pair_init" := 
                     [$  {} ??? { StateInit_??_split_depth } ;
                         {} ??? { StateInit_??_special } ;
                         #{pair_code}  -> set () ??? {StateInit_??_code} ;
                         ( !{pair_data_cl} ) -> set () ??? {StateInit_??_data} ;
                         {} ??? {StateInit_??_library} $]   ; { _ } }}.
 	 	 refine {{ new 'pair_init_cl : cell @ "pair_init_cl" := build ( ?? !{pair_init} ) -> make_cell () ; { _ } }} .
 	 	 refine {{ return_ [ !{pair_init} , tvm_hash (!{pair_init_cl}) ] }} .
Defined.
 
Definition prepare_trading_pair_state_init_and_addr_right {b1 b2} 
                          (x0: URValue TradingPairClassTypes.DTradingPairLRecord b1 ) 
                          (x1: URValue cell b2 ) : URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=??2) prepare_trading_pair_state_init_and_addr x0 x1).    

Notation " 'prepare_trading_pair_state_init_and_addr_' '(' x0 ',' x1 ')' " := (prepare_trading_pair_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 ,  x0 custom URValue at level 0, x1 custom URValue at level 0) : ursus_scope.

Definition deployTradingPair ( tip3_root : address ) 
                              ( deploy_min_value : uint128 ) 
                              ( deploy_value : uint128 ) 
                              ( min_trade_amount : uint128 ) 
                              ( notify_addr : address ) : UExpression address true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	refine {{ tvm_accept () ; { _ } }} .  
  refine {{ new 'pair_data : TradingPairClassTypes.DTradingPairLRecord @ "pair_data" := 
                              [$ _flex_ ??? { DTradingPair_??_flex_addr_ } ; 
                              ( #{tip3_root} ) ??? { DTradingPair_??_tip3_root_ } ;
                              [ #{0%Z}, 0]  ??? { DTradingPair_??_notify_addr_ }  $] ; {_} }}.  
  refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) @ ("state_init", "std_addr") :=
            prepare_trading_pair_state_init_and_addr_ ( !{ pair_data } , _trading_pair_code_ )  ; { _ } }} . 
  refine {{ new 'trade_pair : address @ "trade_pair" := [ _workchain_id_ , !{std_addr} ] ; { _ } }} . 
  refine ( let trade_pair_ptr := {{ ITradingPairPtr [[ !{trade_pair}  ]] }} in 
              {{ {trade_pair_ptr} with {} ??? TradingPair.deploy ( !{state_init} ) ; {_} }} ).  
  refine {{ {trade_pair_ptr} with [$ #{deploy_value} ??? { Messsage_??_value } ;
                                              FALSE  ??? { Messsage_??_bounce } ;
                                   DEFAULT_MSG_FLAGS ??? { Messsage_??_flags }  $] 
                                  ??? TradingPair.onDeploy (#{min_trade_amount} , 
                                                          #{deploy_min_value} , 
                                                          #{notify_addr} ) ; { _ } }} .
  refine {{ return_  !{trade_pair} }} . 
Defined . 

Definition deployTradingPair_right { a1 a2 a3 a4 a5 }  ( tip3_root : URValue address a1 ) ( deploy_min_value : URValue uint128 a2 ) ( deploy_value : URValue uint128 a3 ) ( min_trade_amount : URValue uint128 a4 ) ( notify_addr : URValue address a5 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??5 ) deployTradingPair 
 tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ) . 
 
Notation " 'deployTradingPair_' '(' tip3_root , deploy_min_value , deploy_value , min_trade_amount , notify_addr ')' " := 
 ( deployTradingPair_right tip3_root deploy_min_value deploy_value min_trade_amount notify_addr ) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 
 , deploy_min_value custom URValue at level 0 , deploy_value custom URValue at level 0 
 , min_trade_amount custom URValue at level 0 , notify_addr custom URValue at level 0 ) : ursus_scope . 

Definition prepare_xchg_pair_state_init_and_addr ( pair_data : XchgPairClassTypes.DXchgPairLRecord ) 
                                                ( pair_code : cell  ) 
                           : UExpression (StateInitLRecord # uint256) false .
 	 	 refine {{ new 'pair_data_cl : cell @ "pair_data_cl" :=  
                      prepare_persistent_data_ ( {} , #{pair_data} ) ; { _ } }} .
 	 	 refine {{ new 'pair_init : StateInitLRecord @ "pair_init" := 
                    [$ {} ??? { StateInit_??_split_depth } ;
                       {} ??? { StateInit_??_special } ;
                       ( #{pair_code} ) -> set () ??? {StateInit_??_code} ;
                       ( !{pair_data_cl} ) -> set () ??? {StateInit_??_data} ;
                       {} ??? {StateInit_??_library}  $]  ; { _ } }}.
 	 	 refine {{ new 'pair_init_cl : cell @ "pair_init_cl" :=  build (?? !{pair_init}) -> make_cell() ; { _ } }} .
 	 	 refine {{ return_ [ !{pair_init} , tvm_hash(!{pair_init_cl}) ] }} .
Defined.

Definition prepare_xchg_pair_state_init_and_addr_right {b1 b2} 
                      (x0: URValue XchgPairClassTypes.DXchgPairLRecord b1 ) 
                      (x1: URValue cell b2 ) 
                      : URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) := 
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=??2) prepare_xchg_pair_state_init_and_addr x0 x1).    

Notation " 'prepare_xchg_pair_state_init_and_addr_' '(' x0 ',' x1 ')' " := (prepare_xchg_pair_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , x0 custom URValue at level 0,x1 custom URValue at level 0) : ursus_scope.

Definition deployXchgPair ( tip3_major_root : address_t ) 
                          ( tip3_minor_root : address_t ) 
                          ( deploy_min_value : uint128 ) 
                          ( deploy_value : uint128 ) 
                          ( min_trade_amount : uint128 ) 
                          ( notify_addr : address_t ) 
                          : UExpression address true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} .
  refine {{ new 'pair_data : ( XchgPairClassTypes.DXchgPairLRecord ) @ "pair_data" :=  
                [$  _flex_  ??? { DXchgPair_??_flex_addr_ } ; 
                    #{ tip3_major_root }  ??? { DXchgPair_??_tip3_major_root_ } ; 
                    #{ tip3_minor_root }  ??? { DXchgPair_??_tip3_minor_root_ } ; 
                    [ #{ 0%Z } , 0 ] ??? { DXchgPair_??_notify_addr_ } $] ; { _ } }} . 
  refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) @ ("state_init", "std_addr") :=
           prepare_xchg_pair_state_init_and_addr_ ( !{ pair_data } , _xchg_pair_code_ )  ; { _ } }} .   
  refine {{ new 'trade_pair : address @ "trade_pair" := [ _workchain_id_ , !{std_addr} ] ; { _ } }} . 
  refine ( let trade_pair_ptr := {{ IXchgPairPtr [[ !{trade_pair}  ]] }} in 
           {{ {trade_pair_ptr} with {} ??? XchgPair.deploy ( !{state_init} ) ; {_} }} ).  
  refine {{ {trade_pair_ptr} with [$ #{deploy_value} ??? { Messsage_??_value } ;
                                              FALSE  ??? { Messsage_??_bounce } ;
                                   DEFAULT_MSG_FLAGS ??? { Messsage_??_flags }  $] 
                                  ??? XchgPair.onDeploy (#{min_trade_amount} , 
                                                          #{deploy_min_value} , 
                                                          #{notify_addr} ) ; { _ } }} .
  refine {{ return_ !{trade_pair} }} . 
Defined .
 
Definition deployXchgPair_right { a1 a2 a3 a4 a5 a6 }  ( tip3_major_root : URValue address_t a1 ) 
                                                       ( tip3_minor_root : URValue address_t a2 ) 
                                                       ( deploy_min_value : URValue uint128 a3 ) 
                                                       ( deploy_value : URValue uint128 a4 ) 
                                                       ( min_trade_amount : URValue uint128 a5 ) 
                                                       ( notify_addr : URValue address_t a6 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??6 ) deployXchgPair tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ) . 
 
Notation " 'deployXchgPair_' '(' tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ')' " := 
 ( deployXchgPair_right tip3_major_root tip3_minor_root deploy_min_value deploy_value min_trade_amount notify_addr ) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom URValue at level 0 , deploy_min_value custom URValue at level 0 
 , deploy_value custom URValue at level 0 , min_trade_amount custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

Definition prepare_price_state_init_and_addr ( price_data : PriceClassTypes.DPriceLRecord ) 
                                             ( price_code : cell ) 
                           : UExpression (StateInitLRecord # uint256) false .
 	 	 refine {{ new 'price_data_cl : cell @ "price_data_cl" :=  
                    prepare_persistent_data_ ( {}, #{price_data} ) ; { _ } }} .
 	 	 refine {{ new 'price_init : StateInitLRecord @ "pair_init" :=
                   [$ {} ??? { StateInit_??_split_depth } ;
                      {} ??? { StateInit_??_special } ;
                      ( #{price_code} ) -> set () ??? {StateInit_??_code} ;
                      ( !{price_data_cl} ) -> set () ??? {StateInit_??_data} ;
                      {} ??? {StateInit_??_library} $] ; { _ } }}.
 	 	 refine {{ new 'price_init_cl : cell @ "price_init_cl" := build (?? !{price_init} ) -> make_cell() ; { _ } }} .
 	 	 refine {{ return_ [ !{price_init} , tvm_hash(!{price_init_cl}) ] }} .
Defined.

Definition prepare_price_state_init_and_addr_right {b1 b2} 
          (x0: URValue PriceClassTypes.DPriceLRecord b1 ) 
          (x1: URValue cell b2 ) 
          : URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) :=
  wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=??2) prepare_price_state_init_and_addr x0 x1).

Notation " 'prepare_price_state_init_and_addr_' '(' x0 ',' x1 ')' " := 
  (prepare_price_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , x0 custom URValue at level 0, x1 custom URValue at level 0) : ursus_scope.

Definition preparePrice (price min_amount : uint128 ) (deals_limit : uint8 )
                        (tip3_code: cell  )
                        (tip3cfg: Tip3ConfigLRecord ) (price_code: cell  )
                        (notify_addr: address  ) : UExpression (StateInitLRecord # (address # uint256)) false .  
  refine {{ new 'price_data : PriceClassTypes.DPriceLRecord @ "price_data" :=
        [$ (#{price})  ??? { DPrice_??_price_ } ;
            0  ??? { DPrice_??_sells_amount_ } ;
            0  ??? { DPrice_??_buys_amount_ } ;
            _flex_  ??? { DPrice_??_flex_ } ; 
            (#{min_amount})  ??? { DPrice_??_min_amount_ } ;
            (#{deals_limit})  ??? { DPrice_??_deals_limit_ } ;
            (#{notify_addr})  ??? { DPrice_??_notify_addr_ } ;
            _workchain_id_  ??? { DPrice_??_workchain_id_ } ;
            _tons_cfg_  ??? { DPrice_??_tons_cfg_ } ;
            (#{tip3_code})  ??? { DPrice_??_tip3_code_ } ;
            (#{tip3cfg})  ??? { DPrice_??_tip3cfg_ } ;
            {}  ??? { DPrice_??_sells_ } ;
            {}  ??? { DPrice_??_buys_ } $] ; { _ } }} .
  refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) 
                @ ("state_init", "std_addr") :=
           prepare_price_state_init_and_addr_ ( !{ price_data } , #{price_code} ) ; { _ } }} .   
  refine {{ new 'addr : address @ "addr" := [ _workchain_id_, !{std_addr} ] ; { _ } }} .
  refine {{ return_ [ !{state_init} , !{addr} , !{std_addr} ] }} .
Defined.

Definition preparePrice_right {b1 b2 b3 b4 b5 b6 b7} 
                              (x0: URValue uint128 b1 ) 
                              (x1: URValue uint128 b2 ) 
                              (x2: URValue uint8 b3 ) 
                              (x3: URValue cell b4 ) 
                              (x4: URValue Tip3ConfigLRecord b5 ) 
                              (x5: URValue cell b6 ) 
                              (x6: URValue address b7)
                              : URValue (StateInitLRecord # (address # uint256)) (orb(orb(orb(orb(orb(orb b7 b6) b5) b4)b3) b2) b1) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=??7) preparePrice x0 x1 x2 x3 x4 x5 x6 ).    

Notation " 'preparePrice_' '(' x0 ',' x1 , x2 ',' x3 , x4 ',' x5 ',' x6 ')' " := 
                                         (preparePrice_right x0 x1 x2 x3 x4 x5 x6)  
   (in custom URValue at level 0 , x0 custom URValue at level 0,
    x1 custom URValue at level 0, x2 custom URValue at level 0,
    x3 custom URValue at level 0, x4 custom URValue at level 0,
    x5 custom URValue at level 0, x6 custom URValue at level 0 ) : ursus_scope.

 Definition deployPriceWithSell ( price : uint128 ) 
                                ( amount : uint128 ) 
                                ( lend_finish_time : uint32 ) 
                                ( min_amount : uint128 ) 
                                ( deals_limit : uint8 ) 
                                ( tons_value : uint128 ) 
                                ( price_code : cell ) 
                                ( my_tip3_addr : address ) 
                                ( receive_wallet : address ) 
                                ( tip3cfg : Tip3ConfigLRecord ) 
                                ( notify_addr : address ) 
                                : UExpression address true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ require_ ( _flex_wallet_code_ , error_code::missed_flex_wallet_code ) ; { _ } }} . 
 	refine {{ tvm_accept () ; { _ } }} . 
  refine {{ new ( 'state_init : StateInitLRecord , 'addr : address ,'std_addr : uint256 ) 
              @ ("state_init", "addr" , "std_addr") :=
                 preparePrice_ ( #{price} , #{min_amount} , #{deals_limit} , 
                                 _flex_wallet_code_ ->  get () , #{tip3cfg} ,
                                        #{price_code} , #{notify_addr} ) ; { _ } }} .
  refine {{ new 'price_addr : address @ "price_addr" := !{addr}; { _ } }} . 
  refine {{ new 'deploy_init_cl : cell @ "deploy_init_cl" := build ( ??  ! {state_init} ) -> endc ()  ; { _ } }} . 
 	refine {{ new 'sell_args : PriceClassTypesModule.SellArgsLRecord @ "sell_args" :=
                   [$ (#{amount}) ??? {SellArgs_??_amount} ;
                      (#{receive_wallet}) ??? { SellArgs_??_receive_wallet } $] ; { _ } }} .
  refine {{ new 'payload : cell @ "payload" := build ( ?? !{ sell_args } ) -> endc ()  ; { _ } }} . 
  refine {{ new 'my_tip3 : address @ "my_tip3" := #{ my_tip3_addr } ; { _ } }} .
  refine ( let my_tip3_ptr := {{ ITONTokenWalletPtr [[ !{my_tip3}  ]] }} in 
            {{ {my_tip3_ptr} with [$ (#{tons_value}) ??? { Messsage_??_value } ;
                                      FALSE  ??? { Messsage_??_bounce } ;
                                  DEFAULT_MSG_FLAGS ??? { Messsage_??_flags }  $] 
                            ??? .lendOwnership ( tvm_myaddr () , 0 , !{std_addr} , #{amount} , #{lend_finish_time} ,
                                              !{deploy_init_cl} , !{payload} ) ; {_} }} ).   
  refine {{ return_ !{price_addr} }} . 
Defined .

Definition deployPriceWithSell_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 }  
                                      ( price : URValue uint128 a1 ) 
                                      ( amount : URValue uint128 a2 ) 
                                      ( lend_finish_time : URValue uint32 a3 ) 
                                      ( min_amount : URValue uint128 a4 ) 
                                      ( deals_limit : URValue uint8 a5 ) 
                                      ( tons_value : URValue uint128 a6 ) 
                                      ( price_code : URValue cell a7 ) 
                                      ( my_tip3_addr : URValue address a8 ) 
                                      ( receive_wallet : URValue address a9 ) 
                                      ( tip3cfg : URValue Tip3ConfigLRecord a10 ) 
                                      ( notify_addr : URValue address a11 ) 
                                      : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??11 ) deployPriceWithSell price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ) . 
 
Notation " 'deployPriceWithSell_' '(' price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ')' " := 
 ( deployPriceWithSell_right price amount lend_finish_time min_amount deals_limit tons_value price_code my_tip3_addr receive_wallet tip3cfg notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 , lend_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 , deals_limit custom URValue at level 0 
 , tons_value custom URValue at level 0 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 , receive_wallet custom URValue at level 0 
 , tip3cfg custom URValue at level 0 , notify_addr custom URValue at level 0 ) : ursus_scope . 

Definition deployPriceWithBuy ( price : uint128 ) ( amount : uint128 ) 
                              ( order_finish_time : uint32 ) ( min_amount : uint128 ) ( deals_limit : uint8 ) 
                              ( deploy_value : uint128 ) ( price_code : cell ) ( my_tip3_addr : address_t ) 
                              ( tip3cfg : Tip3ConfigLRecord ) ( notify_addr : address_t ) : UExpression address true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ require_ ( _flex_wallet_code_ , error_code::missed_flex_wallet_code ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ new ( 'state_init : StateInitLRecord , 'addr : address ,'std_addr : uint256 ) 
              @ ("state_init", "addr" , "std_addr") :=
                 preparePrice_ ( #{price} , #{min_amount} , #{deals_limit} , 
                                _flex_wallet_code_ -> get () , #{tip3cfg} ,
                                 #{price_code} , #{notify_addr} ) ; { _ } }} . 
  refine {{ new 'price_addr : address @ "price_addr":= !{addr} ; { _ } }} . 
  refine ( let price_addr_ptr := {{ IPricePtr [[ !{price_addr}  ]] }} in 
           {{ {price_addr_ptr} with {} ??? Price.deploy ( !{state_init} ) ; {_} }} ).
  refine {{ {price_addr_ptr} with [$ (#{deploy_value}) ??? { Messsage_??_value } ;
                       DEFAULT_MSG_FLAGS ??? { Messsage_??_flags } ;
                       FALSE  ??? { Messsage_??_bounce } $]
                           ??? .buyTip3 ( #{amount} , #{my_tip3_addr} , #{order_finish_time} ) ; {_} }} .
  refine {{ return_ !{price_addr} }} . 
Defined . 
 
Definition deployPriceWithBuy_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  ( price : URValue uint128 a1 ) ( amount : URValue uint128 a2 ) ( order_finish_time : URValue uint32 a3 ) ( min_amount : URValue uint128 a4 ) ( deals_limit : URValue uint8 a5 ) ( deploy_value : URValue uint128 a6 ) ( price_code : URValue cell a7 ) ( my_tip3_addr : URValue address_t a8 ) ( tip3cfg : URValue Tip3ConfigLRecord a9 ) ( notify_addr : URValue address_t a10 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??10 ) deployPriceWithBuy price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceWithBuy_' '(' price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ')' " := 
 ( deployPriceWithBuy_right price amount order_finish_time min_amount deals_limit deploy_value price_code my_tip3_addr tip3cfg notify_addr ) 
 (in custom URValue at level 0 , price custom URValue at level 0 
 , amount custom URValue at level 0 , order_finish_time custom URValue at level 0 
 , min_amount custom URValue at level 0 , deals_limit custom URValue at level 0 
 , deploy_value custom URValue at level 0 , price_code custom URValue at level 0 
 , my_tip3_addr custom URValue at level 0 , tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 

Definition cancelSellOrder ( price : uint128 ) ( min_amount : uint128 ) 
                           ( deals_limit : uint8 ) ( value : uint128 ) ( price_code : cell ) 
                           ( tip3cfg : Tip3ConfigLRecord ) ( notify_addr : address_t ) 
                           : UExpression PhantomType true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ require_ ( _flex_wallet_code_  , error_code::missed_flex_wallet_code ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ new ( 'state_init : StateInitLRecord , 'addr : address , 'std_addr : uint256 ) 
              @ ("state_init", "addr" , "std_addr") :=
             preparePrice_ ( #{price} , #{min_amount} , #{deals_limit} , _flex_wallet_code_ -> get () , #{tip3cfg} , 
                            #{price_code} , #{notify_addr} ) ; { _ } }} . 
  refine {{ new 'price_addr : address @ "price_addr" := !{addr}  ; { _ } }} . 
  refine ( let price_addr_ptr := {{ IPricePtr [[ !{price_addr}  ]] }} in 
            {{ {price_addr_ptr} with [$ (#{value}) ??? { Messsage_??_value } ;
                       DEFAULT_MSG_FLAGS ??? { Messsage_??_flags } ;
                       FALSE  ??? { Messsage_??_bounce } $]
                           ??? Price.cancelSell () ; {_} }} ).   
  refine {{ return_ {} }}.
Defined .

Definition cancelSellOrder_left { R a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue uint128 a1 ) ( min_amount : URValue uint128 a2 ) ( deals_limit : URValue uint8 a3 ) ( value : URValue uint128 a4 ) ( price_code : URValue cell a5 ) ( tip3cfg : URValue Tip3ConfigLRecord a6 ) ( notify_addr : URValue address_t a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??7 ) cancelSellOrder price min_amount deals_limit value price_code tip3cfg notify_addr ) . 
 
 Notation " 'cancelSellOrder_' '(' price min_amount deals_limit value price_code tip3cfg notify_addr ')' " := 
 ( cancelSellOrder_left price min_amount deals_limit value price_code tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , price custom URValue at level 0 
 , min_amount custom URValue at level 0 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
Definition cancelBuyOrder ( price : uint128 ) ( min_amount : uint128 ) ( deals_limit : uint8 ) 
                          ( value : uint128 ) ( price_code : cell ) ( tip3cfg : Tip3ConfigLRecord ) 
                          ( notify_addr : address_t ) : UExpression PhantomType true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ require_ ( _flex_wallet_code_ , error_code::missed_flex_wallet_code ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ new ( 'state_init : StateInitLRecord , 'addr : address , 'std_addr : uint256 ) 
              @ ("state_init", "addr" , "std_addr") :=
                  preparePrice_ ( #{price} , #{min_amount} , #{deals_limit} , _flex_wallet_code_ -> get () , 
                             #{tip3cfg} , #{price_code} , #{notify_addr} ) ; { _ } }} . 
  refine {{ new 'price_addr : address @ "price_addr" := !{addr}; { _ } }} . 
  refine ( let price_addr_ptr := {{ IPricePtr [[ !{price_addr}  ]] }} in 
            {{ {price_addr_ptr} with [$ (#{value}) ??? { Messsage_??_value } ;
                       DEFAULT_MSG_FLAGS ??? { Messsage_??_flags } ;
                       FALSE  ??? { Messsage_??_bounce } $]
                           ??? Price.cancelBuy () ; {_}  }}  ).  
  refine {{return_ {} }}.
Defined .

Definition cancelBuyOrder_left { R a1 a2 a3 a4 a5 a6 a7 }  ( price : URValue uint128 a1 ) ( min_amount : URValue uint128 a2 ) ( deals_limit : URValue uint8 a3 ) ( value : URValue uint128 a4 ) ( price_code : URValue cell a5 ) ( tip3cfg : URValue Tip3ConfigLRecord a6 ) ( notify_addr : URValue address_t a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??7 ) cancelBuyOrder price min_amount deals_limit value price_code tip3cfg notify_addr ) . 
 
Notation " 'cancelBuyOrder_' '(' price min_amount deals_limit value price_code tip3cfg notify_addr ')' " := 
 ( cancelBuyOrder_left price min_amount deals_limit value price_code tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , price custom URValue at level 0 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 , value custom URValue at level 0  , price_code custom URValue at level 0 
 , tip3cfg custom URValue at level 0 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
Definition prepare_price_xchg_state_init_and_addr ( price_data : PriceXchgClassTypesModule.DPriceXchgLRecord ) 
                                                  ( price_code : cell ) 
                                                  : UExpression (StateInitLRecord # uint256) false .
  refine {{ new 'price_data_cl : cell @ "price_data_cl" :=  
                    prepare_persistent_data_ ( {} , #{price_data} )  ; { _ } }} .
  refine {{ new 'price_init : StateInitLRecord @ "price_init" :=
                [$
                      {} ??? { StateInit_??_split_depth } ;
                      {} ??? { StateInit_??_special } ;
                      (#{price_code} ) -> set () ??? {StateInit_??_code} ;
                      ( !{price_data_cl} ) -> set () ??? {StateInit_??_data} ;
                      {} ??? {StateInit_??_library}
                $] ; { _ } }}.
  refine {{ new 'price_init_cl : cell @ "price_init_cl" := build ( ?? !{price_init} ) -> make_cell () ; {_} }} .
  refine {{ return_ [ !{price_init} , tvm_hash ( !{price_init_cl} ) ] }} .
Defined.

Definition prepare_price_xchg_state_init_and_addr_right {b1 b2} 
                      (x0: URValue PriceXchgClassTypesModule.DPriceXchgLRecord b1 ) 
                      (x1: URValue cell b2 ) : URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=??2) prepare_price_xchg_state_init_and_addr x0 x1).    

Notation " 'prepare_price_xchg_state_init_and_addr_' '(' x0 ',' x1 ')' " := 
  (prepare_price_xchg_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , x0 custom URValue at level 0, x1 custom URValue at level 0) : ursus_scope.

Definition preparePriceXchg ( price_num : uint128 ) 
                            ( price_denum : uint128 ) ( min_amount : uint128 ) 
                            ( deals_limit : uint8 ) ( major_tip3cfg : Tip3ConfigLRecord ) 
                            ( minor_tip3cfg : Tip3ConfigLRecord ) ( price_code : cell )
                            ( notify_addr : address_t ) 
                            : UExpression ( StateInitLRecord # ( address # uint256 ) ) true .
  refine {{ new 'price_data : ( PriceXchgClassTypesModule.DPriceXchgLRecord ) @ "price_data" :=  
               [$
                 [$ (#{price_num}) ??? {RationalPrice_??_num} ; 
                    (#{price_denum}) ??? {RationalPrice_??_denum} $] 
                                     ??? { DPriceXchg_??_price_ } ;
               0 ??? { DPriceXchg_??_sells_amount_ } ;
               0 ??? { DPriceXchg_??_buys_amount_ }  ;
               _flex_ ??? { DPriceXchg_??_flex_ } ;
               (#{ min_amount }) ??? { DPriceXchg_??_min_amount_ } ;
               (#{ deals_limit }) ??? { DPriceXchg_??_deals_limit_ } ;
               (#{ notify_addr }) ??? { DPriceXchg_??_notify_addr_ } ;
               _workchain_id_ ??? { DPriceXchg_??_workchain_id_ } ;
               _tons_cfg_ ??? { DPriceXchg_??_tons_cfg_ } ;

               ( _flex_wallet_code_ -> get () ) ??? { DPriceXchg_??_tip3_code_ } ;

               (#{ major_tip3cfg }) ??? { DPriceXchg_??_major_tip3cfg_ } ; 
               (#{ minor_tip3cfg }) ??? { DPriceXchg_??_minor_tip3cfg_ } ; 
               {} ??? { DPriceXchg_??_sells_ } ; 
               {} ??? { DPriceXchg_??_buys_ }  
                 $] ; { _ } }} . 
    refine {{ new ( 'state_init : StateInitLRecord , 
                    'std_addr : uint256 ) @ ("state_init", "std_addr") :=
        prepare_price_xchg_state_init_and_addr_ ( !{price_data} , #{price_code} ) ; { _ } }} . 
    refine {{ new 'addr : address @ "addr" := [ _workchain_id_ , !{std_addr} ] ; { _ } }} . 
    refine {{ return_ [ !{ state_init } , !{ addr } , !{ std_addr } ]  }} . 
Defined .

Definition preparePriceXchg_right { a1 a2 a3 a4 a5 a6 a7 a8 }  ( price_num : URValue uint128 a1 ) 
                                                               ( price_denum : URValue uint128 a2 ) 
                                                               ( min_amount : URValue uint128 a3 ) 
                                                               ( deals_limit : URValue uint8 a4 ) 
                                                               ( major_tip3cfg : URValue Tip3ConfigLRecord a5 ) 
                                                               ( minor_tip3cfg : URValue Tip3ConfigLRecord a6 ) 
                                                               ( price_code : URValue cell a7 ) 
                                                               ( notify_addr : URValue address_t a8 ) 
                                                               : URValue ( StateInitLRecord # (address # uint256) ) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??8 ) preparePriceXchg price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ) . 
 
Notation " 'preparePriceXchg_' '(' price_num ',' price_denum ',' min_amount ',' deals_limit ',' major_tip3cfg ',' minor_tip3cfg ',' price_code ',' notify_addr ')' " := 
 ( preparePriceXchg_right price_num price_denum min_amount deals_limit major_tip3cfg minor_tip3cfg price_code notify_addr ) 
 (in custom URValue at level 0 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 , min_amount custom URValue at level 0 
 , deals_limit custom URValue at level 0 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 , price_code custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope .

Definition deployPriceXchg ( sell : boolean ) ( price_num : uint128 ) ( price_denum : uint128 ) 
                            ( amount : uint128 ) ( lend_amount : uint128 ) ( lend_finish_time : uint32 ) 
                            ( min_amount : uint128 ) ( deals_limit : uint8 ) ( tons_value : uint128 ) 
                            ( xchg_price_code : cell ) ( my_tip3_addr : address ) ( receive_wallet : address ) 
                            ( major_tip3cfg : Tip3ConfigLRecord ) ( minor_tip3cfg : Tip3ConfigLRecord ) 
                            ( notify_addr : address ) : UExpression address true . 
  refine {{ require_ ( msg_pubkey () == _owner_  , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ require_ (  _flex_wallet_code_  , error_code::missed_flex_wallet_code ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ new ( 'state_init : StateInitLRecord , 'addr : address ,'std_addr : uint256 ) 
              @ ("state_init", "addr" , "std_addr") := 
              preparePriceXchg_ ( #{price_num} , #{price_denum} , 
                                  #{min_amount} , #{deals_limit} , 
                                  #{major_tip3cfg} , #{ minor_tip3cfg} , 
                                  #{xchg_price_code} , #{notify_addr} ) ; { _ } }} . 
  refine {{ new 'price_addr : address @ "price_addr" := !{addr} ; { _ } }} . 
  refine {{ { price_addr } := !{addr} (* IPriceXchgPtr ( addr ) *) ; { _ } }} . 
  refine {{ new 'deploy_init_cl : cell @ "deploy_init_cl" := {} ; { _ } }} . 
  refine {{ { deploy_init_cl } := build ( ?? !{ state_init } ) -> endc ()  ; { _ } }} . 
  refine {{ new 'payload_args : ( PriceXchgClassTypesModule.PayloadArgsLRecord ) @ "payload_args" :=  
        [$ #{ sell }  ??? { PayloadArgs_??_sell } ; 
          #{ amount } ??? { PayloadArgs_??_amount } ; 
          #{ receive_wallet } ??? { PayloadArgs_??_receive_tip3_wallet } ;
          tvm_myaddr () ??? { PayloadArgs_??_client_addr }   $]  ; { _ } }} . 
  refine {{ new 'payload : cell @ "payload" := build ( ?? !{ payload_args } ) -> endc ()  ; { _ } }} . 
  refine {{ new 'my_tip3: address @ "my_tip3" := #{ my_tip3_addr } ; { _ } }} . 
  refine ( let my_tip3_ptr := {{ ITONTokenWalletPtr [[ !{my_tip3}  ]] }} in 
           {{ {my_tip3_ptr} with [$ (#{tons_value}) ??? { Messsage_??_value } ;
                       DEFAULT_MSG_FLAGS ??? { Messsage_??_flags } ;
                       FALSE  ??? { Messsage_??_bounce } $]
                           ??? .lendOwnership ( tvm_myaddr () , 0 , !{std_addr} , #{lend_amount} , #{lend_finish_time} , !{deploy_init_cl} , !{payload} ) ; {_} }} ).  
  refine {{ return_ !{ price_addr } }} . 
Defined .

 Definition deployPriceXchg_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 }  
                                  ( sell : URValue boolean a1 ) 
                                  ( price_num : URValue uint128 a2 ) 
                                  ( price_denum : URValue uint128 a3 ) 
                                  ( amount : URValue uint128 a4 ) 
                                  ( lend_amount : URValue uint128 a5 ) 
                                  ( lend_finish_time : URValue uint32 a6 ) 
                                  ( min_amount : URValue uint128 a7 ) 
                                  ( deals_limit : URValue uint8 a8 ) 
                                  ( tons_value : URValue uint128 a9 ) 
                                  ( xchg_price_code : URValue cell a10 ) 
                                  ( my_tip3_addr : URValue address_t a11 ) 
                                  ( receive_wallet : URValue address_t a12 ) 
                                  ( major_tip3cfg : URValue Tip3ConfigLRecord a13 ) 
                                  ( minor_tip3cfg : URValue Tip3ConfigLRecord a14 ) 
                                  ( notify_addr : URValue address_t a15 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??15 ) deployPriceXchg sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ) . 
 
 Notation " 'deployPriceXchg_' '(' sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ')' " := 
 ( deployPriceXchg_right sell price_num price_denum amount lend_amount lend_finish_time min_amount deals_limit tons_value xchg_price_code my_tip3_addr receive_wallet major_tip3cfg minor_tip3cfg notify_addr ) 
 (in custom URValue at level 0 , sell custom URValue at level 0 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 , amount custom URValue at level 0 , lend_amount custom URValue at level 0 
 , lend_finish_time custom URValue at level 0 , min_amount custom URValue at level 0 , deals_limit custom URValue at level 0 
 , tons_value custom URValue at level 0 , xchg_price_code custom URValue at level 0 , my_tip3_addr custom URValue at level 0 
 , receive_wallet custom URValue at level 0 , major_tip3cfg custom URValue at level 0 , minor_tip3cfg custom URValue at level 0 
 , notify_addr custom URValue at level 0 ) : ursus_scope . 
 
Definition cancelXchgOrder ( sell : boolean ) ( price_num : uint128 ) ( price_denum : uint128 ) 
                            ( min_amount : uint128 ) ( deals_limit : uint8 ) ( value : uint128 ) ( xchg_price_code : cell ) 
                            ( major_tip3cfg : Tip3ConfigLRecord ) ( minor_tip3cfg : Tip3ConfigLRecord ) 
                            ( notify_addr : address_t ) : UExpression PhantomType true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ require_ ( _flex_wallet_code_ , error_code::missed_flex_wallet_code ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ new ( 'state_init : StateInitLRecord , 'addr : address , 'std_addr : uint256 ) 
              @ ("state_init", "addr" , "std_addr") :=
        preparePriceXchg_ ( #{price_num} , #{price_denum} , #{min_amount} , #{deals_limit} , #{major_tip3cfg} , #{minor_tip3cfg} ,
                            #{xchg_price_code} , #{notify_addr} ) ; { _ } }} . 
  refine {{ new 'price_addr : address @ "price_addr" := !{addr} ; { _ } }} . 
  refine {{ if ( #{ sell } ) then { { _ } } else { { _ } } }} . 
  refine ( let price_addr_ptr := {{ IPriceXchgPtr [[ !{price_addr}  ]] }} in 
           {{ {price_addr_ptr} with [$ #{value} ??? { Messsage_??_value } ;
                                FALSE  ??? { Messsage_??_bounce } ;
                    DEFAULT_MSG_FLAGS ??? { Messsage_??_flags }  $] 
                    ??? PriceXchg.cancelSell () }} ).
    refine ( let price_addr_ptr := {{ IPriceXchgPtr [[ !{price_addr}  ]] }} in 
    {{ {price_addr_ptr} with [$ #{value} ??? { Messsage_??_value } ;
                                FALSE  ??? { Messsage_??_bounce } ;
                    DEFAULT_MSG_FLAGS  ??? { Messsage_??_flags }  $] 
                    ??? PriceXchg.cancelBuy () ; {_} }} ). 
    refine {{ return_ {} }} .
Defined . 
 
 Definition cancelXchgOrder_left { R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 }  
                                 ( sell : URValue boolean a1 ) 
                                 ( price_num : URValue uint128 a2 ) 
                                 ( price_denum : URValue uint128 a3 ) 
                                 ( min_amount : URValue uint128 a4 ) 
                                 ( deals_limit : URValue uint8 a5 ) 
                                 ( value : URValue uint128 a6 ) 
                                 ( xchg_price_code : URValue cell a7 ) 
                                 ( major_tip3cfg : URValue Tip3ConfigLRecord a8 ) 
                                 ( minor_tip3cfg : URValue Tip3ConfigLRecord a9 ) 
                                 ( notify_addr : URValue address_t a10 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??10 ) cancelXchgOrder sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ) . 
 
 Notation " 'cancelXchgOrder_' '(' sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ')' " := 
 ( cancelXchgOrder_left sell price_num price_denum min_amount deals_limit value xchg_price_code major_tip3cfg minor_tip3cfg notify_addr ) 
 (in custom ULValue at level 0 , sell custom URValue at level 0 , price_num custom URValue at level 0 
 , price_denum custom URValue at level 0 , min_amount custom URValue at level 0 , deals_limit custom URValue at level 0 
 , value custom URValue at level 0 , xchg_price_code custom URValue at level 0 , major_tip3cfg custom URValue at level 0 
 , minor_tip3cfg custom URValue at level 0 , notify_addr custom URValue at level 0 ) : ursus_scope . 

Definition transfer ( dest : address_t ) ( value : uint128 ) ( bounce : boolean ) : UExpression PhantomType true . 
  refine {{ require_ ( ( msg_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept () ;  { _ } }} . 
  refine {{ tvm_transfer ( #{dest} , #{value} , #{bounce} , DEFAULT_MSG_FLAGS ) ; {_} }} .
  refine {{ return_ {} }} . 
Defined . 
 
Definition transfer_left { R a1 a2 a3 } ( dest : URValue address_t a1 ) 
                                        ( value : URValue uint128 a2 ) 
                                        ( bounce : URValue boolean a3 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??3 ) transfer dest value bounce ) . 
 
Notation " 'transfer_' '(' dest value bounce ')' " := ( transfer_left dest value bounce ) 
 (in custom ULValue at level 0 , dest custom URValue at level 0 , 
 value custom URValue at level 0 , bounce custom URValue at level 0 ) : ursus_scope . 

Definition prepare_wallet_state_init_and_addr (wallet_data : TonsConfigFields )
                                              : UExpression ( StateInitLRecord # uint256 ) false .
   
(* refine {{ if ( #{TIP3_ENABLE_EXTERNAL} )
                        then  { { _:UEf } } (* wallet_replay_protection_t::init()  *)
                        else  { { _:UEf } } ; { _ } }}. *)
 	 	 refine {{ new 'wallet_data_cl : cell @ "wallet_data_cl" :=  
                       prepare_persistent_data_ ( {} , #{wallet_data} )  ; { _ } }} .
 	 	 refine {{ new 'wallet_init : StateInitLRecord @ "wallet_init" :=
                   [$
                         {} ??? { StateInit_??_split_depth } ;
                         {} ??? { StateInit_??_special } ;
                         {} ??? {StateInit_??_code} ;
                         {} ??? {StateInit_??_data} ;
                         {} ??? {StateInit_??_library}
                    $] ; { _ } }}.
 	 	 refine {{ new 'wallet_init_cl : cell @ "wallet_init_cl" := build ( ?? !{wallet_init} ) -> make_cell () ; { _ } }} .
 	 	 refine {{ return_ [ !{wallet_init} , tvm_hash(!{wallet_init_cl}) ] }} .
Defined.

Definition prepare_wallet_state_init_and_addr_right {b1} (x0: URValue TonsConfigFields b1 ) 
           : URValue (StateInitLRecord # uint256) ( orb false b1 ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=??1) prepare_wallet_state_init_and_addr x0).    

Notation " 'prepare_wallet_state_init_and_addr_' '(' x0  ')' " := (prepare_wallet_state_init_and_addr_right x0)  
   (in custom URValue at level 0 , x0 custom URValue at level 0) : ursus_scope.

Definition prepare_wrapper_state_init_and_addr ( wrapper_code : cell ) 
                                               ( wrapper_data : WrapperClassTypesModule.DWrapperLRecord ) 
                           : UExpression (StateInitLRecord # uint256) false .
 	 	 refine {{ new 'wrapper_data_cl : cell @ "wrapper_data_cl" :=  
                  prepare_persistent_data_ (  wrapper_replay_protection_t::init() , #{wrapper_data} ) ; { _ } }} .
 	 	 refine {{ new 'wrapper_init : StateInitLRecord @ "wrapper_init" :=
                   [$ {} ??? { StateInit_??_split_depth } ;
                      {} ??? { StateInit_??_special } ;
                      ( #{wrapper_code} ) -> set () ??? {StateInit_??_code} ;
                      ( !{wrapper_data_cl} ) -> set () ??? {StateInit_??_data} ;
                      {} ??? {StateInit_??_library} $] ; { _ } }}.
 	 	 refine {{ new 'wrapper_init_cl : cell @ "wrapper_init_cl" := 
                 build ( ?? !{wrapper_init} ) -> make_cell () ; { _ } }} .
 	 	 refine {{ return_ [ !{wrapper_init} ,  tvm_hash( !{wrapper_init_cl} ) ] }} .
Defined.

Definition prepare_wrapper_state_init_and_addr_right {b1 b2} 
                                                      (x0: URValue cell b1 ) 
                                                      (x1: URValue WrapperClassTypesModule.DWrapperLRecord b2 ) 
                                                      : URValue (StateInitLRecord # uint256) ( orb false (orb b2 b1) ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=??2) prepare_wrapper_state_init_and_addr x0 x1).    

Notation " 'prepare_wrapper_state_init_and_addr_' '(' x0 ',' x1 ')' " := (prepare_wrapper_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , x0 custom URValue at level 0,  x1 custom URValue at level 0) : ursus_scope.

Definition prepare_internal_wallet_state_init_and_addr ( name :  String ) ( symbol :  String )
                                                       ( decimals :  uint8 ) ( root_public_key :  uint256 )
                                                       ( wallet_public_key :  uint256 ) ( root_address :  address ) 
                                                       ( owner_address :  optional  address ) ( code :  cell ) 
                                                       ( workchain_id :  int ) : UExpression ( StateInitLRecord # uint256 ) false . 

  refine {{ new 'wallet_data : TONTokenWalletClassTypesModule.DTONTokenWalletInternalLRecord @ "wallet_data" := 
              [ #{name} , #{symbol} , #{decimals} , 0 , #{root_public_key} , 
                #{wallet_public_key} , #{root_address} , #{owner_address} , 
                {} , #{code} , #{workchain_id} ] ; { _ } }} . 
  refine {{ new 'wallet_data_cl : cell @ "wallet_data_cl" := prepare_persistent_data_ ( {} , !{wallet_data} ) ; { _ } }} . 
  refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 
          [ {} , {} , (#{code}) -> set () , (!{wallet_data_cl}) -> set () , {} ] ; { _ } }} . 
  refine {{ new 'wallet_init_cl : cell @ "wallet_init_cl" := build ( ?? !{wallet_init} ) -> make_cell () ;{_} }} .
  refine {{ return_ [ !{ wallet_init } ,  tvm_hash ( !{wallet_init_cl} )  ] }} . 
 Defined . 

Definition prepare_internal_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  
                                                              ( name : URValue String a1 ) 
                                                              ( symbol : URValue String a2 ) 
                                                              ( decimals : URValue uint8 a3 ) 
                                                              ( root_public_key : URValue uint256 a4 ) 
                                                              ( wallet_public_key : URValue uint256 a5 ) 
                                                              ( root_address : URValue address a6 ) 
                                                              ( owner_address : URValue ( optional  address ) a7 ) 
                                                              ( code : URValue cell a8 ) 
                                                              ( workchain_id : URValue int a9 ) : URValue ( StateInitLRecord # uint256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??9 ) prepare_internal_wallet_state_init_and_addr name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
Notation " 'prepare_internal_wallet_state_init_and_addr_' '(' name ',' symbol ',' decimals ',' root_public_key ',' wallet_public_key ',' root_address ',' owner_address ',' code ',' workchain_id ')' " := 
 ( prepare_internal_wallet_state_init_and_addr_right name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 , root_public_key custom URValue at level 0 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 , owner_address custom URValue at level 0 , code custom URValue at level 0 
 , workchain_id custom URValue at level 0 ) : ursus_scope . 


Definition deployEmptyFlexWallet ( pubkey : uint256 ) ( tons_to_wallet : uint128 ) 
                                 ( tip3cfg : Tip3ConfigLRecord ) : UExpression address true . 
  refine {{ require_ ( ( msg_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ require_ ( ( _flex_wallet_code_ ) , error_code::missed_flex_wallet_code ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ new ( 'init : StateInitLRecord , 'hash_addr : uint256 ) 
              @ ("init", "hash_addr") :=  
              prepare_internal_wallet_state_init_and_addr_ 
                  ( (#{tip3cfg}) ???  Tip3Config.name , 
                    (#{tip3cfg}) ???  Tip3Config.symbol , 
                    (#{tip3cfg}) ???  Tip3Config.decimals , 
                    (#{tip3cfg}) ???  Tip3Config.root_public_key , 
                    #{pubkey} , 
                    (#{tip3cfg}) ???  Tip3Config.root_address , 
                    (tvm_myaddr ()) -> set () , 
                    _flex_wallet_code_ -> get_default () , 
                    _workchain_id_ ) ; { _ } }} . 
  refine {{ new 'new_wallet : address @ "new_wallet" := [ _workchain_id_ , !{hash_addr} ] ; { _ } }}.
  refine ( let new_wallet_ptr := {{ ITONTokenWalletPtr [[ !{new_wallet}  ]] }} in 
          {{ {new_wallet_ptr} with [$ (#{tons_to_wallet}) ??? { Messsage_??_value }  $]
                                      ??? TONTokenWallet.deploy_noop ( !{init} ) ; {_} }} ).  
  refine {{ return_ !{new_wallet} }} . 
Defined . 
  
Definition deployEmptyFlexWallet_right { a1 a2 a3 }  ( pubkey : URValue uint256 a1 ) 
                                                     ( tons_to_wallet : URValue uint128 a2 ) 
                                                     ( tip3cfg : URValue Tip3ConfigLRecord a3 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??3 ) deployEmptyFlexWallet pubkey tons_to_wallet tip3cfg ) . 
 
Notation " 'deployEmptyFlexWallet_' '(' pubkey tons_to_wallet tip3cfg ')' " := 
 ( deployEmptyFlexWallet_right pubkey tons_to_wallet tip3cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , tons_to_wallet custom URValue at level 0 , tip3cfg custom URValue at level 0 ) : ursus_scope . 

Definition burnWallet ( tons_value : uint128 ) ( out_pubkey : uint256 )  
                       ( out_internal_owner : address_t ) ( my_tip3_addr : address_t ) : UExpression PhantomType true . 
  refine {{ require_ ( ( msg_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine {{ new 'my_tip3 : address @ "my_tip3" := #{my_tip3_addr} ; { _ } }}.
  refine ( let my_tip3_ptr := {{ ITONTokenWalletPtr [[ !{my_tip3}  ]] }} in 
          {{ {my_tip3_ptr} with [$ (#{tons_value}) ??? { Messsage_??_value }  $]
                                      ??? .burn ( #{out_pubkey} , #{out_internal_owner} ) ; {_} }} ).  
  refine {{ {my_tip3} := !{my_tip3} ; {_} }} .
  refine {{ return_ {} }} .
Defined . 
 
 Definition burnWallet_left { R a1 a2 a3 a4 } ( tons_value : URValue uint128 a1 ) 
                                              ( out_pubkey : URValue uint256 a2 ) 
                                              ( out_internal_owner : URValue address_t a3 ) 
                                              ( my_tip3_addr : URValue address_t a4 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= ??4 ) burnWallet tons_value out_pubkey out_internal_owner my_tip3_addr ) . 
 
Notation " 'burnWallet_' '(' tons_value out_pubkey out_internal_owner my_tip3_addr ')' " := 
 ( burnWallet_left tons_value out_pubkey out_internal_owner my_tip3_addr ) 
 (in custom ULValue at level 0 , tons_value custom URValue at level 0 , out_pubkey custom URValue at level 0 
 , out_internal_owner custom URValue at level 0 , my_tip3_addr custom URValue at level 0 ) : ursus_scope . 

Definition getOwner : UExpression uint256 false . 
    refine {{ return_ _owner_ }} . 
Defined . 
 
Definition getOwner_right  : URValue uint256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??0 ) getOwner ) . 

Notation " 'getOwner_' '(' ')' " := ( getOwner_right ) 
 (in custom URValue at level 0 ) : ursus_scope .
 
Definition getFlex : UExpression address false . 
  refine {{ return_ _flex_ }} . 
Defined . 
 
Definition getFlex_right  : URValue address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??0 ) getFlex ) . 
 
Notation " 'getFlex_' '(' ')' " := ( getFlex_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition hasExtWalletCode : UExpression boolean false . 
  refine {{ return_  ? _ext_wallet_code_ }} . 
Defined . 

Definition hasExtWalletCode_right  : URValue boolean false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??0 ) hasExtWalletCode ) . 
 
Notation " 'hasExtWalletCode_' '(' ')' " := ( hasExtWalletCode_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition hasFlexWalletCode : UExpression boolean false . 
  refine {{ return_ ? _flex_wallet_code_ }} . 
Defined . 

Definition hasFlexWalletCode_right  : URValue boolean false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??0 ) hasFlexWalletCode ) . 
 
Notation " 'hasFlexWalletCode_' '(' ')' " := ( hasFlexWalletCode_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition hasFlexWrapperCode : UExpression boolean false . 
  refine {{ return_ ? _flex_wrapper_code_  }} . 
Defined . 
 
Definition hasFlexWrapperCode_right  : URValue boolean false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??0 ) hasFlexWrapperCode ) . 
 
Notation " 'hasFlexWrapperCode_' '(' ')' " := ( hasFlexWrapperCode_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getPayloadForDeployInternalWallet ( owner_pubkey : uint256 ) 
                                             ( owner_addr : address_t ) 
                                             ( tons : uint128 ) : UExpression cell false . 
  refine {{ return_ ( build (?? [ #{ owner_pubkey } , #{ owner_addr } , #{ tons } ] ) -> endc () ) }} .  
Defined .
 
 Definition getPayloadForDeployInternalWallet_right { a1 a2 a3 }  ( owner_pubkey : URValue uint256 a1 ) 
                                                    ( owner_addr : URValue address_t a2 ) 
                                                    ( tons : URValue uint128 a3 ) : URValue cell ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??3 ) getPayloadForDeployInternalWallet owner_pubkey owner_addr tons ) . 
 
Notation " 'getPayloadForDeployInternalWallet_' '(' owner_pubkey owner_addr tons ')' " := 
 ( getPayloadForDeployInternalWallet_right owner_pubkey owner_addr tons ) 
 (in custom URValue at level 0 , owner_pubkey custom URValue at level 0 
 , owner_addr custom URValue at level 0 , tons custom URValue at level 0 ) : ursus_scope . 

Definition _fallback ( msg : cell ) ( msg_body : slice ) : UExpression uint false . 
  refine {{ return_ 0 }} . 
Defined . 
 
Definition _fallback_right { a1 a2 }  ( msg : URValue cell a1 ) ( msg_body : URValue ( slice ) a2 ) : URValue uint ( orb a2 a1 ) := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= ??2 ) _fallback msg msg_body ) . 
 
 Notation " '_fallback_' '(' msg msg_body ')' " := ( _fallback_right msg msg_body ) 
 (in custom URValue at level 0 , msg custom URValue at level 0 , msg_body custom URValue at level 0 ) : ursus_scope . 

Definition registerWrapper ( wrapper_pubkey : uint256 ) 
                           ( value : uint128 ) 
                           ( tip3cfg : Tip3ConfigLRecord ) : UExpression PhantomType true . 
  refine {{ require_ ( msg_pubkey () == _owner_ , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept ()  ; { _ }  }} . 
  refine ( let flex__ptr := {{ IFlexPtr [[  _flex_   ]] }} in 
           {{ {flex__ptr} with [$ #{value} ??? { Messsage_??_value }  $] 
                              ??? Flex.registerWrapper ( #{wrapper_pubkey} , #{tip3cfg} ) ; {_} }} ) .
  refine {{ return_ {} }} .
Defined . 

Definition registerTradingPair ( request_pubkey : uint256 ) 
                                ( value : uint128 ) 
                                ( tip3_root : address ) 
                                ( min_amount : uint128 ) 
                                ( notify_addr : address ) : UExpression PhantomType true . 
  refine {{ require_ ( msg_pubkey () == _owner_  , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} . 
  refine ( let flex__ptr := {{ IFlexPtr [[  _flex_   ]] }} in 
           {{ {flex__ptr} with [$ #{value} ??? { Messsage_??_value }  $] 
              ??? Flex.registerTradingPair ( #{request_pubkey} , #{tip3_root} , #{min_amount}, #{notify_addr}) ; {_} }} ).  
  refine {{ return_ {} }} .
Defined . 

Definition registerXchgPair ( request_pubkey : uint256 ) 
                             ( value : uint128 ) 
                             ( tip3_major_root : address ) 
                             ( tip3_minor_root : address ) 
                             ( min_amount : uint128 ) ( notify_addr : address ) : UExpression PhantomType true . 
  refine {{ require_ ( ( msg_pubkey () == _owner_ ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} .        
  refine ( let flex__ptr := {{ IFlexPtr [[  _flex_   ]] }} in 
           {{ {flex__ptr} with [$ #{value} ??? { Messsage_??_value }  $] 
              ??? Flex.registerXchgPair ( #{request_pubkey} , #{tip3_major_root} , #{tip3_minor_root} , 
                                        #{min_amount} , #{notify_addr}) ; {_} }} ).  
  refine {{ return_ {} }} .
Defined . 

End FuncsInternal.
End Funcs.
