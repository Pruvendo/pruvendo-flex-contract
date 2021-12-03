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
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import UrsusTVM.Cpp.TvmCells.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.

(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Flex.Ledger.
Require Import Flex.ClassTypesNotations.
Require Import Flex.ClassTypes.
Require Import Flex.Functions.FuncSig.
Require Import Flex.Functions.FuncNotations.

(* Require Flex.Interface. *)

Require Import TradingPair.ClassTypes.
Require Import XchgPair.ClassTypes.
Require Import Wrapper.ClassTypes.
Require Import TONTokenWallet.ClassTypes.

Require Import XchgPair.ClassTypesNotations.
Require Import TradingPair.ClassTypesNotations.
Require Import TONTokenWallet.ClassTypesNotations.
Require Import Wrapper.ClassTypesNotations.

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.

Module Funcs (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .
Import co.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 

Module Import XchgPairModuleForFlex := XchgPair.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import TradingPairModuleForFlex := TradingPair.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import TONTokenWalletModuleForFlex := TONTokenWallet.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import WrapperModuleForFlex := Wrapper.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.

Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.
Existing Instance LedgerPruvendoRecord.

Definition constructor ( deployer_pubkey :  uint256 ) ( ownership_description : String ) ( owner_address :  optional address ) 
                       ( tons_cfg :  TonsConfigLRecord ) ( deals_limit :  uint8 ) ( listing_cfg :  ListingConfigLRecord ) 
                       : UExpression PhantomType true . 
 	 	 refine {{ _deployer_pubkey_ := #{ deployer_pubkey } ; { _ } }} . 
 	 	 refine {{ _ownership_description_ := #{ ownership_description } ; { _ } }} . 
 	 	 refine {{ _owner_address_ := #{ owner_address } ; { _ } }} . 
 	 	 refine {{ _deals_limit_ := #{ deals_limit } ; { _ } }} . 
 	 	 refine {{ _tons_cfg_ := #{ tons_cfg } ; { _ } }} . 
 	 	 refine {{ _listing_cfg_ := #{ listing_cfg } ; { _ } }} . 
 	 	 refine {{ _workchain_id_ := (tvm_myaddr ()) ↑ address.workchain_id ; { _ } }} . 
 	 	 refine {{ require_ ( (((#{listing_cfg}) ↑ ListingConfig.register_pair_cost) >= 
       ( (#{listing_cfg}) ↑ ListingConfig.reject_pair_cost )
                          + ( (#{listing_cfg}) ↑ ListingConfig.register_return_value ) ) , error_code::costs_inconsistency ) ; { _ } }} . 
refine {{ return_ {} }} .
Defined . 

Print constructor .

Definition constructor_left { R a1 a2 a3 a4 a5 a6 }  ( deployer_pubkey : URValue uint256 a1 ) 
                                                      ( ownership_description : URValue ( String ) a2 ) 
                                                      ( owner_address : URValue ( optional address ) a3 ) 
                                                      ( tons_cfg : URValue ( TonsConfigLRecord ) a4 ) 
                                                      ( deals_limit : URValue uint8 a5 ) 
                                                      ( listing_cfg : URValue ListingConfigLRecord a6 ) 
                                                      : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ6 ) constructor deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg ) . 
 
 Notation " 'constructor_' '(' deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg ')' " := 
 ( constructor_left deployer_pubkey ownership_description owner_address tons_cfg deals_limit listing_cfg ) 
 (in custom ULValue at level 0 , deployer_pubkey custom URValue at level 0 , ownership_description custom URValue at level 0 , 
  owner_address custom URValue at level 0 , tons_cfg custom URValue at level 0 , deals_limit custom URValue at level 0 ,
  listing_cfg custom URValue at level 0 ) : ursus_scope . 
 
(*   void setSpecificCode(uint8 type, cell code) {
    switch (static_cast<code_type>(type.get())) {
    case code_type::trade_pair_code: setPairCode(code); return;
    case code_type::xchg_pair_code: setXchgPairCode(code); return;
    case code_type::wrapper_code: setWrapperCode(code); return;
    case code_type::ext_wallet_code: setExtWalletCode(code); return;
    case code_type::flex_wallet_code: setFlexWalletCode(code); return;
    case code_type::price_code: setPriceCode(code); return;
    case code_type::xchg_price_code: setXchgPriceCode(code); return;
    }
  }
 *)

Definition setSpecificCode ( type :  uint8 ) ( code :  cell ) : UExpression PhantomType false .
   (* refine {{ switch_ ( {} ) with { { _ } ;; { _ } ;; { _ } ;; { _ } ;; { _ } ;; { _ } ;; { _ } } ) }}.
  refine {{ case_ trade_pair_code => setPairCode(code) ; return_ {} }}.
  refine {{ case_ xchg_pair_code => setPairCode(code) ; return_ {} }}.
  refine {{ case_ wrapper_code => setPairCode(code) ; return_ {} }}.
  refine {{ case_ ext_wallet_code => setPairCode(code) ; return_ {} }}.
  refine {{ case_ flex_wallet_code => setPairCode(code) ; return_ {} }}.
  refine {{ case_ price_code => setPairCode(code) ; return_ {} }}.
  refine {{ case_ xchg_price_code => setPairCode(code) ; return_ {} }}. *)
 	 	 refine {{ return_ {} }} .
Defined.

Definition setPairCode ( code :  cell ) : UExpression PhantomType true . 
  refine {{ require_ ( ( ~ _pair_code_ ) , error_code::cant_override_code ) ; { _ } }} . 
  refine {{ require_ ( ( msg_pubkey () == _deployer_pubkey_ ) ,  error_code::sender_is_not_deployer  ) ; { _ } }} . 
  refine {{ tvm_accept () ; { _ } }} .   
(*   refine {{ require_ ( ( (#{code}) -> ctos () -> sref () == #{2} ) ,  error_code::unexpected_refs_count_in_code  ) ; { _ } }} . *)
  refine {{ _pair_code_ := {} (* builder ( ) . stslice ( #{code} -> to_slice () ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) ; {_} }} . 
 refine {{ return_ {} }}.
Defined . 
 
Definition setXchgPairCode ( code :  cell ) : UExpression PhantomType true . 
    refine {{ require_ ( ( ~ _xchg_pair_code_ ) , error_code::cant_override_code ) ; { _ } }} . 
    refine {{ require_ ( ( msg_pubkey () == _deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
    refine {{ tvm_accept () ; { _ } }} . 
    (* refine {{ require_ ( ( (#{code}) -> to_slice () -> refs () == #{2} ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} .  *)
    refine {{ _xchg_pair_code_ := {}(* builder ( ) . stslice ( #{code} -> to_slice () ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) ; {_} }} . 
    refine {{ return_ {} }}.
Defined . 
 
Definition setWrapperCode ( code :  cell ) : UExpression PhantomType true . 
    refine {{ require_ ( ( ! _wrapper_code_ ) , error_code::cant_override_code ) ; { _ } }} . 
    refine {{ require_ ( ( msg_pubkey () == _deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
    refine {{ tvm_accept () ; { _ } }} . 
   (*  refine {{ require_ ( ( (#{code}) -> to_slice () -> refs () == #{2} ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} .  *)
    refine {{ _wrapper_code_ := {} (* builder ( ) . stslice ( #{code} -> to_slice () ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) ; {_} }} . 
    refine {{ return_ {} }}.
Defined . 


 Definition setPriceCode ( code :  cell ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _price_code_ ) ,  error_code::cant_override_code  ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey () == _deployer_pubkey_ ) ,  error_code::sender_is_not_deployer  ) ; { _ } }} . 
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ _price_code_ -> set ( (#{code}) ) ; {_} }} . 
  refine {{ return_ {} }}. 
 Defined . 
 
 Definition setXchgPriceCode ( code :  cell ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _xchg_price_code_ ) ,  error_code::cant_override_code  ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey () == _deployer_pubkey_ ) ,  error_code::sender_is_not_deployer  ) ; { _ } }} . 
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ _xchg_price_code_ -> set ((#{code})) ; {_} }} . 
  refine {{ return_ {} }}. 
 Defined .  
 
 Definition setExtWalletCode ( code :  cell ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _ext_wallet_code_ ) ,   error_code::cant_override_code  ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey () == _deployer_pubkey_ ) ,  error_code::sender_is_not_deployer  ) ; { _ } }} . 
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ _ext_wallet_code_ -> set ( (#{code}) ) ; {_} }} . 
  refine {{ return_ {} }}. 
 Defined . 
 
 Definition setFlexWalletCode ( code :  cell ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _flex_wallet_code_ ) ,  error_code::cant_override_code  ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg_pubkey () == _deployer_pubkey_ ) ,   error_code::sender_is_not_deployer  ) ; { _ } }} . 
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ _flex_wallet_code_ -> set ( (#{code}) ) ; {_} }} . 
  refine {{ return_ {} }}. 
 Defined . 

Definition check_owner : UExpression PhantomType true . 
 	 	 refine {{ new 'internal_ownership : boolean @ "internal_ownership" :=  ~~ ? _owner_address_ ; { _ } }} . 
  	 refine {{ if ( #{Internal} ) then { { _: UExpression PhantomType true } } else { { _: UExpression PhantomType true } } ; { _ } }} . 
 	 	   refine {{ require_ ( !{ internal_ownership } && ( int_sender () == ( _owner_address_ ->get_default () ) ) ,  error_code::sender_is_not_my_owner )  }} . 
 	 	   refine {{ require_ ( ( ~ !{ internal_ownership } && ( msg_pubkey () == _deployer_pubkey_ ) ) ,  error_code::sender_is_not_my_owner )  }} . 
     refine {{ return_ {} }} .
 Defined . 

Definition check_owner_left { R }  : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_owner ) . 
 
Notation " 'check_owner_' '(' ')' " :=  ( check_owner_left ) (in custom ULValue at level 0 ) : ursus_scope . 

Definition transfer ( tto : address ) ( tons :  uint128 ) : UExpression PhantomType true . 
  	 refine {{ check_owner_ ( ) ; { _ } }} .
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ tvm_transfer ( #{tto} , #{tons}  , TRUE , DEFAULT_MSG_FLAGS ) ; {_} }} . 
refine {{ return_ {} }} .
Defined . 

Definition prepare_trading_pair_state_init_and_addr 
( pair_data :  TradingPairClassTypesModule.DTradingPairLRecord ) 
( pair_code :  cell ) 
: UExpression ( StateInitLRecord # uint256 )  false . 
 	 	refine {{ new 'pair_data_cl : cell @ "pair_data_cl" := 
                       prepare_persistent_data_ ( {} , #{pair_data} ) ; { _ } }} . 
 	 	 refine {{ new 'pair_init : StateInitLRecord @ "pair_init" :=  
                 [$ {}  ⇒ {StateInit_ι_split_depth} ;
                    {}  ⇒ {StateInit_ι_special} ; 
           ( (#{pair_code}) -> set () ) ⇒ {StateInit_ι_code} ; 
           ( (!{pair_data_cl}) -> set () ) ⇒ {StateInit_ι_data} ; 
            {}  ⇒ {StateInit_ι_library} $] ; { _ } }} .

 	 	 refine {{ new 'pair_init_cl : cell @ "pair_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ { pair_init_cl } := build ( σ (!{pair_init}) ) -> make_cell ()  ; { _ } }} . 
	 	 refine {{ return_ [ !{ pair_init } , tvm_hash ( !{pair_init_cl} ) ] }} .
 Defined .  
 
 Definition prepare_trading_pair_state_init_and_addr_right { a1 a2 }  
                  ( pair_data : URValue TradingPairClassTypesModule.DTradingPairLRecord a1 )
                  ( pair_code : URValue cell a2 ) : URValue ( StateInitLRecord * uint256 )  ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_trading_pair_state_init_and_addr pair_data pair_code ) . 
 
Notation " 'prepare_trading_pair_state_init_and_addr_' '(' pair_data ',' pair_code ')' " := 
                  ( prepare_trading_pair_state_init_and_addr_right pair_data pair_code ) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 , pair_code custom URValue at level 0 ) : ursus_scope . 
  
Definition prepare_trading_pair ( flex : address ) 
                                 ( tip3_root : address ) 
                                 ( pair_code : cell ) : UExpression ( StateInitLRecord # uint256 )  false . 
 	 	 refine {{ new 'pair_data : TradingPairClassTypesModule.DTradingPairLRecord  @ "pair_data" :=  
               	 	 [$ tvm_myaddr () ⇒ { DTradingPair_ι_flex_addr_ } ; 
                      #{tip3_root} ⇒ { DTradingPair_ι_tip3_root_ } ; 
                      0 ⇒ { DTradingPair_ι_min_amount_ } ; 
                      [ #{0%Z}, 0 ]  ⇒ { DTradingPair_ι_notify_addr_  }  $] ; { _ } }} . 
 	 	 refine {{ return_ ( prepare_trading_pair_state_init_and_addr_ ( !{ pair_data } , #{pair_code} ) ) }} . 
Defined .
 
Definition prepare_trading_pair_right { a1 a2 a3 }  ( flex : URValue address a1 ) 
                                                     ( tip3_root : URValue address a2 ) 
                                                     ( pair_code : URValue cell a3 ) : URValue ( StateInitLRecord * uint256 )  ( orb ( orb a3 a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) prepare_trading_pair flex tip3_root pair_code ) . 
 
 Notation " 'prepare_trading_pair_' '(' flex ',' tip3_root ',' pair_code ')' " := ( prepare_trading_pair_right flex tip3_root pair_code ) 
 (in custom URValue at level 0 , flex custom URValue at level 0 , tip3_root custom URValue at level 0 , pair_code custom URValue at level 0 ) : ursus_scope . 

 Definition registerTradingPair ( pubkey :  uint256 ) 
                                ( tip3_root : address ) 
                                ( min_amount :  uint128  ) 
                                ( notify_addr : address ) : UExpression address true . 
 	 	 refine {{ require_ ( ( int_value () > ( _listing_cfg_ ↑  ListingConfig.register_pair_cost) ) ,  error_code::not_enough_funds  ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( ~ (_trading_pair_listing_requests_ ->contains ( #{pubkey} )) ) ,  
               error_code::trading_pair_with_such_pubkey_already_requested  ) ; { _ } }} . 
 
  	 refine {{ _trading_pair_listing_requests_ -> set_at 
               ( #{pubkey} ,  [ int_sender () , 
                                int_value ()  - 
                                  _listing_cfg_ ↑  ListingConfig.register_return_value , 
                                #{tip3_root} , 
                                #{min_amount} , 
                                #{notify_addr}  ] ) ; { _ } }} . 
  	 	 refine {{ set_int_return_value ( _listing_cfg_ ↑ ListingConfig.register_return_value ) ; { _ } }} .  
      refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) @ ("state_init", "std_addr") :=
                prepare_trading_pair_ ( tvm_myaddr () , #{tip3_root} , _pair_code_ -> get () ) ; { _ } }} .
 	 	 refine {{ return_ [ _workchain_id_ , !{std_addr} ]  }} . 
 Defined .
 
Definition approveTradingPairImpl ( pubkey : uint256 )
                                  ( trading_pair_listing_requests : trading_pairs_map ) 
                                  ( pair_code : cell ) 
                                  ( workchain_id : int ) 
                                  ( listing_cfg : ListingConfigLRecord ) : UExpression ( address * (trading_pairs_map ) ) true . 
 	 	 refine {{ new 'opt_req_info : optional TradingPairListingRequestLRecord @ "opt_req_info" := 
                (#{trading_pair_listing_requests}) -> extract ( #{pubkey} ) ; {_} }} .

  
 	 	 refine {{ require_ ( !{opt_req_info}  ,  error_code::trading_pair_not_requested  ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : TradingPairListingRequestLRecord @ "req_info" := 
                              (!{opt_req_info}) -> get () ; { _ } }} . 
 	 	 refine {{ new ( 'state_init : StateInitLRecord, 'std_addr : uint256 ) @ ("state_init", "std_addr") := 
                 prepare_trading_pair_ ( tvm_myaddr () , !{req_info} ↑ TradingPairListingRequest.tip3_root , #{pair_code} ) ; { _ } }} . 
 	 	 refine {{ new 'trade_pair : address @ "trade_pair" := 
                               [ #{ workchain_id } , !{std_addr} ] ; { _ } }} . 
refine ( let trade_pair_ptr := {{ ITradingPairPtr [[ !{trade_pair}  ]] }} in 
              {{ {trade_pair_ptr} with {} ⤳ TradingPair.deploy ( !{state_init} ) ; {_} }} ).  

      refine ( let trade_pair_ptr := {{ ITradingPairPtr [[ !{trade_pair}  ]] }} in 
        {{ {trade_pair_ptr} with [$ (#{listing_cfg}) ↑ ListingConfig.pair_deploy_value ⇒ { Messsage_ι_value } ;
                                     DEFAULT_MSG_FLAGS ⇒ { Messsage_ι_flags }  $] 
                        ⤳ TradingPair.onDeploy (!{req_info} ↑ TradingPairListingRequest.min_amount , 
                                                (#{listing_cfg}) ↑ ListingConfig.pair_keep_balance , 
                                                !{req_info} ↑ TradingPairListingRequest.notify_addr ) ; { _ } }} ).
 	 	 refine {{ new 'remaining_funds : uint128 @ "remaining_funds" :=   
 	 	   !{req_info} ↑ TradingPairListingRequest.client_funds - 
            (#{listing_cfg}) ↑ ListingConfig.register_pair_cost ; { _ } }} . 
refine {{ IListingAnswerPtr [[  !{req_info} ↑ TradingPairListingRequest.client_addr ]]
          with [$ !{remaining_funds} ⇒ { Messsage_ι_value } $]  ⤳ .onTradingPairApproved ( #{pubkey} , !{trade_pair} ) ; {_} }}. 

 	 	 refine {{ return_ [ !{trade_pair} , #{trading_pair_listing_requests} ] }} . 
Defined .

Definition approveTradingPairImpl_right { a1 a2 a3 a4 a5 } ( pubkey : URValue uint256 a1 ) 
                                                           ( trading_pair_listing_requests : URValue trading_pairs_map a2 ) 
                                                           ( pair_code : URValue cell a3 )
                                                           ( workchain_id : URValue int a4 ) 
                                                           ( listing_cfg : URValue ListingConfigLRecord a5 ) 
                                                           : URValue ( address # trading_pairs_map )  true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) approveTradingPairImpl pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg ) . 
 
Notation " 'approveTradingPairImpl_' '(' pubkey , trading_pair_listing_requests , pair_code , workchain_id , listing_cfg ')' " := 
 ( approveTradingPairImpl_right pubkey trading_pair_listing_requests pair_code workchain_id listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 , trading_pair_listing_requests custom URValue at level 0 , 
  pair_code custom URValue at level 0 , workchain_id custom URValue at level 0 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

 Definition approveTradingPair ( pubkey :  uint256 ) : UExpression address true . 
  	 refine {{ check_owner_ ( ) ; { _ } }} .
 	 	 refine {{ tvm_accept () ; { _ } }} .
 	 	 refine {{ new ( 'trade_pair : address , 'new_trading_pair_listing_requests : trading_pairs_map ) 
                    @ ("trade_pair", "new_trading_pair_listing_requests")  := 
            approveTradingPairImpl_ ( #{pubkey} , _trading_pair_listing_requests_ , _pair_code_ -> get () , _workchain_id_ , _listing_cfg_ ) ; { _ } }} . 
 	 	 refine {{ _trading_pair_listing_requests_ := !{new_trading_pair_listing_requests} ; { _ } }} . 
 	 	 refine {{ if ( #{Internal} ) then { { _ } } else { exit_ {} } ; { _ } }} . 
 	 	 refine {{ new 'value_gr : uint @ "value_gr" := int_value ()  ; { _ } }} . 
  	 	 refine {{ tvm_rawreserve ( tvm_balance () - !{value_gr} ,  rawreserve_flag::up_to  )  (* ; { _ } *) }} .
 	 	 refine {{ set_int_return_flag ( #{SEND_ALL_GAS} ) ; {_} }} .
 	 refine {{ return_ !{ trade_pair } }} . 
Defined .
 
Definition approveTradingPair_right { a1 }  ( pubkey : URValue uint256 a1 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) approveTradingPair pubkey ) . 
 
Notation " 'approveTradingPair_' '(' pubkey ')' " :=  ( approveTradingPair_right  pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

Definition rejectTradingPairImpl ( pubkey : uint256 ) 
                                 ( trading_pair_listing_requests : trading_pairs_map ) 
                                 ( listing_cfg :  ListingConfigLRecord ) : UExpression (trading_pairs_map ) true . 
 	 	 refine {{ new 'opt_req_info : optional TradingPairListingRequestLRecord @ "opt_req_info" := 
                 (#{trading_pair_listing_requests}) -> extract ( #{pubkey} ) ; { _ } }} .  
 	 	 refine {{ require_ ( !{ opt_req_info }  ,  error_code::trading_pair_not_requested  ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( TradingPairListingRequestLRecord ) @ "req_info" := 
                    (!{opt_req_info}) -> get ()  ; { _ } }} . 
 	 	 refine {{ new 'remaining_funds : uint128 @ "remaining_funds" := 
            ( (!{req_info}) ↑ TradingPairListingRequest.client_funds ) - ( (#{listing_cfg}) ↑ ListingConfig.reject_pair_cost ) ; { _ } }} . 
refine {{ IListingAnswerPtr [[  !{req_info} ↑ TradingPairListingRequest.client_addr ]]
          with [$ !{remaining_funds} ⇒ { Messsage_ι_value } $]  ⤳ .onTradingPairRejected ( #{pubkey} ) ; {_} }}.                                                               
 	 	 refine {{ return_ #{trading_pair_listing_requests} }} . 
Defined . 

Definition rejectTradingPairImpl_right { a1 a2 a3 }  ( pubkey : URValue  uint256  a1 )
                                                     ( trading_pair_listing_requests : URValue trading_pairs_map  a2 ) 
                                                     ( listing_cfg : URValue ListingConfigLRecord a3 ): URValue trading_pairs_map true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) rejectTradingPairImpl pubkey trading_pair_listing_requests listing_cfg ) . 

 Notation " 'rejectTradingPairImpl_' '(' pubkey , trading_pair_listing_requests , listing_cfg ')' " := 
 ( rejectTradingPairImpl_right pubkey trading_pair_listing_requests listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 , trading_pair_listing_requests custom URValue at level 0 , listing_cfg custom URValue at level 0 ) : ursus_scope .

 Definition rejectTradingPair ( pubkey :  uint256 ) : UExpression XBool true . 
  	refine {{ check_owner_ ( ) ; { _ } }} .
 	 	refine {{ _trading_pair_listing_requests_ := 
              rejectTradingPairImpl_ ( #{pubkey} , _trading_pair_listing_requests_ , _listing_cfg_ ) ; { _ } }} . 
 	 	refine {{ new 'value_gr : uint @ "value_gr" := int_value () ; { _ } }} . 
  	refine {{ tvm_rawreserve ( tvm_balance () - !{value_gr} , rawreserve_flag::up_to  ) ; { _ } }} .
 	 	refine {{ if ( #{Internal} ) then { { _ } } else { return_ {} } ; { _ } }} . 
 	  refine {{ {value_gr} := int_value () ; { _ } }} .  	 	 	 
    refine {{ set_int_return_flag ( #{SEND_ALL_GAS} ) }} .
 	 refine {{ return_ TRUE }} .
Defined . 

Definition rejectTradingPair_right { a1 }  ( pubkey : URValue uint256 a1 ) : URValue XBool true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) rejectTradingPair pubkey ) . 
 
Notation " 'rejectTradingPair_' '(' pubkey ')' " := ( rejectTradingPair_right pubkey ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 ) : ursus_scope . 

Definition prepare_xchg_pair_state_init_and_addr ( pair_data :  XchgPairClassTypesModule.DXchgPairLRecord ) 
                                                 ( pair_code :  cell ) : UExpression ( StateInitLRecord # uint256 )  false . 
  refine {{ new 'pair_data_cl : cell @ "pair_data_cl" := 
                  prepare_persistent_data_ ( {} , #{pair_data} )   ; { _ } }} . 
  refine {{ new 'pair_init : StateInitLRecord @ "pair_init" := 
            [$ {} ⇒ { StateInit_ι_split_depth } ; 
               {} ⇒ { StateInit_ι_special } ; 
               #{pair_code} -> set () ⇒ { StateInit_ι_code } ;
               !{pair_data_cl} -> set () ⇒ { StateInit_ι_data } ;
               {} ⇒ { StateInit_ι_library } $] ; { _ } }} .
  refine {{ new 'pair_init_cl : cell @ "pair_init_cl" := 
                     build ( σ !{ pair_init } ) -> make_cell () ; { _ } }} . 
  refine {{ return_ [ !{ pair_init } , tvm_hash ( !{pair_init_cl} )  ] }} .
Defined .

Definition prepare_xchg_pair_state_init_and_addr_right { a1 a2 } ( pair_data : URValue XchgPairClassTypesModule.DXchgPairLRecord a1 ) 
                                                                  ( pair_code : URValue cell a2 ) : 
          URValue ( StateInitLRecord # uint256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_xchg_pair_state_init_and_addr pair_data pair_code ) . 
 
Notation " 'prepare_xchg_pair_state_init_and_addr_' '(' pair_data , pair_code ')' " := ( prepare_xchg_pair_state_init_and_addr_right pair_data pair_code ) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 , pair_code custom URValue at level 0 ) : ursus_scope .

Definition approveXchgPairImpl ( pubkey :  uint256 ) ( xchg_pair_listing_requests :  xchg_pairs_map ) 
                               ( xchg_pair_code :  cell ) ( workchain_id :  int ) ( listing_cfg :  ListingConfigLRecord ) 
                               : UExpression ( address # xchg_pairs_map )  true . 

 	 	 refine {{ new 'opt_req_info : ( optional XchgPairListingRequestLRecord ) @ "opt_req_info" := 
                         (#{xchg_pair_listing_requests}) -> extract ( #{pubkey} ) ; { _ } }} . 
 	 	 refine {{ require_ ( !{ opt_req_info }  ,  error_code::xchg_pair_not_requested  ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( XchgPairListingRequestLRecord ) @ "req_info" := 
                          (!{opt_req_info}) -> get () ; { _ } }} . (* 43'' *)
 	 	 refine {{ new 'pair_data : ( XchgPairClassTypesModule.DXchgPairLRecord ) @ "pair_data" :=  
               	 	 [$ tvm_myaddr () ⇒ { DXchgPair_ι_flex_addr_ } ; 
                      !{req_info} ↑ XchgPairListingRequest.tip3_major_root ⇒ { DXchgPair_ι_tip3_major_root_ } ; 
                      !{req_info} ↑ XchgPairListingRequest.tip3_minor_root ⇒ { DXchgPair_ι_tip3_minor_root_ } ; 
                      0 ⇒ { DXchgPair_ι_min_amount_ } ; 
                  [ #{0%Z} , 0 ] ⇒ { DXchgPair_ι_notify_addr_ } $] ; { _ } }} . (*45''*) 

 	 	 refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) @ ( "state_init" , "std_addr" ) := prepare_xchg_pair_state_init_and_addr_ ( !{pair_data} , #{xchg_pair_code} ) ; { _ } }} . 
      refine {{ new 'xchg_pair : address @ "xchg_pair" := 
                      [ #{workchain_id} , !{std_addr} ] ; { _ } }} .
    refine ( let xchg_pair_ptr := {{ IXchgPairPtr [[ !{xchg_pair}  ]] }} in 
              {{ {xchg_pair_ptr} with {} ⤳ XchgPair.deploy ( !{state_init} ) ; {_} }} ).  

      refine ( let xchg_pair_ptr := {{ IXchgPairPtr [[ !{xchg_pair}  ]] }} in 
        {{ {xchg_pair_ptr} with [$ ((#{listing_cfg}) ↑ ListingConfig.pair_deploy_value) ⇒ { Messsage_ι_value } ;
                                    FALSE  ⇒ { Messsage_ι_bounce } ;
                                    DEFAULT_MSG_FLAGS ⇒ { Messsage_ι_flags }  $] 
                        ⤳ XchgPair.onDeploy (!{req_info} ↑ XchgPairListingRequest.min_amount , 
                                (#{listing_cfg}) ↑ ListingConfig.pair_keep_balance , 
                                !{req_info} ↑ XchgPairListingRequest.notify_addr ) ; { _ } }} ).
 	 	 refine {{ new 'remaining_funds : uint128 @ "remaining_funds" := !{req_info} ↑ XchgPairListingRequest.client_funds - 
                                                                     ( #{listing_cfg} ) ↑ ListingConfig.register_pair_cost  ; { _ } }} . 
     refine {{ IListingAnswerPtr [[  !{req_info} ↑ XchgPairListingRequest.client_addr ]]
          with [$ !{remaining_funds} ⇒ { Messsage_ι_value } $]  ⤳ .onXchgPairApproved ( #{pubkey} , !{xchg_pair} ) ; {_} }}.                                                               
 	 	 refine {{ return_ [ !{xchg_pair} , #{xchg_pair_listing_requests} ] }} . 
 Defined .
 
 Definition approveXchgPairImpl_right { a1 a2 a3 a4 a5 }  
( pubkey : URValue uint256 a1 ) 
( xchg_pair_listing_requests : URValue xchg_pairs_map a2 ) 
( xchg_pair_code : URValue cell a3 ) ( workchain_id : URValue int a4 ) 
( listing_cfg : URValue ListingConfigLRecord a5 ) 
: URValue ( address # xchg_pairs_map ) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ5 ) approveXchgPairImpl 
 pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg ) . 
 
 Notation " 'approveXchgPairImpl_' '(' pubkey , xchg_pair_listing_requests , xchg_pair_code , workchain_id , listing_cfg ')' " := 
 ( approveXchgPairImpl_right 
 pubkey xchg_pair_listing_requests xchg_pair_code workchain_id listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , xchg_pair_listing_requests custom URValue at level 0 
 , xchg_pair_code custom URValue at level 0 
 , workchain_id custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

 Definition rejectXchgPairImpl 
( pubkey :  uint256 ) 
( xchg_pair_listing_requests :  xchg_pairs_map ) 
( listing_cfg :  ListingConfigLRecord ) : 
UExpression xchg_pairs_map true . 
 	 	 refine {{ new 'opt_req_info : ( optional XchgPairListingRequestLRecord ) @ "opt_req_info" := 
                (#{xchg_pair_listing_requests}) -> extract (#{pubkey}) ; { _ } }} . 
 	 	 refine {{ require_ ( !{ opt_req_info } ,  error_code::xchg_pair_not_requested  ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( XchgPairListingRequestLRecord ) @ "req_info" := 
                  (!{opt_req_info}) -> get () ; { _ } }} . 
 	 	 refine {{ new 'remaining_funds : uint128 @ "remaining_funds" := 
          ( (!{req_info}) ↑ XchgPairListingRequest.client_funds )
                 - ( (#{listing_cfg}) ↑ ListingConfig.reject_pair_cost ) ; { _ } }} . 
refine {{ IListingAnswerPtr [[  !{req_info} ↑ XchgPairListingRequest.client_addr ]]
          with [$ !{remaining_funds} ⇒ { Messsage_ι_value } $]  ⤳ .onXchgPairRejected ( #{pubkey} ) ; {_} }}.  
 	 	 refine {{ return_ #{xchg_pair_listing_requests} }} . 
 Defined . 
 
 Definition rejectXchgPairImpl_right { a1 a2 a3 } 
 ( pubkey : URValue uint256 a1 ) 
( xchg_pair_listing_requests : URValue xchg_pairs_map a2 ) 
( listing_cfg : URValue ListingConfigLRecord a3 ) 
: URValue xchg_pairs_map true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) rejectXchgPairImpl 
 pubkey xchg_pair_listing_requests listing_cfg ) . 
 
 Notation " 'rejectXchgPairImpl_' '(' pubkey , xchg_pair_listing_requests , listing_cfg ')' " := 
 ( rejectXchgPairImpl_right 
 pubkey xchg_pair_listing_requests listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , xchg_pair_listing_requests custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope .

 Definition prepare_wrapper_state_init_and_addr 
( wrapper_code :  cell ) 
( wrapper_data :  ( WrapperClassTypesModule.DWrapperLRecord ) ) 
: UExpression ( StateInitLRecord * uint256 )  false . 
 	 	 refine {{ new 'wrapper_data_cl : cell @ "wrapper_data_cl" :=  
             prepare_persistent_data_ ( {} (* wrapper_replay_protection_t::init () *) , #{wrapper_data} ) ; { _ } }} . 
 	 	 refine {{ new 'wrapper_init : StateInitLRecord @ "wrapper_init" := 

               [$ {} ⇒ { StateInit_ι_split_depth } ; 
                  {} ⇒ { StateInit_ι_special } ;
               (#{wrapper_code}) -> set () ⇒ { StateInit_ι_code } ;
               (!{wrapper_data_cl}) -> set () ⇒ { StateInit_ι_data } ;  
                  {} ⇒ { StateInit_ι_library } 
               $]; { _ } }} . 

 	 	 refine {{ new 'wrapper_init_cl : cell @ "wrapper_init_cl" := 
                   build ( σ !{ wrapper_init } ) -> make_cell () ; { _ } }} . 
 	 	 refine {{ return_ [ !{ wrapper_init } ,  tvm_hash ( !{wrapper_init_cl} ) ] }} . 
 Defined . 

 Definition prepare_wrapper_state_init_and_addr_right { a1 a2 }  ( wrapper_code : URValue cell a1 )
 ( wrapper_data : URValue ( WrapperClassTypesModule.DWrapperLRecord ) a2 ) : URValue ( StateInitLRecord * uint256 )  ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) prepare_wrapper_state_init_and_addr 
 wrapper_code wrapper_data ) . 
 
 Notation " 'prepare_wrapper_state_init_and_addr_' '(' wrapper_code , wrapper_data ')' " := 
 ( prepare_wrapper_state_init_and_addr_right 
 wrapper_code wrapper_data ) 
 (in custom URValue at level 0 , wrapper_code custom URValue at level 0 
 , wrapper_data custom URValue at level 0 ) : ursus_scope . 

 Definition prepare_external_wallet_state_init_and_addr 
( name :  ( XString ) ) 
( symbol :  ( XString ) ) 
( decimals :  uint8 ) 
( root_public_key :  uint256 ) 
( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  cell ) 
( workchain_id :  int ) 
: UExpression ( StateInitLRecord # uint256 )  false .

refine {{ new 'wallet_data : ( TONTokenWalletClassTypesModule.DTONTokenWalletExternalLRecord ) @ "wallet_data" := 
                 [$ 
                       (#{name}) ⇒ {DTONTokenWalletExternal_ι_name_ } ; 
                       (#{symbol}) ⇒ {DTONTokenWalletExternal_ι_symbol_ } ;
                       (#{decimals}) ⇒ {DTONTokenWalletExternal_ι_decimals_ } ; 
                        0 ⇒ {DTONTokenWalletExternal_ι_balance_} ; 
                       (#{root_public_key}) ⇒ {DTONTokenWalletExternal_ι_root_public_key_ } ; 
                       (#{wallet_public_key}) ⇒ {DTONTokenWalletExternal_ι_wallet_public_key_ } ; 
                       (#{root_address}) ⇒ {DTONTokenWalletExternal_ι_root_address_ } ; 
                       (#{owner_address}) ⇒ {DTONTokenWalletExternal_ι_owner_address_ } ; 
                       (#{code}) ⇒ {DTONTokenWalletExternal_ι_code_ } ; 
                       {} ⇒ {DTONTokenWalletExternal_ι_allowance_ } ; 
                       (#{workchain_id}) ⇒ {DTONTokenWalletExternal_ι_workchain_id_ } 
                               $] ; { _ } }} . 

 refine {{ new 'wallet_data_cl : cell @ "wallet_data_cl" :=
             prepare_persistent_data_ ( {} (* external_wallet_replay_protection_t::init () *) , !{wallet_data} ) ; { _ } }} . 
 refine {{ new 'wallet_init : StateInitLRecord @ "wallet_init" := 
               [$ {} ⇒ { StateInit_ι_split_depth } ; 
                  {} ⇒ { StateInit_ι_special } ;
               (#{code}) -> set () ⇒ { StateInit_ι_code } ;
               (!{wallet_data_cl}) -> set () ⇒ { StateInit_ι_data } ;  
                  {} ⇒ { StateInit_ι_library } 
               $]; { _ } }} . 

 refine {{ new 'wallet_init_cl : cell @ "wallet_init_cl" := 
                  build ( σ !{ wallet_init } ) -> make_cell () ; { _ } }} . 
 refine {{ return_ [ !{ wallet_init } ,  tvm_hash ( !{wallet_init_cl} )  ] }} . 
 Defined . 

 Definition prepare_external_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  
( name : URValue ( XString ) a1 ) 
( symbol :URValue  ( XString ) a2 ) 
( decimals : URValue uint8 a3 )
 ( root_public_key : URValue uint256 a4 ) 
( wallet_public_key : URValue uint256 a5 ) 
( root_address : URValue address a6 ) 
( owner_address : URValue ( optional address ) a7 )
 ( code : URValue cell a8 ) 
( workchain_id : URValue int a9 ) 
: URValue ( StateInitLRecord * uint256 )  ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_external_wallet_state_init_and_addr 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_external_wallet_state_init_and_addr_' '(' name , symbol , decimals , root_public_key , wallet_public_key , root_address , owner_address , code , workchain_id ')' " := 
 ( prepare_external_wallet_state_init_and_addr_right 
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

 Definition approveWrapperImpl 
( pubkey :  uint256 ) 
( wrapper_listing_requests :  ( wrappers_map ) ) 
( wrapper_code :  cell ) 
( ext_wallet_code :  cell ) 
( flex_wallet_code :  cell ) 
( workchain_id :  int ) 
( listing_cfg :  ListingConfigLRecord ) 
: UExpression ( address # ( wrappers_map ) )  true . 

 refine {{ new 'opt_req_info : ( optional WrapperListingRequestLRecord ) @ "opt_req_info" := 
             (#{wrapper_listing_requests}) -> extract ( #{pubkey} ) ; { _ } }} . 
 refine {{ require_ ( !{ opt_req_info }  ,  error_code::wrapper_not_requested  ) ; { _ } }} . 
 refine {{ new 'req_info : ( WrapperListingRequestLRecord ) @ "req_info" := 
               (!{opt_req_info}) -> get () ; { _ } }} . 
 refine {{ new 'tip3cfg : ( Tip3ConfigLRecord ) @ "tip3cfg" := 
                 (!{req_info}) ↑ WrapperListingRequest.tip3cfg ; { _ } }} .
 refine {{ new 'wrapper_data : ( WrapperClassTypesModule.DWrapperLRecord ) @ "wrapper_data" :=  
               	 [$ ( (!{ tip3cfg }) ↑ Tip3Config.name ) ⇒ { DWrapper_ι_name_ } ; 
               ( (!{ tip3cfg }) ↑ Tip3Config.symbol ) ⇒ { DWrapper_ι_symbol_ } ; 
               ( (!{ tip3cfg }) ↑ Tip3Config.decimals ) ⇒ { DWrapper_ι_decimals_ } ; 
               (#{workchain_id}) ⇒ { DWrapper_ι_workchain_id_ } ; 
               (#{pubkey}) ⇒ { DWrapper_ι_root_public_key_ } ; 
               {} ⇒ { DWrapper_ι_total_granted_ } ; 
               {} ⇒ { DWrapper_ι_internal_wallet_code_ } ; 
              ( ( tvm_myaddr () ) -> set () )  ⇒ { DWrapper_ι_owner_address_ } ; 
               ( (#{listing_cfg}) ↑ ListingConfig.wrapper_keep_balance ) ⇒ { DWrapper_ι_start_balance_ } ; 
               {} ⇒ { DWrapper_ι_external_wallet_ }  
               $] ; { _ } }} . 
 	 	 refine {{ new ( 'wrapper_init : StateInitLRecord , 
                     'wrapper_hash_addr : uint256 ) @ ( "wrapper_init" , "wrapper_hash_addr" ) := 
               prepare_wrapper_state_init_and_addr_ ( #{wrapper_code} , !{wrapper_data} ) ; { _ } }} . 
 refine {{ new 'wrapper_addr : address @ "wrapper_addr" := 
                            [ #{workchain_id} , !{wrapper_hash_addr} ]  ; { _ } }} .
 	 	 refine {{ new ( 'wallet_init : StateInitLRecord , 'wallet_hash_addr : uint256 ) @ ( "wallet_init" , "wallet_hash_addr" ) := 
       prepare_external_wallet_state_init_and_addr_ 
           ( (!{ tip3cfg }) ↑ Tip3Config.name , 
             (!{ tip3cfg }) ↑ Tip3Config.symbol , 
             (!{ tip3cfg }) ↑ Tip3Config.decimals , 
             (!{ tip3cfg }) ↑ Tip3Config.root_public_key , 
             #{pubkey} , 
             (!{ tip3cfg }) ↑ Tip3Config.root_address , 
             (!{wrapper_addr}) -> set () , 
              #{ext_wallet_code} , 
              #{workchain_id} ) ; { _ } }} . 
 refine {{ new 'wallet_addr : address @ "wallet_addr" := {} ; { _ } }} .

          
refine ( let wallet_addr_ptr := {{ ITONTokenWalletPtr [[ !{wallet_addr}  ]] }} in 
              {{ {wallet_addr_ptr} with [$ (#{listing_cfg}) ↑ ListingConfig.ext_wallet_balance ⇒ { Messsage_ι_value }  $] 
                                         ⤳ TONTokenWallet.deploy_noop ( !{wallet_init} ) ; {_} }} ).  
refine ( let wallet_addr_ptr := {{ IWrapperPtr [[ !{wallet_addr}  ]] }} in 
              {{ {wallet_addr_ptr} with [$ ((#{listing_cfg}) ↑ ListingConfig.wrapper_deploy_value) ⇒ { Messsage_ι_value }  $] 
                                         ⤳ Wrapper.deploy ( !{wrapper_init} ) ; {_} }} ). (* Тут должен быть init, который делаент непонятно что *)  

 	 	 refine {{ return_ [ !{wrapper_addr} , #{wrapper_listing_requests} ] }} . 
 Defined .
 
 Definition approveWrapperImpl_right { a1 a2 a3 a4 a5 a6 a7 }  
( pubkey : URValue uint256 a1 ) 
( wrapper_listing_requests : URValue (wrappers_map ) a2 )
( wrapper_code : URValue cell a3 ) 
( ext_wallet_code : URValue cell a4 ) 
( flex_wallet_code : URValue cell a5 )
 ( workchain_id : URValue int a6 ) 
( listing_cfg : URValue ListingConfigLRecord a7 ) 
: URValue ( address # (wrappers_map ) )  true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) approveWrapperImpl 
 pubkey wrapper_listing_requests wrapper_code ext_wallet_code flex_wallet_code workchain_id listing_cfg ) . 
 
 Notation " 'approveWrapperImpl_' '(' pubkey ',' wrapper_listing_requests ',' wrapper_code ',' ext_wallet_code ',' flex_wallet_code ',' workchain_id ',' listing_cfg ')' " := 
 ( approveWrapperImpl_right 
 pubkey wrapper_listing_requests  wrapper_code  ext_wallet_code  flex_wallet_code  workchain_id  listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , wrapper_listing_requests custom URValue at level 0 
 , wrapper_code custom URValue at level 0 
 , ext_wallet_code custom URValue at level 0 
 , flex_wallet_code custom URValue at level 0 
 , workchain_id custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

Definition rejectWrapperImpl 
( pubkey :  uint256 ) 
( wrapper_listing_requests :  (wrappers_map ) ) 
( listing_cfg :  ListingConfigLRecord ) 
: UExpression (wrappers_map ) true . 

 	 	 refine {{ new 'opt_req_info : ( optional WrapperListingRequestLRecord ) @ "opt_req_info" := 
                   (#{wrapper_listing_requests}) -> extract ( #{pubkey} ) ; { _ } }} . 
 	 	 refine {{ require_ ( !{ opt_req_info } ,  error_code::wrapper_not_requested  ) ; { _ } }} . 
 	 	 refine {{ new 'req_info : ( WrapperListingRequestLRecord ) @ "req_info" := 
                             (!{opt_req_info}) -> get () ; { _ } }} . 
 	 	 refine {{ new 'remaining_funds : uint128 @ "remaining_funds" := 
              ( (!{req_info}) ↑ WrapperListingRequest.client_funds ) - 
                ( (#{listing_cfg}) ↑ ListingConfig.reject_wrapper_cost ) ; { _ } }} . 
refine {{ IListingAnswerPtr [[  !{req_info} ↑ WrapperListingRequest.client_addr ]]
          with [$ !{remaining_funds} ⇒ { Messsage_ι_value } $]  ⤳ .onWrapperRejected ( #{pubkey} ) ; {_} }}.  
 	 	 refine {{ return_ (#{wrapper_listing_requests}) }} . 
 Defined .
 
 Definition rejectWrapperImpl_right { a1 a2 a3 } 
( pubkey : URValue uint256 a1 ) 
( wrapper_listing_requests : URValue (wrappers_map ) a2 ) 
( listing_cfg : URValue ListingConfigLRecord a3 ) 
: URValue (wrappers_map ) true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ3 ) rejectWrapperImpl 
 pubkey wrapper_listing_requests listing_cfg ) . 
 
 Notation " 'rejectWrapperImpl_' '(' pubkey , wrapper_listing_requests , listing_cfg ')' " := 
 ( rejectWrapperImpl_right 
 pubkey wrapper_listing_requests listing_cfg ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , wrapper_listing_requests custom URValue at level 0 
 , listing_cfg custom URValue at level 0 ) : ursus_scope . 

 Definition registerXchgPair 
( pubkey :  uint256 ) 
( tip3_major_root : address ) 
( tip3_minor_root : address ) 
( min_amount :  uint128 ) 
( notify_addr : address ) 
: UExpression address true . 

 refine {{ require_ ( int_value() > (_listing_cfg_ ↑ ListingConfig.register_pair_cost) ,  error_code::not_enough_funds  ) ; { _ } }} . 
 refine {{ require_ ( ~ (  _xchg_pair_listing_requests_ -> contains(#{pubkey}) ) ,  error_code::xchg_pair_with_such_pubkey_already_requested  ) ; { _ } }} . 
 refine {{ _xchg_pair_listing_requests_ -> set_at ( #{pubkey} , 
          [ int_sender () , int_value () - _listing_cfg_ ↑ ListingConfig.register_return_value , 
            #{tip3_major_root} , 
            #{tip3_minor_root} , 
            #{min_amount} , 
            #{notify_addr} ] ) ; { _ } }} . 
       	 	 refine {{ new 'pair_data : ( XchgPairClassTypesModule.DXchgPairLRecord ) @ "pair_data" :=  
               	 	 [$  ( tvm_myaddr () ) ⇒ { DXchgPair_ι_flex_addr_ }  ; 
                      (#{tip3_major_root}) ⇒ { DXchgPair_ι_tip3_major_root_ } ; 
                      (#{tip3_minor_root}) ⇒ { DXchgPair_ι_tip3_minor_root_ } ; 
                      0 ⇒ { DXchgPair_ι_min_amount_ }   ; 
                     [ # {0%Z} , 0 ]  ⇒ { DXchgPair_ι_notify_addr_ }  
                   $] ; { _ } }} . 
 	 	 refine {{ set_int_return_value ( _listing_cfg_ ↑ ListingConfig.register_return_value ) ; { _ } }} . 
 	 	 refine {{ new ( 'state_init : StateInitLRecord , 'std_addr : uint256 ) @ ( "state_init" , "std_addr" )  := 
       prepare_xchg_pair_state_init_and_addr_ ( !{pair_data} , _xchg_pair_code_ -> get () ) ; { _ } }} . 
     (* AL: change workchain_id type *)  
 	 	 refine {{ return_ [ _workchain_id_  , !{std_addr} ] }} . 
 Defined . 

 Definition approveXchgPair ( pubkey :  uint256 ) : UExpression address true . 
  	 	 refine {{ check_owner_ ( ) ; { _ } }} .
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ new ( 'xchg_pair : address , 'xchg_pair_listing_requests : xchg_pairs_map  ) @ ( "xchg_pair" , "xchg_pair_listing_requests" ) := 
               approveXchgPairImpl_ ( #{pubkey} , 
                                      _xchg_pair_listing_requests_ , 
                                      _xchg_pair_code_ -> get () , 
                                      _workchain_id_ , 
                                      _listing_cfg_ ) ; { _ } }} . 
 	 	 refine {{ _xchg_pair_listing_requests_ := !{xchg_pair_listing_requests} ; { _ } }} . 
 	 	 refine {{ if ( #{Internal} ) then { { _ } } else { exit_ {} } ; { _ } }} . 
 	 	 refine {{ new 'value_gr : uint @ "value_gr" := int_value () ; { _ } }} . 
  	 refine {{ tvm_rawreserve ( tvm_balance () - !{value_gr} ,  rawreserve_flag::up_to  ) (* ; { _ } *) }} .  
 	 	 refine {{ set_int_return_flag ( #{SEND_ALL_GAS} ) ; {_} }} .  
 	 refine {{ return_ !{ xchg_pair } }} . 
 Defined . 

Definition rejectXchgPair ( pubkey : uint256 ) : UExpression XBool true . 
  	 	 refine {{ check_owner_ ( ) ; { _ } }} .
 	 	 refine {{ _xchg_pair_listing_requests_ := 
          rejectXchgPairImpl_ ( #{pubkey} , _xchg_pair_listing_requests_ , _listing_cfg_ ) ; { _ } }} . 
 	 	 refine {{ if ( #{Internal} ) then { { _ } } else { exit_ {} } ; { _ } }} . 
 	 	 	 refine {{ new 'value_gr : uint @ "value_gr" := int_value () ; { _ } }} . 
 	 	 	 refine {{ tvm_rawreserve ( tvm_balance () - !{value_gr} ,  rawreserve_flag::up_to ) (* ; { _ } *) }} .
  	 	 	 refine {{ set_int_return_flag (  #{SEND_ALL_GAS} ) ; {_} }} .  
 	 refine {{ return_ TRUE }} . 
 Defined . 

Definition registerWrapper 
( pubkey :  uint256 ) 
( tip3cfg :  ( Tip3ConfigLRecord ) ) 
: UExpression address true . 
 	 	 refine {{ require_ ( int_value () 
           > ( _listing_cfg_ ↑ ListingConfig.register_wrapper_cost ) ,  error_code::not_enough_funds  ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( ~ (_wrapper_listing_requests_ -> contains ( #{pubkey} ) ) ) ,  error_code::wrapper_with_such_pubkey_already_requested  ) ; { _ } }} . 
 	 	 refine {{ _wrapper_listing_requests_ -> set_at ( #{pubkey} , 
                               [ int_sender () , 
                                 int_value () - _listing_cfg_ ↑ ListingConfig.register_return_value , 
                                 #{tip3cfg} ] ) ; { _ } }} . 
 	 	 refine {{ new 'wrapper_data : ( WrapperClassTypesModule.DWrapperLRecord ) @ "wrapper_data" := 
 	 	 [$ ((#{tip3cfg}) ↑ Tip3Config.name) ⇒ { DWrapper_ι_name_ } ; 
        ((#{tip3cfg}) ↑ Tip3Config.symbol) ⇒ { DWrapper_ι_symbol_ } ; 
        ((#{tip3cfg}) ↑ Tip3Config.decimals) ⇒ { DWrapper_ι_decimals_ } ;
        _workchain_id_ ⇒ { DWrapper_ι_workchain_id_ } ;
          (#{pubkey}) ⇒ { DWrapper_ι_root_public_key_ } ; 
            (#{pubkey}) ⇒ { DWrapper_ι_root_public_key_ } ;
           ( tvm_myaddr () ) -> set () ⇒ { DWrapper_ι_owner_address_ } ;
        {} ⇒ { DWrapper_ι_total_granted_ } ; 
        {} ⇒ { DWrapper_ι_internal_wallet_code_ } ; 
       ( (tvm_myaddr ()) -> set() ) ⇒ { DWrapper_ι_owner_address_ } ;
       (_listing_cfg_ ↑ ListingConfig.wrapper_keep_balance) ⇒ { DWrapper_ι_start_balance_ } ; 
        {} ⇒ { DWrapper_ι_external_wallet_ }  
      $] ; { _ } }} . 
  	 	 refine {{ set_int_return_value ( _listing_cfg_ ↑  ListingConfig.register_return_value ) ; { _ } }} .  
 	 	 refine {{ new ( 'wrapper_init :StateInitLRecord , 'wrapper_hash_addr : uint256 ) @ ( "wrapper_init" , "wrapper_hash_addr" ) := 
               prepare_wrapper_state_init_and_addr_ ( _wrapper_code_ -> get () , !{wrapper_data} ) ; { _ } }} . 
 	 	 refine {{ return_  [ _workchain_id_ , !{wrapper_hash_addr} ] }} . 
 Defined . 
 
 Definition approveWrapper ( pubkey :  uint256 ) : UExpression address true . 
  	 	 refine {{ check_owner_ ( ) ; { _ } }} .
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ new ( 'wrapper_addr : address , 
                     'new_wrapper_listing_requests : (wrappers_map ) )
                     @ ( "wrapper_addr" , "new_wrapper_listing_requests" ) := 
                 approveWrapperImpl_ ( #{pubkey} , 
                                  _wrapper_listing_requests_ , 
                                  _wrapper_code_ -> get () , 
                                  _ext_wallet_code_ -> get () , 
                                  _flex_wallet_code_ -> get () , 
                                  _workchain_id_ , 
                                  _listing_cfg_ ) ; { _ } }} . 
 	 	 refine {{ _wrapper_listing_requests_ := !{new_wrapper_listing_requests} ; { _ } }} . 
 	 	 refine {{ if ( #{Internal} ) then { { _ } } else { exit_ {} } ; { _ } }} . 
 	 	 refine {{new 'value_gr : uint @ "value_gr" := int_value () ; { _ } }} . 
  	 refine {{ tvm_rawreserve ( tvm_balance () - !{value_gr} ,  rawreserve_flag::up_to  ) (* ; { _ } *) }} .
  	 	 	 refine {{ set_int_return_flag ( #{SEND_ALL_GAS} ) ; {_} }} .
 	 refine {{ return_ !{ wrapper_addr } }} . 
Defined . 
 

 Definition rejectWrapper ( pubkey :  uint256 ) : UExpression XBool true . 
  	 	 refine {{ check_owner_ ( ) ; { _ } }} .
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ _wrapper_listing_requests_ := 
            rejectWrapperImpl_ ( #{pubkey} , _wrapper_listing_requests_ , _listing_cfg_ ) ; { _ } }} . 
 	 	 refine {{ if ( #{Internal} ) then { { _ } } else { exit_ {} } ; { _ } }} . 
 	 	 	 refine {{ new 'value_gr : uint @ "value_gr" := int_value () ; { _ } }} . 
 	 	 	 refine {{ tvm_rawreserve ( tvm_balance () - !{value_gr} ,  rawreserve_flag::up_to  ) (* ; { _ } *) }} .
  	 	 	 refine {{ set_int_return_flag ( #{SEND_ALL_GAS} ) ; {_} }} . 
 	 refine {{ return_ TRUE }} . 
Defined . 

Definition isFullyInitialized : UExpression XBool false . 
 	 	 refine {{ return_ ? ( _pair_code_ && 
                         _price_code_ && 
                         _xchg_pair_code_ && 
                         _xchg_price_code_ && 
                         _ext_wallet_code_ && 
                         _flex_wallet_code_ && 
                         _wrapper_code_ ) }} . 
 Defined . 

 Definition isFullyInitialized_right  : URValue XBool false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) isFullyInitialized 
 ) . 
 
 Notation " 'isFullyInitialized_' '(' ')' " := 
 ( isFullyInitialized_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getTonsCfg : UExpression TonsConfigLRecord false . 
 	 	 refine {{ return_ _tons_cfg_ }} . 
 Defined .
 
 Definition getTonsCfg_right  : URValue TonsConfigLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTonsCfg 
 ) . 
 
 Notation " 'getTonsCfg_' '(' ')' " := 
 ( getTonsCfg_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getListingCfg : UExpression ListingConfigLRecord false . 
 	 	 refine {{ return_ _listing_cfg_ }} . 
 Defined . 
 
 Definition getListingCfg_right  : URValue ListingConfigLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getListingCfg 
 ) . 
 
 Notation " 'getListingCfg_' '(' ')' " := 
 ( getListingCfg_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition getTradingPairCode : UExpression cell true . 
 	 	 refine {{ return_ ( _pair_code_ -> get () ) }} . 
 Defined . 
 
Definition getTradingPairCode_right  : URValue cell true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTradingPairCode 
 ) . 
 
 Notation " 'getTradingPairCode_' '(' ')' " := 
 ( getTradingPairCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
 Definition getXchgPairCode : UExpression cell true . 
 	 	 refine {{ return_ ( _xchg_pair_code_ -> get () ) }} . 
 Defined . 

 Definition getXchgPairCode_right  : URValue cell true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getXchgPairCode 
 ) . 
 
 Notation " 'getXchgPairCode_' '(' ')' " := 
 ( getXchgPairCode_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getDealsLimit : UExpression uint8 false . 
 	 	 refine {{ return_ _deals_limit_ }} . 
 Defined . 

 Definition getDealsLimit_right  : URValue uint8 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDealsLimit 
 ) . 
 
 Notation " 'getDealsLimit_' '(' ')' " := 
 ( getDealsLimit_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getOwnershipInfo : UExpression FlexOwnershipInfoLRecord false . 
 	 	 refine {{ return_ [ _deployer_pubkey_ , _ownership_description_ , _owner_address_ ] }} . 
 Defined . 

 Definition getOwnershipInfo_right  : URValue FlexOwnershipInfoLRecord false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwnershipInfo 
 ) . 
 
 Notation " 'getOwnershipInfo_' '(' ')' " := 
 ( getOwnershipInfo_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getWrapperListingRequests : UExpression ( XHMap uint WrapperListingRequestWithPubkeyLRecord ) false . 
 	 	 refine {{ new 'rv :  ( XHMap uint WrapperListingRequestWithPubkeyLRecord ) @ "rv" := {} ; { _ } }} . 
     refine {{ for ( 'v : _wrapper_listing_requests_) do { {_ : UEf} } ; { _ } }}. 
	   refine {{ {rv}  -> push ( [ first ({v}) , second ({v}) ] ) }}.
  	 refine {{ return_ !{rv} }} . 
Defined . 

 Definition getWrapperListingRequests_right  : URValue ( XHMap uint WrapperListingRequestWithPubkeyLRecord) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getWrapperListingRequests 
 ) . 
 
 Notation " 'getWrapperListingRequests_' '(' ')' " := 
 ( getWrapperListingRequests_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getTradingPairListingRequests : UExpression ( XHMap uint TradingPairListingRequestWithPubkeyLRecord ) false . 
 	 	 refine {{ new 'rv :  ( XHMap uint TradingPairListingRequestWithPubkeyLRecord ) @ "rv" := {} ; { _ } }} . 
     refine {{ for ( 'v : _trading_pair_listing_requests_) do { {_ : UEf} } ; { _ } }}. 
	   refine {{ {rv}  -> push ( [ first ({v}) , second ({v}) ] ) }}.
 	 refine {{ return_ !{rv} }} . 
Defined . 

 Definition getTradingPairListingRequests_right  : URValue ( XHMap uint TradingPairListingRequestWithPubkeyLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTradingPairListingRequests 
 ) . 
 
 Notation " 'getTradingPairListingRequests_' '(' ')' " := 
 ( getTradingPairListingRequests_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getXchgPairListingRequests : UExpression ( XHMap uint XchgPairListingRequestWithPubkeyLRecord ) false . 
 	 	 refine {{ new 'rv :  ( XHMap uint XchgPairListingRequestWithPubkeyLRecord ) @ "rv" := {} ; { _ } }} . 
     refine {{ for ( 'v : _xchg_pair_listing_requests_) do { {_ : UEf} } ; { _ } }}. 
	   refine {{ {rv}  -> push ( [ first ({v}) , second ({v}) ] ) }}.
 	 refine {{ return_ !{rv} }} . 
Defined .

 Definition getXchgPairListingRequests_right  : URValue ( XHMap uint XchgPairListingRequestWithPubkeyLRecord ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getXchgPairListingRequests 
 ) . 
 
 Notation " 'getXchgPairListingRequests_' '(' ')' " := 
 ( getXchgPairListingRequests_right 
 ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 Definition getDetails : UExpression FlexDetailsLRecord true .
 	 	 refine {{ return_ [ isFullyInitialized_ ( ) , 
                         getTonsCfg_ ( ) , 
                         getListingCfg_ ( ) , 
                         getTradingPairCode_ ( ) , 
                         getXchgPairCode_ ( ) ,
                         getDealsLimit_ ( ) , 
                         getOwnershipInfo_ ( ) , 
                         getWrapperListingRequests_ ( ) , 
                         getTradingPairListingRequests_ ( ) , 
                         getXchgPairListingRequests_ ( ) ] }} . 
 Defined .

 Definition getSellPriceCode ( tip3_addr : address ) : UExpression cell true . 
     refine {{ require_ (FALSE, 0) ; {_} }}.
 	 	 refine {{ new 'price_code_sl : ( slice ) @ "price_code_sl" := {}
                          (* _price_code_ -> get () -> to_slice () *) ; { _ } }} . 
 	 	 (* refine {{ require_ ( (!{price_code_sl}) -> refs () == #{2} ,  error_code::unexpected_refs_count_in_code  ) ; { _ } }} .  *)
 	 	 refine {{ new 'salt : cell @ "salt" := {} 
            (*  builder ( ) . stslice ( tvm_myaddr ( ) ) . stslice ( tip3_addr.sl ( ) ) . endc ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ {} (* builder ( ) . stslice ( !{ price_code_sl } ) . stref ( !{ salt } ) . endc ( ) *) }} . 
 Defined . 

 Definition getXchgPriceCode ( tip3_addr1 : address ) ( tip3_addr2 : address ) : UExpression cell true . 
 	 	 refine {{ require_ (FALSE, 0) ; {_} }}.
      refine {{ new 'price_code_sl : ( slice ) @ "price_code_sl" := {}
               (* _xchg_price_code_ -> get () -> to_slice ()  *) ; { _ } }} . 
 	 	 (* refine {{ require_ ( (!{price_code_sl}) -> refs () == #{2} ,   error_code::unexpected_refs_count_in_code  ) ; { _ } }} .  *)
 	 	 refine {{ new 'keys : ( address # address )  @ "keys" := 
                   [ #{tip3_addr1} , #{tip3_addr2} ] ; { _ } }} . 
 	 	 refine {{ return_ {} (* builder ( ) . stslice ( !{ price_code_sl } ) . stref ( build ( !{ keys } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 

 Definition getSellTradingPair ( tip3_root : address ) : UExpression address true . 
 	 	 refine {{ new 'std_addr : uint256 @ "std_addr" := 
          second (  prepare_trading_pair_ ( ( tvm_myaddr () ) , #{tip3_root} , _pair_code_ -> get () ) ) ; { _ } }} . 
 	 	 refine {{ return_ [ _workchain_id_ , !{ std_addr } ] }} . 
 Defined . 
 
 Definition getXchgTradingPair ( tip3_major_root : address ) 
( tip3_minor_root : address ) : UExpression address true . 
 	 	 refine {{ new 'myaddr :address @ "myaddr" := ( tvm_myaddr () ) ; { _ } }} . 
 	 	 refine {{ new 'pair_data : ( XchgPairClassTypesModule.DXchgPairLRecord ) @ "pair_data" :=  
               	 	 [$            !{ myaddr } ⇒ { DXchgPair_ι_flex_addr_ } ; 
                        (#{tip3_major_root}) ⇒ { DXchgPair_ι_tip3_major_root_ } ; 
                        (#{tip3_minor_root}) ⇒ { DXchgPair_ι_tip3_minor_root_ } ; 
                                          0  ⇒ { DXchgPair_ι_min_amount_ } ; 
          [#{0%Z} , 0] ⇒ { DXchgPair_ι_notify_addr_ }  
                   $] ; { _ } }} . 
 	 	 refine {{ new 'std_addr : uint256 @ "std_addr" := 
           second ( prepare_xchg_pair_state_init_and_addr_ ( !{ pair_data } , _xchg_pair_code_ -> get () ) ); { _ } }} . 
 	 	 refine {{ return_ [ _workchain_id_ , !{ std_addr } ] }} . 
 Defined . 

 
 Definition _fallback ( msg :  cell ) 
                      ( msg_body :  ( slice ) ) : UExpression uint false . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 

 Definition prepare_flex_state_init_and_addr ( flex_data :  (ContractLRecord ) ) 
                                             ( flex_code :  cell ) 
                    : UExpression ( StateInitLRecord * uint256 ) false . 
 	 	 refine {{ new 'flex_data_cl : cell @ "flex_data_cl" :=
              prepare_persistent_data_ ( {} (* flex_replay_protection_t::init ()*) , #{flex_data} ) ; { _ } }} . 
 	 	 refine {{ new 'flex_init : StateInitLRecord @ "flex_init" := 
             [ {} , {} , (#{flex_code}) -> set () , (!{flex_data_cl}) -> set () , {} ] ; { _ } }} . 
 	 	 refine {{ new 'flex_init_cl : cell @ "flex_init_cl" := 
                       build ( σ !{ flex_init } ) -> make_cell () ; { _ } }} . 
 	 	 refine {{ return_ [ !{ flex_init } , tvm_hash ( !{flex_init_cl} )  ] }} . 
 Defined . 

 
 Definition prepare_internal_wallet_state_init_and_addr 
( name :  ( XString ) ) 
( symbol :  ( XString ) )
 ( decimals :  uint8 )
 ( root_public_key :  uint256 )
 ( wallet_public_key :  uint256 ) 
( root_address : address ) 
( owner_address :  ( optional address ) ) 
( code :  cell ) 
( workchain_id :  int ) 
: UExpression ( StateInitLRecord * uint256 ) false . 
 	 	 refine {{ new 'wallet_data : ( TONTokenWalletClassTypesModule.DTONTokenWalletInternalLRecord ) @ "wallet_data" := 
                 [ #{name} , #{symbol} , #{decimals} , 0 , #{root_public_key} , 
                   #{wallet_public_key} , #{root_address} , #{owner_address} , 
                   {} , #{code} , #{workchain_id} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_data_cl : cell @ "wallet_data_cl" := 
               prepare_persistent_data_ ( {} , !{wallet_data} ) ; { _ } }} . 
 	 	 refine {{ new 'wallet_init : StateInitLRecord @ "wallet_init" := 
              [ {} , {} , (#{code}) -> set () , (!{wallet_data_cl}) -> set () , {} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_init_cl : cell @ "wallet_init_cl" := 
                      build ( σ !{ wallet_init } ) -> make_cell () ; { _ } }} . 
 	 	 refine {{ return_ [ !{ wallet_init } ,  tvm_hash ( !{wallet_init_cl} )  ] }} . 
Defined . 

End FuncsInternal.
End Funcs.








