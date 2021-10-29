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

Require Import UrsusTVM.tvmFunc.
Require Import UrsusTVM.tvmNotations.

Require Import Project.CommonConstSig.
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.Flex.Ledger.
Require Import Contracts.Flex.Functions.FuncSig.
Require Import Contracts.Flex.Functions.FuncNotations.
Require Import Contracts.Flex.Interface.

(*this elpi code move to the Ursus lib afterwards*)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 10.


Elpi Command AddLocalState.

Elpi Accumulate lp:{{

main [Name , Term, LocalStateFieldT] :-
  trm TrmInternal = Term,
  trm LocalStateField = LocalStateFieldT,
  str NameStr = Name,
  N is NameStr ^ "_j",
  coq.env.add-axiom N  (app [LocalStateField , TrmInternal]) _ , 
  coq.locate  N GR, 
  coq.TC.declare-instance GR 0.
  /* coq.say TrmInternal. */
main _ :- coq.error "usage: AddLocalState <name> <term> <LocalStateField>".

}}.

Elpi Typecheck.
Elpi Export AddLocalState.

Module Funcs (dc : ConstsTypesSig XTypesModule StateMonadModule) .

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

Export SpecModuleForFuncNotations(* ForFuncs *).tvmNotationsModule.

Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Local Notation UE := (UExpression _ _)(only parsing).
Local Notation UEf := (UExpression _ false)(only parsing).
Local Notation UEt := (UExpression _ true)(only parsing).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
Notation " 'private' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.


(* Set Typeclasses Debug.
Check || 1 ||.
About IfElseExpression.
Arguments IfElseExpression {_} {_} {_} {_} {_} {_} {_} {_} {R} (* & {_} *) {B} {bb} {xb} {yb} & {_} {_} _ _ _ .
Set Typeclasses Iterative Deepening.
Check {{  if m_value then { {_: UEf} } else { {_: UEf} } }}. 

About IfElseExpression. *)

Definition constructor 
( deployer_pubkey : URValue XInteger256 false) 
( ownership_description : URValue XString false ) 
( owner_address : URValue ( XMaybe XAddress ) false ) 
( transfer_tip3 : URValue ( XInteger128) false  ) 
( return_ownership : URValue ( XInteger128) false  ) 
( trading_pair_deploy : URValue ( XInteger128) false  ) 
( order_answer : URValue ( XInteger128) false  ) 
( process_queue : URValue ( XInteger128) false  ) 
( send_notify : URValue ( XInteger128) false  ) 
( deals_limit : URValue ( XInteger8) false  ) : UExpression PhantomType false . 
 	 	 refine {{ _deployer_pubkey_ := { deployer_pubkey } ; { _ } }} . 
 	 	 refine {{ _ownership_description_ := { ownership_description } ; { _ } }} . 
 	 	 refine {{ _owner_address_ := { owner_address } ; { _ } }} . 
 	 	 refine {{ _deals_limit_ := { deals_limit } ; { _ } }} . 
 	 	 refine {{ _tons_cfg_ := [$ 
                 { transfer_tip3 } ⇒ {TonsConfig_ι_transfer_tip3} ; 
              { return_ownership } ⇒ {TonsConfig_ι_return_ownership} ;  
           { trading_pair_deploy } ⇒ {TonsConfig_ι_trading_pair_deploy} ;  
                  { order_answer } ⇒ {TonsConfig_ι_order_answer} ; 
                 { process_queue } ⇒ {TonsConfig_ι_process_queue} ;  
                   { send_notify } ⇒ {TonsConfig_ι_send_notify} 
                             $] 
      }} . 
 Defined . 

Definition constructor_left {R b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 }
( deployer_pubkey : URValue XInteger256 b0) 
( ownership_description : URValue XString b1) 
( owner_address : URValue (XMaybe XAddress) b2)
( transfer_tip3 : URValue XInteger128 b3) 
( return_ownership : URValue XInteger128 b4) 
( trading_pair_deploy : URValue XInteger128 b5) 
( order_answer : URValue XInteger128 b6)
( process_queue : URValue XInteger8 b7) 
( send_notify : URValue XAddress b8)
( deals_limit : URValue XAddress b9) :  UExpression R 
((orb(orb(orb(orb(orb(orb(orb(orb(orb b9 b8)b7)b6)b5)b4)b3)b2)b1)b0)) :=

wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ10) 
constructor 
deployer_pubkey
ownership_description
owner_address
transfer_tip3 
return_ownership 
trading_pair_deploy 
order_answer
process_queue 
send_notify
deals_limit ).

Notation " 'constructor_' '(' x0 ',' x1 ',' x2 ',' x3 ',' x4 ',' x5 ',' x6 ',' x7 ',' x8 ',' x9 ')' " :=
( constructor_left x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 )
(in custom ULValue at level 0 , 
x0 custom URValue at level 0,
x1 custom URValue at level 0,
x2 custom URValue at level 0,
x3 custom URValue at level 0,
x4 custom URValue at level 0,
x5 custom URValue at level 0,
x6 custom URValue at level 0,
x7 custom URValue at level 0,
x8 custom URValue at level 0,
x9 custom URValue at level 0) : ursus_scope.

 Definition setPairCode ( code : URValue XCell false ) : UExpression PhantomType true . 
  	 refine {{ require_ ( ( ~ _pair_code_ ) , error_code::cant_override_code ) ; { _ } }} .
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) ,error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ require_ ( ( {code} -> to_slice () ) -> refs () == #{2} , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ _pair_code_ := {} (* builder ( ) . stslice ( code . ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 

Definition setPairCode_left {R b1} (x: URValue XCell b1 ) : UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) setPairCode x).    

Notation " 'setPairCode_' '(' x ')' " := (setPairCode_left x)  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.



 Definition setXchgPairCode ( code : URValue XCell false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _xchg_pair_code_ ) , error_code::cant_override_code ) ; { _ } }} .
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ require_ ( ( ( {code} -> to_slice () ) -> refs () == #{2} ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ _xchg_pair_code_ := {} (* builder ( ) . stslice ( code . ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 

Definition setXchgPairCode_left {R b1} (x: URValue XCell b1 ) : UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) setXchgPairCode x).    

Notation " 'setXchgPairCode_' '(' x ')' " := (setXchgPairCode x)  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.

 Definition setPriceCode ( code : URValue XCell false ) : UExpression PhantomType true . 
 	 	 refine {{ require_ ( ( ~ _price_code_ ) , error_code::cant_override_code ) ; { _ } }} .
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _price_code_ ->set ( { code } ) }} . 
 Defined .

Definition setPriceCode_left {R b1} (x: URValue XCell b1 ) : UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) setPriceCode x).    

Notation " 'setPriceCode_' '(' x ')' " := (setPriceCode_left x)  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.


 Definition setXchgPriceCode ( code : URValue XCell false ) : UExpression PhantomType true . 
	 	 refine {{ require_ ( ( ~ _xchg_price_code_ ) ,  error_code::cant_override_code  ) ; { _ } }} .
 	 	 refine {{ require_ ( ( msg.pubkey () == _deployer_pubkey_ ) ,  error_code::sender_is_not_deployer  ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ _xchg_price_code_ ->set ( { code } ) }} . 
 Defined . 

Definition setXchgPriceCode_left {R b1} (x: URValue XCell b1 ) : UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) setXchgPriceCode x).    

Notation " 'setXchgPriceCode_' '(' x ')' " := (setXchgPriceCode_left x)  
   (in custom ULValue at level 0 , x custom URValue at level 0) : ursus_scope.

 Definition transfer_INTERNAL ( tto : URValue XAddress false ) ( tons : URValue XInteger128 false ) : UExpression PhantomType true . 
 	 	 refine {{ new 'internal_ownership : ( XBool ) @ "internal_ownership" := {} ; { _ } }} . 
 	 	 refine {{ { internal_ownership } := {} (* !! _owner_address_ *)  ; { _ } }} . 
 	 	 refine {{ require_ ( ( !{ internal_ownership } && ( {} (* int.sender () *) ==  _owner_address_ -> get_default () ) ) , error_code::message_sender_is_not_my_owner ) ;{ _ } }} . 
 	 	 refine {{ tvm.accept () (* ; { _ } }} . 
 	 	 refine {{ tvm.transfer ( !{tto} , !{tons} , TRUE ) *) }} . 
 Defined . 

Definition transfer_INTERNAL_left {R b1 b2} 
(x0: URValue XAddress b1 ) 
(x1: URValue XInteger128 b2 )
: UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) transfer_INTERNAL x0 x1 ).    

Notation " 'transfer_INTERNAL_' '(' x0 ',' x1 ')' " := (transfer_INTERNAL_left x0 x1 )  
   (in custom ULValue at level 0 , 
x0 custom URValue at level 0 ,
x1 custom URValue at level 0) : ursus_scope.

 Definition transfer_EXTERNAL ( tto : URValue XAddress false ) ( tons : URValue XInteger128 false ) : UExpression PhantomType true . 
 	 	 refine {{ new 'internal_ownership : ( XBool ) @ "internal_ownership" := {} ; { _ } }} . 
 	 	 refine {{ { internal_ownership } := {} (*  ~~ _owner_address_ *) ; { _ } }} . 
 	 	 refine {{ require_ ( ( ( ~ !{ internal_ownership } ) && (msg.pubkey () == _deployer_pubkey_ ) ) , error_code::message_sender_is_not_my_owner ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () (* ; { _ } }} . 
 	 	 refine {{ tvm.transfer ( to , tons . get ( ) , true )  *) }} . 
 Defined . 

Definition transfer_EXTERNAL_left {R b1 b2} 
(x0: URValue XAddress b1 ) 
(x1: URValue XInteger128 b2 )
: UExpression R true :=
   wrapULExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) transfer_EXTERNAL x0 x1 ).    

Notation " 'transfer_EXTERNAL_' '(' x0 ',' x1 ')' " := (transfer_EXTERNAL_left x0 x1 )  
   (in custom ULValue at level 0 , 
x0 custom URValue at level 0 ,
x1 custom URValue at level 0) : ursus_scope.


 Definition isFullyInitialized : UExpression XBool false . 
 	 	 refine {{ return_ {} (*  _pair_code_ && _price_code_ && _xchg_pair_code_ && _xchg_price_code_ *) }} . 
 Defined . 

Definition isFullyInitialized_right : URValue XBool false :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) isFullyInitialized ).    

Notation " 'isFullyInitialized_' '(' ')' " := (isFullyInitialized_right )  
   (in custom URValue at level 0 ) : ursus_scope.

 Definition getTonsCfg : UExpression TonsConfigLRecord false . 
 	 	 refine {{ return_ _tons_cfg_ }} . 
 Defined . 

Definition getTonsCfg_right : URValue TonsConfigLRecord false :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getTonsCfg ).    

Notation " 'getTonsCfg_' '(' ')' " := ( getTonsCfg_right )  
   (in custom URValue at level 0 ) : ursus_scope.


 Definition getTradingPairCode : UExpression XCell false . 
 	 	 refine {{ return_ _pair_code_ ->get_default () }} . 
 Defined .

Definition getTradingPairCode_right : URValue XCell false := (*TODO: maybe true*)
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getTradingPairCode ).    

Notation " 'getTradingPairCode_' '(' ')' " := ( getTradingPairCode_right )  
   (in custom URValue at level 0 ) : ursus_scope.


 Definition getXchgPairCode : UExpression XCell false . 
 	 	 refine {{ return_ _xchg_pair_code_ ->get_default () }} . 
 Defined . 

Definition getXchgPairCode_right : URValue XCell false := (*TODO: maybe true*)
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getXchgPairCode ).    

Notation " 'getXchgPairCode_' '(' ')' " := ( getXchgPairCode_right )  
   (in custom URValue at level 0 ) : ursus_scope.



 Definition getSellPriceCode ( tip3_addr : URValue XAddress false ) : UExpression XCell true . 
 	 	 refine {{ require_ ( ( ( ( ( _price_code_ -> get_default () )  -> to_slice () ) -> refs () ) == #{2} ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ new 'salt : ( XCell ) @ "salt" := {} ; { _ } }} . 
 	 	 refine {{ { salt } := {} (* builder ( ) . stslice ( tvm_myaddr ( ) ) . stslice ( tip3_addr . sl ( ) ) . endc ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ {} (* builder ( ) . stslice ( price_code_ - > ctos ( ) ) . stref ( !{ salt } ) . endc ( ) *) }} . 
 Defined . 
 
Definition getSellPriceCode_right {b1} (x: URValue XAddress b1 ) : URValue XCell true :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) getSellPriceCode x).    

Notation " 'getSellPriceCode_' '(' x ')' " := (getSellPriceCode_right x)  
   (in custom URValue at level 0 , x custom URValue at level 0) : ursus_scope.


 Definition getXchgPriceCode ( tip3_addr1 : URValue XAddress false ) ( tip3_addr2 : URValue XAddress false ) : UExpression XCell true . 
 	 	 refine {{ require_ ( ( ( ( ( _price_code_ -> get_default () )  -> to_slice () ) -> refs () ) == #{2} ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ new 'keys : ( XAddress # XAddress )%sol @ "keys" := {} ; { _ } }} . 
 	 	 refine {{ { keys } := [ { tip3_addr1 } , { tip3_addr2 } ] ; { _ } }} . 
 	 	 refine {{ return_ {} (* builder ( ) . stslice ( xchg_price_code_ - > ctos ( ) ) . stref ( build ( !{ keys } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 
 
Definition getXchgPriceCode_right {b1 b2} 
(x0: URValue XAddress b1 ) 
(x1: URValue XAddress b2 ) 
: URValue XCell true :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) getXchgPriceCode x0 x1).    

Notation " 'getXchgPriceCode_' '(' x0 ',' x1 ')' " := (getXchgPriceCode_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.


(* std::pair<StateInit, uint256> prepare_trading_pair_state_init_and_addr(DTradingPair pair_data, cell pair_code) {
  cell pair_data_cl = prepare_persistent_data<ITradingPair, void, DTradingPair>({}, pair_data);
  StateInit pair_init {
    /*split_depth*/{}, /*special*/{},
    pair_code, pair_data_cl, /*library*/{}
  };
  cell pair_init_cl = build(pair_init).make_cell();
  return { pair_init, uint256(tvm_hash(pair_init_cl)) };
} *)

Definition prepare_trading_pair_state_init_and_addr ( pair_data : URValue DTradingPairLRecord false) 
                                                    ( pair_code : URValue XCell false ) 
                           : UExpression (StateInitLRecord # XInteger256)%sol false .
 	 	 refine {{ new 'pair_data_cl : XCell @ "pair_data_cl" := {} 
                       (* prepare_persistent_data<ITradingPair, void, DTradingPair>({}, pair_data) *) ; { _ } }} .
 	 	 refine {{ new 'pair_init : StateInitLRecord @ "pair_init" :=
                   [$
                         {} ⇒ { StateInit_ι_split_depth } ;
                         {} ⇒ { StateInit_ι_special } ;
                         ( {pair_code} ) -> set () ⇒ {StateInit_ι_code} ;
                         ( !{pair_data_cl} ) -> set () ⇒ {StateInit_ι_data} ;
                         {} ⇒ {StateInit_ι_library}
                    $] ; { _ } }}.
 	 	 refine {{ new 'pair_init_cl : XCell @ "pair_init_cl" := {} (* build(pair_init).make_cell() *) ; { _ } }} .
 	 	 refine {{ return_ [ !{pair_init} , {} (* tvm_hash(pair_init_cl) *) ] }} .
Defined.

Definition prepare_trading_pair_state_init_and_addr_right {b1 b2} 
(x0: URValue DTradingPairLRecord b1 ) 
(x1: URValue XCell b2 ) 
: URValue (StateInitLRecord # XInteger256)%sol ( orb false (orb b2 b1) ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) prepare_trading_pair_state_init_and_addr x0 x1).    

Notation " 'prepare_trading_pair_state_init_and_addr_' '(' x0 ',' x1 ')' " := (prepare_trading_pair_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.


 Definition getSellTradingPair ( tip3_root : URValue XAddress false ) : UExpression XAddress false . 
 	 	 refine {{ new 'myaddr : ( XAddress ) @ "myaddr" := {} ; { _ } }} . 
 	 	 refine {{ { myaddr } := tvm.address () ; { _ } }} . 
 	 	 refine {{ new 'pair_data : ( DTradingPairLRecord ) @ "pair_data" := 
                      [$ !{ myaddr } ⇒ { DTradingPair_ι_flex_addr_ } ; 
                       { tip3_root } ⇒ { DTradingPair_ι_tip3_root_ } ; 
                                   0 ⇒ { DTradingPair_ι_min_amount_ } ; 
                                  0  ⇒ { DTradingPair_ι_notify_addr_ } 
                $] ; { _ } }} .
 	 	 refine {{ new 'std_addr : ( XInteger256 ) @ "std_addr" := {} ; { _ } }} . 
 	 	 refine {{ { std_addr } := 
        second ( prepare_trading_pair_state_init_and_addr_ ( !{ pair_data } , ( _pair_code_ -> get_default () ) ) ) ; { _ } }} . 
 	 	 refine {{ new 'workchain_id : ( addr_stdLRecord ) @ "workchain_id" := {} ; { _ } }} . 
 	 	 refine {{ { workchain_id } := {} (* std :: get < addr_std > ( myaddr . val ( ) ) . workchain_id *) ; { _ } }} . 
 	 	 refine {{ return_ {} (* address :: make_std ( !{ workchain_id } , !{ std_addr } ) *) }} . 
 Defined . 
 
Definition getSellTradingPair_right {b1} (x: URValue XAddress b1 ) : URValue XAddress b1 :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) getSellTradingPair x).    

Notation " 'getSellTradingPair_' '(' x ')' " := (getSellTradingPair_right x)  
   (in custom URValue at level 0 , x custom URValue at level 0) : ursus_scope.

Definition prepare_xchg_pair_state_init_and_addr ( pair_data : URValue DXchgPairLRecord false) 
                                                    ( pair_code : URValue XCell false ) 
                           : UExpression (StateInitLRecord # XInteger256)%sol false .
 	 	 refine {{ new 'pair_data_cl : XCell @ "pair_data_cl" := {} 
                       (* prepare_persistent_data<IXchgPair, void, DXchgPair>({}, pair_data) *) ; { _ } }} .
 	 	 refine {{ new 'pair_init : StateInitLRecord @ "pair_init" :=
                   [$
                         {} ⇒ { StateInit_ι_split_depth } ;
                         {} ⇒ { StateInit_ι_special } ;
                         ( {pair_code} ) -> set () ⇒ {StateInit_ι_code} ;
                         ( !{pair_data_cl} ) -> set () ⇒ {StateInit_ι_data} ;
                         {} ⇒ {StateInit_ι_library}
                    $] ; { _ } }}.
 	 	 refine {{ new 'pair_init_cl : XCell @ "pair_init_cl" := {} (* build(pair_init).make_cell() *) ; { _ } }} .
 	 	 refine {{ return_ [ !{pair_init} , {} (* tvm_hash(pair_init_cl) *) ] }} .
Defined.

Definition prepare_xchg_pair_state_init_and_addr_right {b1 b2} 
(x0: URValue DXchgPairLRecord b1 ) 
(x1: URValue XCell b2 ) 
: URValue (StateInitLRecord # XInteger256)%sol ( orb false (orb b2 b1) ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) prepare_xchg_pair_state_init_and_addr x0 x1).    

Notation " 'prepare_xchg_pair_state_init_and_addr_' '(' x0 ',' x1 ')' " := (prepare_xchg_pair_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.


 Definition getXchgTradingPair ( tip3_major_root : URValue XAddress false ) ( tip3_minor_root : URValue XAddress false ) : UExpression XAddress false . 
 	 	 refine {{ new 'myaddr : ( XAddress ) @ "myaddr" := {} ; { _ } }} . 
 	 	 refine {{ { myaddr } := tvm.address () ; { _ } }} . 
 	 	 refine {{ new 'pair_data : ( DXchgPairLRecord ) @ "pair_data" := 
                       [$  !{ myaddr } ⇒ { DXchgPair_ι_flex_addr_ } ;
                   { tip3_major_root } ⇒ { DXchgPair_ι_tip3_major_root_ } ; 
                   { tip3_minor_root } ⇒ { DXchgPair_ι_tip3_minor_root_ } ; 
                                     0 ⇒ { DXchgPair_ι_min_amount_ } ; 
                                     0 ⇒ { DXchgPair_ι_notify_addr_ }  
               $] ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( XInteger256 ) @ "std_addr" := {} ; { _ } }} . 
 	 	 refine {{ { std_addr } := 
                      second ( prepare_xchg_pair_state_init_and_addr_ ( !{ pair_data } , 
                                ( _xchg_pair_code_ -> get_default () ) ) ) ; { _ } }} . 

 	 	 refine {{ new 'workchain_id : ( addr_stdLRecord ) @ "workchain_id" := {} ; { _ } }} . 
 	 	 refine {{ { workchain_id } := {} (* std :: get < addr_std > ( myaddr . val ( ) ) . workchain_id *) ; { _ } }} . 
 	 	 refine {{ return_ {} (* address :: make_std ( !{ workchain_id } , !{ std_addr } ) *) }} . 
 Defined . 

Definition getXchgTradingPair_right {b1 b2} 
(x0: URValue XAddress b1 ) 
(x1: URValue XAddress b2 ) 
: URValue XAddress (orb b2 b1) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) getXchgTradingPair x0 x1).    

Notation " 'getXchgTradingPair_' '(' x0 ',' x1 ')' " := (getXchgTradingPair_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.


 Definition getDealsLimit : UExpression XInteger8 false . 
 	 	 refine {{ return_ _deals_limit_ }} . 
 Defined .

Definition getDealsLimit_right : URValue XInteger8 false := 
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getDealsLimit ).    

Notation " 'getDealsLimit_' '(' ')' " := ( getDealsLimit_right )  
   (in custom URValue at level 0 ) : ursus_scope.


 Definition getOwnershipInfo : UExpression FlexOwnershipInfoLRecord false . 
 	 	 refine {{ return_ [$ _deployer_pubkey_  ⇒ {FlexOwnershipInfo_ι_deployer_pubkey} ; 
                          _ownership_description_  ⇒ {FlexOwnershipInfo_ι_ownership_description} ; 
                          _owner_address_  ⇒ {FlexOwnershipInfo_ι_owner_contract} $] }} . 
 Defined . 
 
Definition getOwnershipInfo_right : URValue FlexOwnershipInfoLRecord false := 
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ0) getOwnershipInfo ).    

Notation " 'getOwnershipInfo_' '(' ')' " := ( getOwnershipInfo_right )  
   (in custom URValue at level 0 ) : ursus_scope.


 Definition _fallback ( msg : URValue XCell false ) ( msg_body : URValue XSlice false ) : UExpression XInteger false . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
Definition _fallback_right {b1 b2} 
(x0: URValue XCell b1 ) 
(x1: URValue XSlice b2 ) 
: URValue XInteger (orb b2 b1) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) _fallback x0 x1).    

Notation " '_fallback_' '(' x0 ',' x1 ')' " := (_fallback_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.


 Definition prepare_flex_state_init_and_addr ( flex_data : URValue ContractLRecord false ) 
                                             ( flex_code : URValue XCell false ) 
: UExpression ( StateInitLRecord # XInteger256 )%sol false . 
 	 	 refine {{ flex_data : ( ContractLRecord ) @ "flex_data" ; { _ } }} . 
 	 	 refine {{ flex_code : ( XCell ) @ "flex_code" ; { _ } }} . 
 	 	 refine {{ new 'flex_data_cl : ( XCell ) @ "flex_data_cl" := {} ; { _ } }} . 
 	 	 refine {{ { flex_data_cl } := {} (* prepare_persistent_data ( flex_replay_protection_t : : init ( ) , flex_data ) *) ; { _ } }} . 
 	 	 refine {{ new 'flex_init : ( StateInitLRecord ) @ "flex_init" := {} ; { _ } }} . 
 	 	 refine {{ { flex_init } := [$ {} ⇒ {StateInit_ι_split_depth} ; 
                                   {} ⇒ {StateInit_ι_special} ;
                            (!{flex_code}) -> set ()  ⇒ {StateInit_ι_code} ; 
                         ( !{flex_data_cl}) -> set () ⇒ {StateInit_ι_data} ;
                                   {} ⇒ {StateInit_ι_library} $] ; { _ } }} . 	 	 
     refine {{ new 'flex_init_cl : ( XCell ) @ "flex_init_cl" := {} ; { _ } }} . 
 	 	 refine {{ { flex_init_cl } := {} (* build ( !{ flex_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ flex_init } , {} (* tvm.hash ( !{ flex_init_cl } ) *) ] }} . 
 Defined . 

Definition prepare_flex_state_init_and_addr_right {b1 b2} 
(x0: URValue ContractLRecord b1 ) 
(x1: URValue XCell b2 ) 
: URValue ( StateInitLRecord # XInteger256 )%sol (orb b2 b1) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ2) prepare_flex_state_init_and_addr x0 x1).    

Notation " 'prepare_flex_state_init_and_addr_' '(' x0 ',' x1 ')' " := (prepare_flex_state_init_and_addr_right x0 x1)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0,
    x1 custom URValue at level 0) : ursus_scope.



End FuncsInternal.
End Funcs.








