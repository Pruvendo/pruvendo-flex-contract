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

Module Funcs (dc : ConstsTypesSig XTypesModule StateMonadModule) . 
 
Module Export FuncNotationsModuleForFuncs := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.Cpp.tvmNotationsModule.

Module FuncsInternal <: SpecModuleForFuncNotations.SpecSig. 
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.

Definition onlyOwner {X b}`{XDefault X} (e:UExpression X b) : UExpression X true .
   refine {{ require_ ( (tvm_pubkey() != 0) && (tvm_pubkey() == msg.pubkey()), 1 ) ; { _ } }} .
   refine {{ tvm_accept(); {e} }}.
Defined .

Definition Flex_Ф_constructor ( deployer_pubkey : uint256 ) 
( transfer_tip3 : uint128 ) ( return_ownership : uint128 )
 ( trading_pair_deploy : uint128 ) ( order_answer : uint128 ) 
( process_queue : uint128 ) ( send_notify : uint128 )
 ( deals_limit : uint8 ) ( notify_addr : XAddress ) : UExpression PhantomType false . 
         refine {{ deployer_pubkey : ( uint256 ) @ "deployer_pubkey" ; { _ } }} . 
         refine {{ transfer_tip3 : ( uint128 ) @ "transfer_tip3" ; { _ } }} . 
         refine {{ return_ownership : ( uint128 ) @ "return_ownership" ; { _ } }} . 
         refine {{ trading_pair_deploy : ( uint128 ) @ "trading_pair_deploy" ; { _ } }} . 
         refine {{ order_answer : ( uint128 ) @ "order_answer" ; { _ } }} . 
         refine {{ process_queue : ( uint128 ) @ "process_queue" ; { _ } }} . 
         refine {{ send_notify : ( uint128 ) @ "send_notify" ; { _ } }} . 
         refine {{ deals_limit : ( uint8 ) @ "deals_limit" ; { _ } }} . 
         refine {{ notify_addr : ( XAddress ) @ "notify_addr" ; { _ } }} . 
         refine {{ Flex.deployer_pubkey_ := !{ deployer_pubkey } ; { _ } }} . 
         refine {{ Flex.deals_limit_ := !{ deals_limit } ; { _ } }} . 
         refine {{ Flex.notify_addr_ := !{ notify_addr } ; { _ } }} . 
         refine {{ Flex.tons_cfg_ := {} (* { !{ transfer_tip3 } , !{ return_ownership } , !{ trading_pair_deploy } , !{ order_answer } , !{ process_queue } , !{ send_notify } } *) }} . 
 Defined . 
 
 
 Definition Flex_Ф_setPairCode ( code : XCell ) : UExpression PhantomType true . 
         refine {{ code : ( XCell ) @ "code" ; { _ } }} . 
         refine {{ require_ ( ( ~ TRUE (* Flex.pair_code_ *) ) , error_code::cant_override_code ) ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == Flex.deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
(*  	 	 refine {{ tvm_accept () ; { _ } }} .  *)
         refine {{ require_ ( (* ( code.ctos ( ) . srefs ( ) *) 1 == 1 (* 2 *) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
         refine {{ Flex.pair_code_ := {} (* builder ( ) . stslice ( code ^^ XCell:ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( )  *) }} . 
 Defined . 
 
 
 Definition Flex_Ф_setXchgPairCode ( code : XCell ) : UExpression PhantomType true . 
         refine {{ code : ( XCell ) @ "code" ; { _ } }} . 
         refine {{ require_ ( TRUE (* ~ Flex.xchg_pair_code_ *) , error_code::cant_override_code ) ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == Flex.deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
(*  	 	 refine {{ tvm_accept () ; { _ } }} .  *)
         refine {{ require_ ( (* ( code.ctos ( ) . srefs ( ) == 2 )  *) 1 == 1 , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
         refine {{ Flex.xchg_pair_code_ := {} (* builder ( ) . stslice ( code.ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *)  }} . 
 Defined . 
 
 
 Definition Flex_Ф_setPriceCode ( code : XCell ) : UExpression PhantomType true . 
         refine {{ code : ( XCell ) @ "code" ; { _ } }} . 
         refine {{ require_ ( ( ~ TRUE (* Flex.price_code_ *) ) , error_code::cant_override_code ) ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == Flex.deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
(*  	 	 refine {{ tvm_accept () ; { _ } }} .  *)
         refine {{ Flex.price_code_ ->set !{ code }  }} . 
 Defined . 
 
 
 Definition Flex_Ф_setXchgPriceCode ( code : XCell ) : UExpression PhantomType true . 
         refine {{ code : ( XCell ) @ "code" ; { _ } }} . 
         refine {{ require_ ( ( ~ TRUE (* Flex.xchg_price_code_ *) ) , error_code::cant_override_code ) ; { _ } }} . 
         refine {{ require_ ( ( msg.pubkey () == Flex.deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
(*  	 	 refine {{ tvm_accept () ; { _ } }} .  *)
         refine {{ Flex.xchg_price_code_ ->set !{ code } }} . 
 Defined . 
 
 
 Definition Flex_Ф_isFullyInitialized : UExpression XBool false . 
         refine {{ return_ {} (* Flex.pair_code_ && Flex.price_code_ && Flex.xchg_pair_code_ && Flex.xchg_price_code_ *) }} . 
 Defined . 
 
 Definition Flex_Ф_getTonsCfg : UExpression TonsConfigStateLRecord false . 
         refine {{ return_ Flex.tons_cfg_ }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getTradingPairCode : UExpression XCell false (* true *) . 
         refine {{ return_ {} (* (Flex.pair_code_ ->get) *) }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getXchgPairCode : UExpression XCell false . 
         refine {{ return_ {} (* (Flex.xchg_pair_code_ ->get) *) }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getSellPriceCode ( tip3_addr : XAddress ) : UExpression XCell true . 
         refine {{ tip3_addr : ( XAddress ) @ "tip3_addr" ; { _ } }} . 
         refine {{ require_ ( ( (* Flex.price_code_ - > ctos ( ) . srefs ( ) == 2 *) 1 == 1 ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
         refine {{ (* new *) salt : ( XCell ) @"salt" ; { _ } }} . 
         refine {{ { salt } := {} (* builder ( ) . stslice ( tvm_myaddr ( ) ) . stslice ( tip3_addr ^^ XAddress:sl ( ) ) . endc ( ) *) ; { _ } }} . 
         refine {{ return_ {} (* builder ( ) . stslice ( price_code_ - > ctos ( ) ) . stref ( !{ salt } ) . endc ( ) *) }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getXchgPriceCode ( tip3_addr1 : XAddress ) ( tip3_addr2 : XAddress ) : UExpression XCell true . 
         refine {{ tip3_addr1 : ( XAddress ) @ "tip3_addr1" ; { _ } }} . 
         refine {{ tip3_addr2 : ( XAddress ) @ "tip3_addr2" ; { _ } }} . 
         refine {{ require_ ( ( (* Flex.price_code_ - > ctos ( ) . srefs ( ) == 2 *) 1 == 1 ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
         refine {{ (* new *) keys : ( XAddress * XAddress ) @ "keys" ; { _ } }} . 
         refine {{ { keys } := {} (* [ !{ tip3_addr1 } , !{ tip3_addr2 } ] *) ; { _ } }} . 
         refine {{ return_ {} (* builder ( ) . stslice ( xchg_price_code_ - > ctos ( ) ) . stref ( build ( !{ keys } ) . endc ( ) ) . endc ( )  *) }} . 
 Defined . 
 
 
 Definition Flex_Ф_getSellTradingPair ( tip3_root : XAddress ) : UExpression XAddress false . 
         refine {{ tip3_root : ( XAddress ) @ "tip3_root" ; { _ } }} . 
         refine {{ (* new *) myaddr : ( XAddress ) @ "myaddr" ; { _ } }} . 
         refine {{ { myaddr } := (* tvm_myaddr *) tvm_myaddr () ; { _ } }} . 
         refine {{ (* new *) pair_data : ( TradingPairStateLRecord ) @ "pair_data" ; { _ } }} . 
         refine {{ { pair_data } := {} (* NEW { . flex_addr_ = myaddr , . tip3_root_ = tip3_root , . min_amount_ = uint128 ( 0 ) } *) ; { _ } }} . 
         refine {{ (* new *) std_addr : ( StateInitStateLRecord * uint256 ) @ "std_addr" ; { _ } }} . 
         refine {{ { std_addr } := {} (* prepare_trading_pair_state_init_and_addr ( !{ pair_data } , Flex.pair_code_ ->get ) ->second *) ; { _ } }} . 
         refine {{ (* new *) workchain_id : ( uint (* auto *) ) @ "workchain_id" ; { _ } }} . 
         refine {{ { workchain_id } := {} (* Std :: get < addr_std > ( myaddr ^^ address:val ( ) ) . workchain_id *) ; { _ } }} . 
         refine {{ return_ {} (* Address :: make_std ( !{ workchain_id } , !{ std_addr } ) *) }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getXchgTradingPair ( tip3_major_root : XAddress ) ( tip3_minor_root : XAddress ) : UExpression XAddress false . 
         refine {{ tip3_major_root : ( XAddress ) @ "tip3_major_root" ; { _ } }} . 
         refine {{ tip3_minor_root : ( XAddress ) @ "tip3_minor_root" ; { _ } }} . 
         refine {{ (* new *) myaddr : ( XAddress ) @ "myaddr" ; { _ } }} . 
         refine {{ { myaddr } := (* tvm_myaddr *) tvm_myaddr () ; { _ } }} . 
         refine {{ (* new *) pair_data : ( XchgPairStateLRecord ) @ "pair_data" ; { _ } }} . 
         refine {{ { pair_data } := {} (* NEW { . flex_addr_ = myaddr , . tip3_major_root_ = tip3_major_root , . tip3_minor_root_ = tip3_minor_root , . min_amount_ = uint128 ( 0 ) } *) ; { _ } }} . 
         refine {{ (* new *) std_addr : ( uint (* auto *) ) @ "std_addr" ; { _ } }} . 
         refine {{ { std_addr } := {} (* prepare_xchg_pair_state_init_and_addr ( !{ pair_data } , Flex.xchg_pair_code_ ->get ) ->second *) ; { _ } }} . 
         refine {{ (* new *) workchain_id : ( uint (* auto *) ) @ "workchain_id" ; { _ } }} . 
         refine {{ { workchain_id } := {} (* Std :: get < addr_std > ( myaddr ^^ address:val ( ) ) . workchain_id *) ; { _ } }} . 
         refine {{ return_ {} (* Address :: make_std ( !{ workchain_id } , !{ std_addr } ) *) }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getDealsLimit : UExpression uint8 false . 
         refine {{ return_ Flex.deals_limit_ }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getNotifyAddr : UExpression XAddress false . 
         refine {{ return_ Flex.notify_addr_ }} . 
 Defined . 
 
 
 
 Definition Flex_Ф__fallback ( _ : XCell ) : UExpression uint false . 
         refine {{ return_ 0 }} . 
 Defined . 



End FuncsInternal.
End Funcs.








