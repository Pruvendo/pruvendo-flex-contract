Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 
Require Import Coq.Program.Equality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import List.
Import ListNotations.


Local Open Scope program_scope. 

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.StateMonad21. 
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.

Require Import UMLang.SolidityNotations2.
Require Import UMLang.ProofEnvironment2.

Require Import FLeXContractTypes.

Require Import FLeXClassSelf.

Require Import FLeXContractConsts.  
Require Import FLeXConstSig.
Require Import ZArith.

Require Import FLeXFuncNotations.
Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG26.

Require Import UrsusStdLib.stdNotations.
Require Import UrsusTVM.tvmNotations.

Module FLeXFuncsSelf (dc : FLeXConstsTypesSig XTypesModule StateMonadModule ).

Module Export FLeXFuncNotationsModule := FLeXFuncNotations XTypesModule StateMonadModule dc. 

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.


Existing Instance xbool_default.
Instance TvmCell_default : XDefault (TvmCell) := {
default := xStrNull}.
Existing Instance TvmCell_default.
Existing Instance phantom_default .

Definition FLeX_Ф_constructor ( deployer_pubkey : XInteger256 ) ( transfer_tip3 : XInteger128 ) ( return_ownership : XInteger128 ) ( trading_pair_deploy : XInteger128 ) ( order_answer : XInteger128 ) ( process_queue : XInteger128 ) ( send_notify : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( notify_addr : XAddress ) : UExpression PhantomType false . 
 	 	 refine {{ deployer_pubkey : ( XInteger256 ) @ "deployer_pubkey" ; { _ } }} . 
 	 	 refine {{ transfer_tip3 : ( XInteger128 ) @ "transfer_tip3" ; { _ } }} . 
 	 	 refine {{ return_ownership : ( XInteger128 ) @ "return_ownership" ; { _ } }} . 
 	 	 refine {{ trading_pair_deploy : ( XInteger128 ) @ "trading_pair_deploy" ; { _ } }} . 
 	 	 refine {{ order_answer : ( XInteger128 ) @ "order_answer" ; { _ } }} . 
 	 	 refine {{ process_queue : ( XInteger128 ) @ "process_queue" ; { _ } }} . 
 	 	 refine {{ send_notify : ( XInteger128 ) @ "send_notify" ; { _ } }} . 
 	 	 refine {{ min_amount : ( XInteger128 ) @ "min_amount" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ notify_addr : ( XAddress ) @ "notify_addr" ; { _ } }} . 
 	 	 refine {{ FLeX.deployer_pubkey_ := !{ deployer_pubkey } ; { _ } }} . 
 	 	 refine {{ FLeX.min_amount_ := !{ min_amount } ; { _ } }} . 
 	 	 refine {{ FLeX.deals_limit_ := !{ deals_limit } ; { _ } }} . 
 	 	 refine {{ FLeX.notify_addr_ := !{ notify_addr } ; { _ } }} . 
 	 	 refine {{ FLeX.tons_cfg_ := {} (* { !{ transfer_tip3 } , !{ return_ownership } , !{ trading_pair_deploy } , !{ order_answer } , !{ process_queue } , !{ send_notify } }  *) }} . 
 Defined . 
 
 
 
Locate "msg.pubkey ()".
Definition FLeX_Ф_setPairCode ( code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ code : ( TvmCell ) @ "code" ; { _ } }} .
 	 	 refine {{ require_ ( ~ ( FLeX_Ф_isFullyInitialized_ref_ ( ) ) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ require_ ( msg.pubkey () == FLeX.deployer_pubkey_ , error_code::sender_is_not_deployer ) ; { _ } }} . 
(*  	 	 refine {{ tvm_accept ( ) ; { _ } }} .  *)
     refine {{ FLeX.pair_code_->set !{ code }; { _ } }} .
all:cycle 1.
	 	 refine {{ require_(  ~TRUE (* FLeX.pair_code_  ->has_value *) , error_code::cant_override_code ) ; { _ } }} .
 	 	 refine {{ require_( TRUE (* code.ctos ( ) . srefs ( ) == 2 *) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ FLeX.pair_code_ := {} (* builder ( ) . stslice ( !{ code } . ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) }} . 
 Admitted . 
 
 (*begin*) 
 Definition FLeX_Ф_setPairCode_call  ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setPairCode_ref_' '(' code ')' " := 
 ( URResult ( FLeX_Ф_setPairCode_call 
 code )) 
 (in custom URValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_setXchgPairCode ( code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ code : ( TvmCell ) @ "code" ; { _ } }} . 
 	 	 refine {{ require_( ( ~ FLeX_Ф_isFullyInitialized_ref_ ( ) ) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ require_( ( VMState.msg_pubkey == FLeX.deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
(*  	 	 refine {{ tvm_accept ( ) ; { _ } }} .  *)
 	 	 refine {{ require_( TRUE (* ! FLeX.xchg_pair_code_  ->has_value *) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ require_( TRUE (* code.ctos ( ) . srefs ( ) == 2 *) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ FLeX.xchg_pair_code_ := {} (* builder ( ) . stslice ( !{ code } . ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) *) }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_setXchgPairCode_call  ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setXchgPairCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setXchgPairCode_ref_' '(' code ')' " := 
 ( URResult ( FLeX_Ф_setXchgPairCode_call 
 code )) 
 (in custom URValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_setPriceCode ( code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ code : ( TvmCell ) @ "code" ; { _ } }} . 
 	 	 refine {{ require_( ( ~ FLeX_Ф_isFullyInitialized_ref_ ( ) ) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ require_( ( VMState.msg_pubkey == FLeX.deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
(*  	 	 refine {{ tvm_accept ( ) ; { _ } }} .  *)
 	 	 refine {{ require_( TRUE (* ! FLeX.price_code_  ->has_value *) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ FLeX.price_code_ := {} (* ->set !{ code } *) }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_setPriceCode_call  ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setPriceCode_ref_' '(' code ')' " := 
 ( URResult ( FLeX_Ф_setPriceCode_call 
 code )) 
 (in custom URValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_setXchgPriceCode ( code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ code : ( TvmCell ) @ "code" ; { _ } }} . 
 	 	 refine {{ require_( ( ~ FLeX_Ф_isFullyInitialized_ref_ ( )  ) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ require_( ( VMState.msg_pubkey == FLeX.deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
(*  	 	 refine {{ tvm_accept ( ) ; { _ } }} .  *)
 	 	 refine {{ require_( TRUE (* ! FLeX.xchg_price_code_ ->has_value *) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ FLeX.xchg_price_code_ := {} (* ->set !{ code } *) }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_setXchgPriceCode_call  ( code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_setXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "code" }} code ) 
 . 
 Notation " 'FLeX_Ф_setXchgPriceCode_ref_' '(' code ')' " := 
 ( URResult ( FLeX_Ф_setXchgPriceCode_call 
 code )) 
 (in custom URValue at level 0 , code custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getTonsCfg : UExpression TonsConfig false . 
 	 	 refine {{ return_ FLeX.tons_cfg_ }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getTonsCfg_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getTonsCfg 
 . 
 Notation " 'FLeX_Ф_getTonsCfg_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getTonsCfg_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getTradingPairCode : UExpression ( XMaybe XInteger ) (* TvmCell *) false . 
 	 	 refine {{ return_ {} (*FLeX.pair_code_ ->hasValue*) }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getTradingPairCode_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getTradingPairCode 
 . 
 Notation " 'FLeX_Ф_getTradingPairCode_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getTradingPairCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getXchgPairCode : UExpression TvmCell false . 
 	 	 refine {{ return_ {} (*FLeX.xchg_pair_code_ ->get*) (*->get_default*) }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getXchgPairCode_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getXchgPairCode 
 . 
 Notation " 'FLeX_Ф_getXchgPairCode_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getXchgPairCode_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getSellPriceCode ( tip3_addr : XAddress ) : UExpression TvmCell true . 
 	 	 refine {{ tip3_addr : ( XAddress ) @ "tip3_addr" ; { _ } }} . 
 	 	 refine {{ require_( ( TRUE (* FLeX.price_code_ - > ctos ( ) . srefs ( ) == 2 *) ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ new 'salt : ( TvmCell ) @ "salt" := {} ; { _ } }} . 
 	 	      (* builder ( ) . stslice ( tvm_myaddr ( ) ) . stslice ( !{ tip3_addr } . sl ( ) ) . endc ( )  *) 
 	 	 refine {{ return_ {} (* builder ( ) . stslice ( FLeX.price_code_ - > ctos ( ) ) . stref ( !{ salt } ) . endc ( ) *) }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getSellPriceCode_call  ( tip3_addr : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_getSellPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr" }} tip3_addr ) 
 . 
 Notation " 'FLeX_Ф_getSellPriceCode_ref_' '(' tip3_addr ')' " := 
 ( URResult ( FLeX_Ф_getSellPriceCode_call 
 tip3_addr )) 
 (in custom URValue at level 0 , tip3_addr custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getXchgPriceCode ( tip3_addr1 : XAddress ) ( tip3_addr2 : XAddress ) : UExpression TvmCell true . 
 	 	 refine {{ tip3_addr1 : ( XAddress ) @ "tip3_addr1" ; { _ } }} . 
 	 	 refine {{ tip3_addr2 : ( XAddress ) @ "tip3_addr2" ; { _ } }} . 
 	 	 refine {{ require_( TRUE (* FLeX.price_code_ - > ctos ( ) . srefs ( ) == 2 *) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
  	 (* refine {{ new 'keys : ( XProd XAddress XAddress ) @ "keys" := {} ; { _ } }} .  *)
 	 	          (* [ !{ tip3_addr1 } , !{ tip3_addr2 } ] *) 
  	 	 
     refine {{ return_ {} (* builder ( ) . stslice ( FLeX.xchg_price_code_ - > ctos ( ) ) . stref ( build ( !{ keys } ) . endc ( ) ) . endc ( )  *) }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getXchgPriceCode_call  ( tip3_addr1 : URValue XAddress false ) ( tip3_addr2 : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) FLeX_Ф_getXchgPriceCode 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr1" }} tip3_addr1 ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_addr2" }} tip3_addr2 ) 
 . 
 Notation " 'FLeX_Ф_getXchgPriceCode_ref_' '(' tip3_addr1 tip3_addr2 ')' " := 
 ( URResult ( FLeX_Ф_getXchgPriceCode_call 
 tip3_addr1 tip3_addr2 )) 
 (in custom URValue at level 0 , tip3_addr1 custom URValue at level 0 
 , tip3_addr2 custom ULValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition Ф_prepare_trading_pair_state_init_and_addr ( pair_data : TradingPair ) ( pair_code : TvmCell ) : UExpression ( XInteger (* StateInit *) # XInteger256 )%sol false . 
 	 	 refine {{ pair_data : ( TradingPair ) @ "pair_data" ; { _ } }} . 
 	 	 refine {{ pair_code : ( TvmCell ) @ "pair_code" ; { _ } }} . 
 	 	 refine {{ pair_data_cl : ( TvmCell ) @ "pair_data_cl" ; { _ } }} . 
 	 	 refine {{ { pair_data_cl } := {} (* prepare_persistent_data_ref ( {} , !{pair_data} ) *) ; { _ } }} . 
 	 	 refine {{ pair_init : ( XInteger (* StateInit *) ) @ "pair_init" ; { _ } }} . 
 	 	 refine {{ { pair_init } := {} (* new { { } , { } , pair_code , pair_data_cl , { } } *) ; { _ } }} . 
 	 	 refine {{ new 'pair_init_cl : ( TvmCell ) @ "pair_init_cl" := {} ; { _ } }} . 
 	 	        (* build ( !{ pair_init } ) . make_cell ( ) *) 
 	 	 refine {{ return_ {} (* [ !{ pair_init } , tvm_hash ( pair_init_cl ) ] *) }} . 
 Defined . 
 
 (*begin*) 
 Definition Ф_prepare_trading_pair_state_init_and_addr_call  ( pair_data : URValue TradingPair false ) ( pair_code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_trading_pair_state_init_and_addr 
 ( SimpleLedgerableArg URValue {{ Λ "pair_data" }} pair_data ) 
 ( SimpleLedgerableArg URValue {{ Λ "pair_code" }} pair_code ) 
 . 
 Notation " 'Ф_prepare_trading_pair_state_init_and_addr_ref_' '(' pair_data ',' pair_code ')' " := 
 ( URResult ( Ф_prepare_trading_pair_state_init_and_addr_call 
 pair_data pair_code )) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 
 , pair_code custom ULValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getSellTradingPair ( tip3_root : XAddress ) : UExpression XAddress false . 
 	 	 refine {{ tip3_root : ( XAddress ) @ "tip3_root" ; { _ } }} . 
 	 	 refine {{ new 'myaddr : ( XAddress ) @ "myaddr" := {} ; { _ } }} . 
 	 	       (* new { tvm_myaddr ( ) } *)  
 	 	 refine {{ pair_data : ( TradingPair ) @ "pair_data" ; { _ } }} . 
 	 	 refine {{ { pair_data } := {} (* new { . flex_addr_ = myaddr , . tip3_root_ = tip3_root , . deploy_value_ = tons_cfg_ . trading_pair_deploy } *) ; { _ } }} . 
 	 	 refine {{ new 'std_addr : ( TvmCell ) @ "std_addr"  := {}; { _ } }} . 
                    (*Ф_prepare_trading_pair_state_init_and_addr_ref_ ( !{ pair_data } , {} (* FLeX.pair_code_ ->get ) . second *) ) *)
 	 	 refine {{ new 'workchain_id : ( XAddress ) @ "workchain_id" := {} ; { _ } }} . 
 	 	                  (* Std :: get < addr_std > ( !{ myaddr } . Val ( ) ) . workchain_id *) 
 	 	 refine {{ return_ {} (* Address :: make_std ( !{ workchain_id } , !{ std_addr } ) *) }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getSellTradingPair_call  ( tip3_root : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф_getSellTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_root" }} tip3_root ) 
 . 
 Notation " 'FLeX_Ф_getSellTradingPair_ref_' '(' tip3_root ')' " := 
 ( URResult ( FLeX_Ф_getSellTradingPair_call 
 tip3_root )) 
 (in custom URValue at level 0 , tip3_root custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition Ф_prepare_xchg_pair_state_init_and_addr ( pair_data : XchgPair ) ( pair_code : TvmCell ) : UExpression ( XInteger (* StateInit *) # XInteger256 )%sol false . 
 	 	 refine {{ pair_data : ( XchgPair ) @ "pair_data" ; { _ } }} . 
 	 	 refine {{ pair_code : ( TvmCell ) @ "pair_code" ; { _ } }} . 
 	 	 refine {{ new 'pair_data_cl : ( TvmCell ) @ "pair_data_cl" := {} ; { _ } }} . 
 	 	                (* prepare_persistent_data ( { } , !{pair_data} ) *) 
 	 	 refine {{ new 'pair_init : ( XInteger (* StateInit *) ) @ "pair_init" := {} ; { _ } }} . 
 	 	         (* new { { } , { } , pair_code , pair_data_cl , { } } *)  
 	 	 refine {{ new 'pair_init_cl : ( TvmCell ) @ "pair_init_cl" := {} ; { _ } }} . 
 	 	           (* build ( !{ pair_init } ) . make_cell ( ) *)  
 	 	 refine {{ return_ {} (* [ !{ pair_init } , tvm_hash ( pair_init_cl ) ] *) }} . 
 Defined . 
 
 (*begin*) 
 Definition Ф_prepare_xchg_pair_state_init_and_addr_call  ( pair_data : URValue XchgPair false ) ( pair_code : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) Ф_prepare_xchg_pair_state_init_and_addr 
 ( SimpleLedgerableArg URValue {{ Λ "pair_data" }} pair_data ) 
 ( SimpleLedgerableArg URValue {{ Λ "pair_code" }} pair_code ) 
 . 
 Notation " 'Ф_prepare_xchg_pair_state_init_and_addr_ref_' '(' pair_data , pair_code ')' " := 
 ( URResult ( Ф_prepare_xchg_pair_state_init_and_addr_call 
 pair_data pair_code )) 
 (in custom URValue at level 0 , pair_data custom URValue at level 0 
 , pair_code custom ULValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getXchgTradingPair ( tip3_major_root : XAddress ) ( tip3_minor_root : XAddress ) : UExpression XAddress false . 
 	 	 refine {{ tip3_major_root : ( XAddress ) @ "tip3_major_root" ; { _ } }} . 
 	 	 refine {{ tip3_minor_root : ( XAddress ) @ "tip3_minor_root" ; { _ } }} . 
 	 	 refine {{ new 'myaddr : ( XAddress ) @ "myaddr" := {} ; { _ } }} . 
 	 	                     (* new { tvm_myaddr ( ) } *)  
 	 	 refine {{ new 'pair_data : ( XchgPair ) @ "pair_data" := {} ; { _ } }} . 
 	 	             (* new { . flex_addr_ = myaddr , . tip3_major_root_ = tip3_major_root , . tip3_minor_root_ = tip3_minor_root , . deploy_value_ = tons_cfg_ . trading_pair_deploy } *)
 (* 	 	 refine {{ new 'std_addr : ( ( XInteger (* StateInit *) * XInteger256 ) ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ { std_addr } := {} (* Ф_prepare_xchg_pair_state_init_and_addr_ref_ ( !{ pair_data } , {} (* FLeX.xchg_pair_code_ ->get *) ) . second *) ; { _ } }} . 
 *)  refine {{ new 'workchain_id : ( XAddress ) @ "workchain_id" := {} ; { _ } }} . 
 	 	            (* Std :: get < addr_std > ( !{ myaddr } . Val ( ) ) . workchain_id *) 
 	 	 refine {{ return_ {} (* Address :: make_std ( !{ workchain_id } , !{ std_addr } ) *) }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getXchgTradingPair_call  ( tip3_major_root : URValue XAddress false ) ( tip3_minor_root : URValue XAddress false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ2 ) FLeX_Ф_getXchgTradingPair 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_major_root" }} tip3_major_root ) 
 ( SimpleLedgerableArg URValue {{ Λ "tip3_minor_root" }} tip3_minor_root ) 
 . 
 Notation " 'FLeX_Ф_getXchgTradingPair_ref_' '(' tip3_major_root tip3_minor_root ')' " := 
 ( URResult ( FLeX_Ф_getXchgTradingPair_call 
 tip3_major_root tip3_minor_root )) 
 (in custom URValue at level 0 , tip3_major_root custom URValue at level 0 
 , tip3_minor_root custom ULValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getMinAmount : UExpression XInteger128 false . 
 	 	 refine {{ return_ FLeX.min_amount_ }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getMinAmount_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getMinAmount 
 . 
 Notation " 'FLeX_Ф_getMinAmount_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getMinAmount_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getDealsLimit : UExpression XInteger8 false . 
 	 	 refine {{ return_ FLeX.deals_limit_ }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getDealsLimit_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getDealsLimit 
 . 
 Notation " 'FLeX_Ф_getDealsLimit_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getDealsLimit_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 
 
 Definition FLeX_Ф_getNotifyAddr : UExpression XAddress false . 
 	 	 refine {{ return_ FLeX.notify_addr_ }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф_getNotifyAddr_call  := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ0 ) FLeX_Ф_getNotifyAddr 
 . 
 Notation " 'FLeX_Ф_getNotifyAddr_ref_' '(' ')' " := 
 ( URResult ( FLeX_Ф_getNotifyAddr_call 
 )) 
 (in custom URValue at level 0 ) : ursus_scope . 
 (*end*) 

 Definition FLeX_Ф__fallback ( _ : TvmCell ) : UExpression XInteger false . 
 	 	 refine {{ return_ 0  }} . 
 Defined . 
 
 (*begin*) 
 Definition FLeX_Ф__fallback_call  ( x : URValue TvmCell false ) := 
 🏓 ursus_call_with_args ( LedgerableWithArgs := λ1 ) FLeX_Ф__fallback 
 ( SimpleLedgerableArg URValue {{ Λ "x" }} x ) 
 . 
 Notation " 'FLeX_Ф__fallback_ref_' '(' x ')' " := 
 ( URResult ( FLeX_Ф__fallback_call 
 x )) 
 (in custom URValue at level 0 , x custom URValue at level 0 ) : ursus_scope . 
 (*end*) 


End FLeXFuncs .