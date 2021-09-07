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

Require Import FLeXClass.

Require Import FLeXContractConsts.  
Require Import FLeXConstSig.
Require Import ZArith.

Require Import FLeXFuncsNotations.
Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG26.

Require Import UrsusStdLib.stdNotations.
Require Import UrsusStdLib.stdUFunc.
Require Import UrsusStdLib.stdFuncNotations.
Require Import UrsusTVM.tvmNotations.

Module FLeXFuncs (dc : FLeXConstsTypesSig XTypesModule StateMonadModule ).

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



Definition Flex_Ф_constructor ( deployer_pubkey : XInteger256 ) ( transfer_tip3 : XInteger128 ) ( return_ownership : XInteger128 ) ( trading_pair_deploy : XInteger128 ) ( order_answer : XInteger128 ) ( process_queue : XInteger128 ) ( send_notify : XInteger128 ) ( deals_limit : XInteger8 ) ( notify_addr : XAddress ) : UExpression PhantomType false . 
 	 	 refine {{ deployer_pubkey : ( XInteger256 ) @ "deployer_pubkey" ; { _ } }} . 
 	 	 refine {{ transfer_tip3 : ( XInteger128 ) @ "transfer_tip3" ; { _ } }} . 
 	 	 refine {{ return_ownership : ( XInteger128 ) @ "return_ownership" ; { _ } }} . 
 	 	 refine {{ trading_pair_deploy : ( XInteger128 ) @ "trading_pair_deploy" ; { _ } }} . 
 	 	 refine {{ order_answer : ( XInteger128 ) @ "order_answer" ; { _ } }} . 
 	 	 refine {{ process_queue : ( XInteger128 ) @ "process_queue" ; { _ } }} . 
 	 	 refine {{ send_notify : ( XInteger128 ) @ "send_notify" ; { _ } }} . 
 	 	 refine {{ deals_limit : ( XInteger8 ) @ "deals_limit" ; { _ } }} . 
 	 	 refine {{ notify_addr : ( XAddress ) @ "notify_addr" ; { _ } }} . 
 	 	 refine {{ FLeX.deployer_pubkey_ := !{ deployer_pubkey } ; { _ } }} . 
 	 	 refine {{ FLeX.deals_limit_ := !{ deals_limit } ; { _ } }} . 
 	 	 refine {{ FLeX.notify_addr_ := !{ notify_addr } ; { _ } }} . 
 	 	 refine {{ FLeX.tons_cfg_ := {} (* { !{ transfer_tip3 } , !{ return_ownership } , !{ trading_pair_deploy } , !{ order_answer } , !{ process_queue } , !{ send_notify } } *) }} . 
 Defined . 
 
 
 Definition Flex_Ф_setPairCode ( code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ code : ( TvmCell ) @ "code" ; { _ } }} . 
 	 	 refine {{ require_ ( ( ~ TRUE (* FLeX.pair_code_ *) ) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == FLeX.deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm.accept () ; { _ } }} . 
 	 	 refine {{ require ( ( code ^^ TvmCell:ctos ( ) . srefs ( ) == 2 ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ pair_code_ := builder ( ) . stslice ( code ^^ TvmCell:ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) ; { _ } }} . 
 Defined . 
 
 
 Definition Flex_Ф_setXchgPairCode ( code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ code : ( TvmCell ) @ "code" ; { _ } }} . 
 	 	 refine {{ require ( ( ! xchg_pair_code_ ) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ require ( ( msg_pubkey ( ) == deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ require ( ( code ^^ TvmCell:ctos ( ) . srefs ( ) == 2 ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ xchg_pair_code_ := builder ( ) . stslice ( code ^^ TvmCell:ctos ( ) ) . stref ( build ( Address { tvm_myaddr ( ) } ) . endc ( ) ) . endc ( ) ; { _ } }} . 
 Defined . 
 
 
 Definition Flex_Ф_setPriceCode ( code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ code : ( TvmCell ) @ "code" ; { _ } }} . 
 	 	 refine {{ require ( ( ! price_code_ ) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ require ( ( msg_pubkey ( ) == deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ price_code_ := !{ code } ; { _ } }} . 
 Defined . 
 
 
 Definition Flex_Ф_setXchgPriceCode ( code : TvmCell ) : UExpression PhantomType true . 
 	 	 refine {{ code : ( TvmCell ) @ "code" ; { _ } }} . 
 	 	 refine {{ require ( ( ! xchg_price_code_ ) , error_code::cant_override_code ) ; { _ } }} . 
 	 	 refine {{ require ( ( msg_pubkey ( ) == deployer_pubkey_ ) , error_code::sender_is_not_deployer ) ; { _ } }} . 
 	 	 refine {{ tvm_accept ( ) ; { _ } }} . 
 	 	 refine {{ xchg_price_code_ := !{ code } ; { _ } }} . 
 Defined . 
 
 
 Definition Flex_Ф_isFullyInitialized : UExpression XBool false . 
 	 	 refine {{ return_ pair_code_ && price_code_ && xchg_pair_code_ && xchg_price_code_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getTonsCfg : UExpression TonsConfig false . 
 	 	 refine {{ return_ tons_cfg_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getTradingPairCode : UExpression TvmCell false . 
 	 	 refine {{ return_ *pair_code_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getXchgPairCode : UExpression TvmCell false . 
 	 	 refine {{ return_ *xchg_pair_code_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getSellPriceCode ( tip3_addr : XAddress ) : UExpression TvmCell true . 
 	 	 refine {{ tip3_addr : ( XAddress ) @ "tip3_addr" ; { _ } }} . 
 	 	 refine {{ require ( ( price_code_ - > ctos ( ) . srefs ( ) == 2 ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ new salt : ( TvmCell ) @ "salt" ; { _ } }} . 
 	 	 refine {{ { salt } := builder ( ) . stslice ( tvm_myaddr ( ) ) . stslice ( tip3_addr ^^ XAddress:sl ( ) ) . endc ( ) ; { _ } }} . 
 	 	 refine {{ return_ builder ( ) . stslice ( price_code_ - > ctos ( ) ) . stref ( !{ salt } ) . endc ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getXchgPriceCode ( tip3_addr1 : XAddress ) ( tip3_addr2 : XAddress ) : UExpression TvmCell true . 
 	 	 refine {{ tip3_addr1 : ( XAddress ) @ "tip3_addr1" ; { _ } }} . 
 	 	 refine {{ tip3_addr2 : ( XAddress ) @ "tip3_addr2" ; { _ } }} . 
 	 	 refine {{ require ( ( price_code_ - > ctos ( ) . srefs ( ) == 2 ) , error_code::unexpected_refs_count_in_code ) ; { _ } }} . 
 	 	 refine {{ new keys : ( auto ) @ "keys" ; { _ } }} . 
 	 	 refine {{ { keys } := std : : make_tuple ( !{ tip3_addr1 } , !{ tip3_addr2 } ) ; { _ } }} . 
 	 	 refine {{ return_ builder ( ) . stslice ( xchg_price_code_ - > ctos ( ) ) . stref ( build ( !{ keys } ) . endc ( ) ) . endc ( ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getSellTradingPair ( tip3_root : XAddress ) : UExpression XAddress false . 
 	 	 refine {{ tip3_root : ( XAddress ) @ "tip3_root" ; { _ } }} . 
 	 	 refine {{ new myaddr : ( XAddress ) @ "myaddr" ; { _ } }} . 
 	 	 refine {{ { myaddr } := NEW { tvm_myaddr ( ) } ; { _ } }} . 
 	 	 refine {{ new pair_data : ( DTradingPairP ) @ "pair_data" ; { _ } }} . 
 	 	 refine {{ { pair_data } := NEW { . flex_addr_ = myaddr , . tip3_root_ = tip3_root , . min_amount_ = uint128 ( 0 ) } ; { _ } }} . 
 	 	 refine {{ new std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ { std_addr } := prepare_trading_pair_state_init_and_addr ( !{ pair_data } , *pair_code_ ) . second ; { _ } }} . 
 	 	 refine {{ new workchain_id : ( auto ) @ "workchain_id" ; { _ } }} . 
 	 	 refine {{ { workchain_id } := Std :: get < addr_std > ( myaddr ^^ address:val ( ) ) . workchain_id ; { _ } }} . 
 	 	 refine {{ return_ Address :: make_std ( !{ workchain_id } , !{ std_addr } ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getXchgTradingPair ( tip3_major_root : XAddress ) ( tip3_minor_root : XAddress ) : UExpression XAddress false . 
 	 	 refine {{ tip3_major_root : ( XAddress ) @ "tip3_major_root" ; { _ } }} . 
 	 	 refine {{ tip3_minor_root : ( XAddress ) @ "tip3_minor_root" ; { _ } }} . 
 	 	 refine {{ new myaddr : ( XAddress ) @ "myaddr" ; { _ } }} . 
 	 	 refine {{ { myaddr } := NEW { tvm_myaddr ( ) } ; { _ } }} . 
 	 	 refine {{ new pair_data : ( DXchgPairP ) @ "pair_data" ; { _ } }} . 
 	 	 refine {{ { pair_data } := NEW { . flex_addr_ = myaddr , . tip3_major_root_ = tip3_major_root , . tip3_minor_root_ = tip3_minor_root , . min_amount_ = uint128 ( 0 ) } ; { _ } }} . 
 	 	 refine {{ new std_addr : ( auto ) @ "std_addr" ; { _ } }} . 
 	 	 refine {{ { std_addr } := prepare_xchg_pair_state_init_and_addr ( !{ pair_data } , *xchg_pair_code_ ) . second ; { _ } }} . 
 	 	 refine {{ new workchain_id : ( auto ) @ "workchain_id" ; { _ } }} . 
 	 	 refine {{ { workchain_id } := Std :: get < addr_std > ( myaddr ^^ address:val ( ) ) . workchain_id ; { _ } }} . 
 	 	 refine {{ return_ Address :: make_std ( !{ workchain_id } , !{ std_addr } ) ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getDealsLimit : UExpression XInteger8 false . 
 	 	 refine {{ return_ deals_limit_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф_getNotifyAddr : UExpression XAddress false . 
 	 	 refine {{ return_ notify_addr_ ; { _ } }} . 
 Defined . 
 
 
 
 Definition Flex_Ф__fallback ( cell : ( ) : UExpression XInteger false . 
 	 	 refine {{ cell : ( ( ) @ "cell" ; { _ } }} . 
 	 	 refine {{ return_ 0 ; { _ } }} . 
 Defined . 
 
 
 
