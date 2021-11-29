Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
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
Require Import Project.CommonTypes.

Require Import Contracts.Wrapper.Ledger.
Require Import Contracts.Wrapper.Functions.FuncSig.
Require Import Contracts.Wrapper.Functions.FuncNotations.
Require Import Contracts.Wrapper.Interface.

(* Require  Import Contracts.TradingPair.ClassTypes.
Require  Import Contracts.PriceXchg.ClassTypes.
Require  Import Contracts.XchgPair.ClassTypes.
Require  Import Contracts.Price.ClassTypes.
Require  Import Contracts.Wrapper.ClassTypes. *)
Require  Import Contracts.TONTokenWallet.ClassTypes.

(*********************************************)
(* Require Import TradingPair.ClassTypesNotations. *)
(*********************************************)

Require Import Project.CommonTypes.

Module Funcs (co: CompilerOptions) (dc : ConstsTypesSig XTypesModule StateMonadModule) .
Import co.

Module Export FuncNotationsModuleForFuncs := FuncNotations XTypesModule StateMonadModule dc.
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module TONTonkenWalletModuleForPrice := 
                      Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.
Local Open Scope ucpp_scope.

Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Existing Instance LedgerPruvendoRecord.


Definition getStateInit ( msg : PhantomType ) : UExpression StateInitLRecord false . 
 refine {{ if TRUE(* ( msg_init -> isa < ref < StateInit > > () ) *) then { {_ :UEf} } else { {_:UEf} }  }} . 
 	 	 	 refine {{ return_ {}(* msg_init -> get < ref < StateInit > > () () *) }} . 
 	 refine {{ return_  {} (* msg_init -> get < StateInit > () *) }} . 
 Defined . 
 
Definition getStateInit_right { a1 }  ( msg : URValue (PhantomType) a1 ) : URValue StateInitLRecord a1 := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) getStateInit msg ) . 

Notation " 'getStateInit_' '(' msg ')' " := 
( getStateInit_right 
msg ) 
(in custom URValue at level 0 , msg custom URValue at level 0 ) : ursus_scope . 

Declare Instance asdfasdf : LocalStateField PhantomType.
 
Definition init ( external_wallet : ( XAddress ) ) : UExpression XBool true . 
     refine {{ require_ ( ( ~ _external_wallet_ ) , error_code::cant_override_external_wallet ) ; {_} }} . 
 	 	 refine {{ new 'parsed_msg : ( PhantomType(* auto *) ) @ "parsed_msg" := {}
                   (* parse ( parser ( msg_slice () ) , error_code::bad_incoming_msg ) *) ; {_} }} . 
 	 	 refine {{ require_ ( (* (!{parsed_msg}) ↑ ???.init *) {} , error_code::bad_incoming_msg ) ; {_} }} . 
 	 	 refine {{ new 'init : ( StateInitLRecord ) @ "init" :=  
                                      getStateInit_ ( (!{ parsed_msg }) ) ; {_} }} . 
 	 	 refine {{ require_ ( ( (!{init}) ↑ StateInit.code ) , error_code::bad_incoming_msg ) ; {_} }} . 
 	 	 refine {{ new 'mycode : ( XCell ) @ "mycode" := 
                             ((!{init}) ↑ StateInit.code ) -> get_default () ; {_} }} . 
 	 	 refine {{ require_ ( ( (!{ mycode }) -> to_cell () -> refs () == #{3} ) , error_code::unexpected_refs_count_in_code ) ; {_} }} . 
(*  	 	 refine {{ parser mycode_parser ( (!{ mycode }) -> to_cell () ) ; {_} }} .  *)
(*  	 	 refine {{ mycode_parser ^^ ldref () ; {_} }} . 
 	 	 refine {{ mycode_parser ^^ ldref () ; {_} }} .  *)
 	 	 refine {{ new 'mycode_salt : ( PhantomType(* auto *) ) @ "mycode_salt" := {} 
                              (* (!{mycode_parser}) ldrefrtos () *) ; {_} }} . 
 	 	 refine {{ new 'flex_addr : ( XAddress ) @ "flex_addr" := {} 
                              (*  parse ( (!{ mycode_salt }) ) *) ; {_} }} . 
 	 	 refine {{ require_ ( ( (!{ flex_addr }) == int_sender () ) , error_code::only_flex_may_deploy_me ) ; {_} }} . 
 	 	 refine {{ _external_wallet_ := (#{ external_wallet }) -> set () ; {_} }} . 
 	 	 refine {{ tvm_rawreserve ( _start_balance_ , rawreserve_flag::up_to ) ; {_} }} . 
(*  	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; {_} }} .  *)
 	 	 refine {{ return_ TRUE }} . 
 Defined .  

 Definition is_internal_owner : UExpression XBool false . 
refine  {{ return_ _owner_address_ -> has_value () }} . 
 Defined . 
 
Definition is_internal_owner_right  : URValue XBool false := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) is_internal_owner 
) . 

Notation " 'is_internal_owner_' '(' ')' " := 
( is_internal_owner_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 

 
 Definition check_internal_owner : UExpression PhantomType true . 
refine {{ require_ ( ( is_internal_owner_ ( ) ) , error_code::internal_owner_disabled ) ; {_} }} . 
 	 	 refine {{ require_ ( ( _owner_address_ -> get_default () == int_sender () ) , error_code::message_sender_is_not_my_owner ) }} . 
 Defined . 
 
 Definition check_external_owner : UExpression PhantomType true . 
 refine {{ require_ ( ( ~ is_internal_owner_ ( ) ) , error_code::internal_owner_enabled ) ; {_} }} . 
 	 	 refine {{ require_ ( ( msg_pubkey () == _root_public_key_ ) , error_code::message_sender_is_not_my_owner ) }} . 
 Defined . 
 
Definition check_internal_owner_left { R }  : UExpression R true := 
wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_internal_owner 
) . 

Notation " 'check_internal_owner_' '(' ')' " := 
( check_internal_owner_left 
) 
(in custom ULValue at level 0 ) : ursus_scope . 

Definition check_external_owner_left { R }  : UExpression R true := 
wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_external_owner 
) . 

Notation " 'check_external_owner_' '(' ')' " := 
( check_external_owner_left 
) 
(in custom ULValue at level 0 ) : ursus_scope . 
 
Definition check_owner : UExpression PhantomType true . 
 refine {{ if ( #{Internal} ) then { {_:UEt} } else { {_:UEt} } }} . 
 	 	 refine {{ check_internal_owner_ ( ) }} . 
 	 	 refine {{ check_external_owner_ ( ) }} . 
 Defined .

Definition check_owner_left { R } : UExpression R true  := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_owner 
 ) . 
 
Notation " 'check_owner_' '(' ')' " := 
 ( check_owner_left ) 
 (in custom ULValue at level 0 ) : ursus_scope .

Definition setInternalWalletCode ( wallet_code : ( XCell ) ) : UExpression XBool true . 
     refine {{ check_owner_ ( ) ; {_} }} .  
 	 	 refine {{ tvm_accept () ; {_}  }} . 
 	 	 refine {{ require_ ( ( ~ _internal_wallet_code_ ) , error_code::cant_override_wallet_code ) ; {_} }} . 
 	 	 refine {{ _internal_wallet_code_ := (#{ wallet_code } ->set()) ; {_} }} . 
 	 	 refine {{ if ( #{Internal} ) then { {_:UEf} }; {_} }} . 
 	 	 	 refine {{ new 'value_gr : XUInteger256 @ "value_gr" := int_value () ; {_} }} . 
<<<<<<< HEAD
 	 	 	 refine {{ tvm_rawreserve (( tvm_balance () - !{value_gr} ) , rawreserve_flag::up_to )(* ;  {_} }} . 
=======
 	 	 	 refine {{ tvm_rawreserve (( tvm_balance () - !{value_gr} ) ,  rawreserve_flag::up_to  )(* ;  {_} }} . 
>>>>>>> 9043f6d409a7ae511a8d4095191064d6e258d97d
 	 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) *) }} . 
 	 refine {{ return_  TRUE  }} . 
Defined . 

Definition prepare_persistent_data { X Y } (persistent_data_header : X) 
                                           (base : Y): UExpression XCell false .
 refine {{ return_ {} }} .  
Defined .

Definition prepare_persistent_data_right { X Y a1 a2 }  
                                    ( persistent_data_header : URValue X a1 ) 
                                    ( base : URValue Y a2 ) 
               : URValue XCell (orb a2 a1) := 
wrapURExpression (ursus_call_with_args ( LedgerableWithArgs:= λ2 ) prepare_persistent_data persistent_data_header base ) . 
 
 Notation " 'prepare_persistent_data_' '(' a ',' b ')' " := ( prepare_persistent_data_right a b ) 
 (in custom URValue at level 0 , a custom URValue at level 0 , b custom URValue at level 0 ) : ursus_scope . 

Definition prepare_internal_wallet_state_init_and_addr ( name :  String ) ( symbol : String )
 														( decimals : uint8 ) ( root_public_key : uint256 )
 														( wallet_public_key : uint256 ) ( root_address : raw_address ) 
														( owner_address : optional raw_address ) ( code : TvmCell ) 
														( workchain_id : uint8 ) : UExpression ( StateInitLRecord * uint256 ) false .
 	 	 refine {{ new 'wallet_data : TONTonkenWalletModuleForPrice.DTONTokenWalletInternalLRecord @ "wallet_data" := 
                 [ #{name} , #{symbol} , #{decimals} , 0 , #{root_public_key} , 
                   #{wallet_public_key} , #{root_address} , #{owner_address} , 
                   {} , #{code} , #{workchain_id} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_data_cl : TvmCell @ "wallet_data_cl" := 
               prepare_persistent_data_ ( {} , !{wallet_data} ) ; { _ } }} . 
 	 	 refine {{ new 'wallet_init : StateInitLRecord @ "wallet_init" := [ {} , {} , (#{code}) -> set () , (!{wallet_data_cl}) -> set () , {} ] ; { _ } }} . 
 	 	 refine {{ new 'wallet_init_cl : TvmCell @ "wallet_init_cl" := {}  
 	 	            (*  build ( !{ wallet_init } ) . make_cell ( ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{ wallet_init } ,  tvm_hash ( !{wallet_init_cl} )  ] }} . 
 Defined . 

Definition prepare_internal_wallet_state_init_and_addr_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 } ( name : URValue String a1 ) 
																							( symbol : URValue String a2 ) 
																							( decimals : URValue uint8 a3 ) 
																							( root_public_key : URValue uint256 a4 ) 
																							( wallet_public_key : URValue uint256 a5 ) 
																							( root_address : URValue raw_address a6 ) 
																							( owner_address : URValue ( optional raw_address ) a7 ) 
																							( code : URValue TvmCell a8 ) 
																							( workchain_id : URValue uint8 a9 ) : URValue ( StateInitLRecord * uint256 ) ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_internal_wallet_state_init_and_addr 
	name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
Notation " 'prepare_internal_wallet_state_init_and_addr_' '(' name ',' symbol ',' decimals ',' root_public_key ',' wallet_public_key ',' root_address ',' owner_address ',' code ',' workchain_id ')' " := 
 ( prepare_internal_wallet_state_init_and_addr_right name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 , symbol custom URValue at level 0 , decimals custom URValue at level 0 , 
 	 root_public_key custom URValue at level 0 , wallet_public_key custom URValue at level 0 , root_address custom URValue at level 0 , 
	 owner_address custom URValue at level 0 , code custom URValue at level 0 , workchain_id custom URValue at level 0 ) : ursus_scope . 

Definition optional_owner ( owner : ( XAddress ) ) : UExpression (XMaybe XAddress) false . 
     refine  {{ return_ {} (* Std :: get < addr_std > ( (#{ owner }) () ) . address ? std::optional ( (#{ owner }) ) : std::optional () *) }} . 
Defined . 
 
Definition optional_owner_right { a1 }  ( owner : URValue ( XAddress ) a1 ) : URValue (XMaybe XAddress) a1 := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) optional_owner 
owner ) . 

Notation " 'optional_owner_' '(' owner ')' " := 
( optional_owner_right 
owner ) 
(in custom URValue at level 0 , owner custom URValue at level 0 ) : ursus_scope . 

Definition calc_internal_wallet_init ( pubkey : ( XUInteger256 ) ) ( owner_addr : ( XAddress ) ) : UExpression ( StateInitLRecord # XAddress ) true . 
		refine {{ wallet_init : ( StateInitLRecord ) @ "wallet_init" ; {_} }} . 
 	 	 refine {{ dest_addr : ( raw_address ) @ "dest_addr" ; {_} }} . 
 	 	 refine {{ new ( 'wallet_init:StateInitLRecord , 'dest_addr:raw_address ) @
                   ( "wallet_init" , "dest_addr" ) := 
         prepare_internal_wallet_state_init_and_addr_ ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ pubkey }) , tvm_myaddr () , optional_owner_ ( (#{ owner_addr }) ) , _internal_wallet_code_ -> get () , _workchain_id_ ) ; {_} }} . 
 	 	 refine {{ new 'dest : ( XAddress ) @ "dest" := {} 
                      (* Address :: make_std ( _workchain_id_ , dest_addr ) *) ; {_} }} . 
 	 	 refine {{ return_ {} (* [ wallet_init , (!{ dest }) ] *) }} . 
 Defined . 
 
Definition calc_internal_wallet_init_right { a1 a2 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( owner_addr : URValue ( XAddress ) a2 ) 
: URValue ( StateInitLRecord # XAddress ) true (* orb a2 a1 *) := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_internal_wallet_init 
pubkey owner_addr ) . 

Notation " 'calc_internal_wallet_init_' '(' pubkey ',' owner_addr ')' " := 
( calc_internal_wallet_init_right 
pubkey owner_addr ) 
(in custom URValue at level 0 , pubkey custom URValue at level 0 
, owner_addr custom URValue at level 0 ) : ursus_scope . 

 
<<<<<<< HEAD
Definition deployEmptyWallet ( pubkey : ( XUInteger256 ) ) ( internal_owner : ( XAddress ) ) ( grams : ( XUInteger128 ) ) : UExpression XAddress true . 
    refine {{ new 'value_gr : ( uint256 ) @ "value_gr" := int_value () ; {_} }} . 
		refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr })  , rawreserve_flag::up_to ) ; {_} }} . 
    refine {{ new ( 'wallet_init:StateInitLRecord , 'dest:raw_address ) @
                  ( "wallet_init" , "dest" ) := 
       calc_internal_wallet_init_ ( (#{ pubkey }) , (#{ internal_owner }) ) ; {_} }} .  
(*  refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; {_} }} .  *)
(* 		refine {{ dest_handle ^^ deploy_noop ( wallet_init , Grams ( (#{ grams }) . get () ) ) ; {_} }} .  *)
(* 		refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; {_} }} .  *)
		refine {{ return_ !{dest} }} . 
 Defined . 
=======
 
(*  Definition deployEmptyWallet ( pubkey : ( XUInteger256 ) ) ( internal_owner : ( XAddress ) ) ( grams : ( XUInteger128 ) ) : UExpression XAddress false . 
 refine {{ new 'value_gr : ( uint256 ) @ "value_gr" := {} ; {_} }} . 
		refine {{ { value_gr } := int_value () ; {_} }} . 
		refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr })  , rawreserve_flag::up_to ) ; {_} }} . 
		refine {{ wallet_init : ( uint256 ) @ "wallet_init" ; {_} }} . 
		refine {{ dest : ( raw_address ) @ "dest" ; {_} }} . 
		(* refine {{ [ wallet_init , dest ] := calc_internal_wallet_init_ ( (#{ pubkey }) , (#{ internal_owner }) ) ; _ }} .  *)
		(* refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; _ }} .  *)
		refine {{ dest_handle ^^ deploy_noop ( wallet_init , Grams ( (#{ grams }) . get () ) ) ; _ }} . 
		refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
		refine {{ return_ dest }} . 
 Defined .  *)
>>>>>>> 9043f6d409a7ae511a8d4095191064d6e258d97d
 
 Parameter set_int_sender : UExpression WrapperRetLRecord false .

Notation " 'set_int_sender_' '(' ')' " := 
 ( set_int_sender ) 
 (in custom ULValue at level 0 ) : ursus_scope . 

 Parameter set_int_return_value : UExpression PhantomType false .
 Notation " 'set_int_return_value_' '(' ')' " := 
  ( set_int_sender ) 
  (in custom ULValue at level 0 ) : ursus_scope .

Parameter set_int_return_flag :UExpression WrapperRetLRecord false .
Notation " 'set_int_return_flag_' '(' ')' " := 
 ( set_int_return_flag ) 
 (in custom ULValue at level 0 ) : ursus_scope .

Definition expected_internal_address 
( sender_public_key : ( XUInteger256 ) ) 
( sender_owner_addr : ( XAddress ) ) 
: UExpression XAddress (* true *) false . 
refine  {{ new 'hash_addr : ( XUInteger256 ) @ "hash_addr" := 
  second(prepare_internal_wallet_state_init_and_addr_ ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ sender_public_key }) , tvm_myaddr () , optional_owner_ ( (#{ sender_owner_addr }) ) , 
    (* TODO!!!!!! *)            _internal_wallet_code_ -> get_default () , _workchain_id_ )); {_} }} .
 	 	 refine {{ return_ {} (* Address :: make_std ( _workchain_id_ , (!{ hash_addr }) ) *) }} . 
 Defined .

Definition expected_internal_address_right { a1 a2 }  ( sender_public_key : URValue ( XUInteger256 ) a1 ) ( sender_owner_addr : URValue ( XAddress ) a2 ) 
: URValue XAddress (* true *) (orb a2 a1) := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) expected_internal_address 
sender_public_key sender_owner_addr ) . 

Notation " 'expected_internal_address_' '(' sender_public_key ',' sender_owner_addr ')' " := 
( expected_internal_address_right 
sender_public_key sender_owner_addr ) 
(in custom URValue at level 0 , sender_public_key custom URValue at level 0 
, sender_owner_addr custom URValue at level 0 ) : ursus_scope . 

Definition onTip3Transfer ( answer_addr : ( XAddress ) ) ( balance : ( XUInteger128 ) ) ( new_tokens : ( XUInteger128 ) ) ( sender_pubkey : ( XUInteger256 ) ) ( sender_owner : ( XAddress ) ) ( payload : ( XCell ) ) : UExpression WrapperRetLRecord true . 
 		refine {{ require_ ( ( int_sender () == _external_wallet_ -> get_default () ) , error_code::not_my_wallet_notifies ) ; {_} }}. 
		refine {{ set_int_sender_ ( (* ( (* #{ answer_addr } *) ) *) ) ; {_} }} . 
		refine {{ set_int_return_value_ ( (* 0 *) ) ; {_} }} . 
		refine {{ set_int_return_flag_ ( (*  SEND_ALL_GAS *) ) ; {_} }} . 
		refine {{ new 'args : ( FlexDeployWalletArgsLRecord ) @ "args" := {} 
                        (* parse ( (#{ payload }) . ctos () ) *) ; {_} }} . 
		refine {{ new 'value_gr : ( uint256 ) @ "value_gr" := int_value () ; {_} }} . 
<<<<<<< HEAD
		refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr })  , rawreserve_flag::up_to ) ; {_} }} . 
		refine {{ new ( 'wallet_init:StateInitLRecord , 'dest:raw_address ) @
                  ( "wallet_init" , "dest" ) := 
               calc_internal_wallet_init_ ( (!{ args }) ↑ FlexDeployWalletArgs.pubkey , 
                                            (!{ args }) ↑ FlexDeployWalletArgs.internal_owner ) ; {_} }} . 
(* 		refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; {_} }} .  *)
(* 		refine {{ dest_handle.deploy ( wallet_init , Grams ( (!{ args }) . grams . get () ) ) . accept ( (#{ new_tokens }) , int_sender () , (!{ args }) . grams ) ; {_} }} .  *)
=======
		refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr })  ,rawreserve_flag::up_to  ) ; {_} }} . 
		(* refine {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
		refine {{ dest : ( auto ) @ "dest" ; _ }} . 
		refine {{ [ wallet_init , dest ] := calc_internal_wallet_init_ ( (!{ args }) . pubkey , (!{ args }) . internal_owner ) ; _ }} . 
		refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; _ }} . 
		refine {{ dest_handle ^^ deploy ( wallet_init , Grams ( (!{ args }) . grams . get () ) ) . accept ( (#{ new_tokens }) , int_sender () , (!{ args }) . grams ) ; _ }} .  *)
>>>>>>> 9043f6d409a7ae511a8d4095191064d6e258d97d
		refine {{ _total_granted_ += (#{ new_tokens }) ; {_} }} . 
		refine {{ return_ {} (* [ 0 , dest_handle ^^ get () ] *) }} . 
 Defined . 
 
Parameter int_value_ : uint (*Grams*) .

Definition int_sender_and_value : UExpression ( XAddress # uint (*Grams*)) false .
  refine {{ new 'sender : XAddress @ "sender" := int_sender() ; { _ } }} .
  refine {{ return_ [ !{sender} , #{int_value_} ] }} .
Defined.

Definition int_sender_and_value_right : URValue ( XAddress # uint (*Grams*)) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) int_sender_and_value ) . 
 
<<<<<<< HEAD
 Notation " 'int_sender_and_value_' '(' ')' " := 
 ( int_sender_and_value_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition burn 
( answer_addr : ( XAddress ) ) 
( sender_pubkey : ( XUInteger256 ) ) 
( sender_owner : ( XAddress ) ) 
( out_pubkey : ( XUInteger256 ) ) 
( out_internal_owner : ( XAddress ) ) 
( tokens : ( XUInteger128 ) ) 
: UExpression PhantomType true . 
     refine {{ require_ ( ( _total_granted_ >= (#{ tokens }) ) , error_code::burn_unallocated ) ; {_} }} . 
 	 	 refine {{ new ( 'sender:XAddress , 'value_gr:uint ) @
                     ( "sender" , "value_gr" ) :=
                    int_sender_and_value_ ( ) ; {_} }} .  
(* TODO: this require has a "true" functions of expected_internal_address *)
 	 	 refine {{ require_ ( ( (!{sender}) == ( expected_internal_address_ ( (#{ sender_pubkey }) , (#{ sender_owner }) ) ) ) ,
                                        error_code::message_sender_is_not_good_wallet ) ; {_} }} .
 	 	 refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr })  , rawreserve_flag::up_to ) ; {_} }} . 
 	 	 (* refine {{ ( *external_wallet_ ) ( Grams ( 0 ) , SEND_ALL_GAS ) . transferToRecipient ( (#{ answer_addr }) , (#{ out_pubkey }) , (#{ out_internal_owner }) , (#{ tokens }) , uint128 ( 0 ) ,  TRUE ,  FALSE ) ; {_} }} .  *)
 	 	 refine {{ _total_granted_ -= (#{ tokens }) }} . 
 Defined . 
 
Definition requestTotalGranted : UExpression XUInteger128 false . 
 refine {{ new 'value_gr : ( uint256 ) @ "value_gr" := 
                                   int_value () ; {_} }} . 
 	 	 refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr })  , rawreserve_flag::up_to ) ; {_} }} . 
 	 	 (* refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; {_} }} .  *)
=======
 
 
 Definition burn ( answer_addr : ( XAddress ) ) ( sender_pubkey : ( XUInteger256 ) ) ( sender_owner : ( XAddress ) ) ( out_pubkey : ( XUInteger256 ) ) ( out_internal_owner : ( XAddress ) ) ( tokens : ( XUInteger128 ) ) : UExpression PhantomType true . 
refine {{ require_ ( ( _total_granted_ >= (#{ tokens }) ) , 1(* error_code::burn_unallocated *) ) ; {_} }} . 
 	 	 refine {{ new 'sender : ( raw_address ) @ "sender" := {} ; {_} }} . 
 	 	 refine {{ new 'value_gr  : uint  @ "value_gr" := {} ; {_} }} . 
 	 	 (* refine {{ [ { sender } , { value_gr } ] := int_sender_and_value () ; {_} }} .  *)
 	 	 (* refine {{ require_ ( ( !{sender} == expected_internal_address_ ( (#{ sender_pubkey }) ) , (#{ sender_owner }) ) ; _ }} .  *)
 	 	 refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr })  ,  rawreserve_flag::up_to  ) ; {_} }} . 
 	 	 (* refine {{ ( *external_wallet_ ) ( Grams ( 0 ) , SEND_ALL_GAS ) . transferToRecipient ( (#{ answer_addr }) , (#{ out_pubkey }) , (#{ out_internal_owner }) , (#{ tokens }) , uint128 ( 0 ) ,  TRUE ,  FALSE ) ; _ }} .  *)
 	 	 refine {{ _total_granted_ -= (#{ tokens }) }} . 
 Defined . 
 
 
 
 
 Definition requestTotalGranted : UExpression XUInteger128 false . 
 refine {{ new 'value_gr : ( uint256 ) @ "value_gr" := {} ; {_} }} . 
 	 	 refine {{ { value_gr } := int_value () ; {_} }} . 
 	 	 refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr })  ,  rawreserve_flag::up_to  ) ; {_} }} . 
 	 	 (* refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} .  *)
>>>>>>> 9043f6d409a7ae511a8d4095191064d6e258d97d
 	 	 refine {{ return_ _total_granted_ }} . 
 Defined . 
 
 Definition getName : UExpression XString false . 
 refine {{ return_ _name_ }} . 
 Defined . 
 
 Definition getSymbol : UExpression XString false . 
refine  {{ return_ _symbol_ }} . 
 Defined . 
 
 Definition getDecimals : UExpression XUInteger8 false . 
refine  {{ return_ _decimals_ }} . 
 Defined . 
 
 Definition getRootKey : UExpression XUInteger256 false . 
refine  {{ return_ _root_public_key_ }} . 
 Defined . 
 
 Definition getTotalGranted : UExpression XUInteger128 false . 
 refine {{ return_ _total_granted_ }} . 
 Defined . 
 
 Definition hasInternalWalletCode : UExpression XBool false . 
refine  {{ return_ ? ~ ~ _internal_wallet_code_  }} . 
 Defined . 
 
 Definition getInternalWalletCode : UExpression XCell true . 
refine  {{ return_ _internal_wallet_code_ -> get () }} . 
 Defined . 
 
 Definition getOwnerAddress : UExpression XAddress true . 
refine  {{ return_ (_owner_address_->has_value()) ? _owner_address_ ->get() : {}(* Address :: make_std ( 0 , 0 ) *) }} . 
 Defined . 
 
 Definition getExternalWallet : UExpression XAddress true . 
refine {{ return_ _external_wallet_ -> get () }} . 
 Defined . 
 
 Definition getWalletAddress ( pubkey : ( XUInteger256 ) ) ( owner : ( XAddress ) ) : UExpression XAddress true . 
refine {{ return_ second ( calc_internal_wallet_init_ ( (#{ pubkey }) , (#{ owner }) ) ) }} . 
 Defined . 
 
Definition getName_right  : URValue XString false := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getName 
) .
Notation " 'getName_' '(' ')' " := 
( getName_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 
Definition getSymbol_right  : URValue XString false := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSymbol 
) . 

Notation " 'getSymbol_' '(' ')' " := 
( getSymbol_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 
Definition getDecimals_right  : URValue XUInteger8 false := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDecimals 
) . 

Notation " 'getDecimals_' '(' ')' " := 
( getDecimals_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 
Definition getRootKey_right  : URValue XUInteger256 false := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootKey 
) . 

Notation " 'getRootKey_' '(' ')' " := 
( getRootKey_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 
Definition getTotalGranted_right  : URValue XUInteger128 false := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getTotalGranted 
) . 

Notation " 'getTotalGranted_' '(' ')' " := 
( getTotalGranted_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 
Definition hasInternalWalletCode_right  : URValue XBool false := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) hasInternalWalletCode 
) . 

Definition getInternalWalletCode_right  : URValue XCell true := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getInternalWalletCode 
) . 

Notation " 'getInternalWalletCode_' '(' ')' " := 
( getInternalWalletCode_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 

Definition getOwnerAddress_right  : URValue XAddress true := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwnerAddress 
) . 

Notation " 'getOwnerAddress_' '(' ')' " := 
( getOwnerAddress_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 

Definition getExternalWallet_right  : URValue XAddress true := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getExternalWallet 
) . 

Notation " 'getExternalWallet_' '(' ')' " := 
( getExternalWallet_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 
 
 Definition getDetails : UExpression wrapper_details_infoLRecord true . 
refine  {{ return_ [ getName_ ( ) , getSymbol_ ( ) , getDecimals_ ( ) , 
                     getRootKey_ ( ) , getTotalGranted_ ( ) , getInternalWalletCode_ ( ) ,
                     getOwnerAddress_ ( ) , getExternalWallet_ ( ) ] }} . 
Defined .
 
Definition getDetails_right  : URValue wrapper_details_infoLRecord true := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDetails 
) . 

Notation " 'getDetails_' '(' ')' " := 
( getDetails_right 
) 
(in custom URValue at level 0 ) : ursus_scope . 
 
(* template<class Interface, class ReplayAttackProtection, class DContract>
inline std::tuple<persistent_data_header_t<Interface, ReplayAttackProtection>, DContract> 
load_persistent_data() *)
Definition load_persistent_data : UExpression ( XCell # DWrapperLRecord ) false .
 refine {{ return_ {} }} .  
Defined .

Definition load_persistent_data_right : URValue ( XCell # DWrapperLRecord ) false := 
 wrapURExpression (ursus_call_with_args ( LedgerableWithArgs:= λ0 ) load_persistent_data ) . 
 
Notation " 'load_persistent_data_' '(' ')' " := ( load_persistent_data_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

(* void save_persistent_data(persistent_data_header_t<IContract, ReplayAttackProtection> persistent_data_header,
                                 DContract base) {
  persistent_data::set(prepare_persistent_data<IContract, ReplayAttackProtection, DContract>(persistent_data_header, base)); } *)
Definition save_persistent_data (persistent_data_header:XCell) 
                                (base:DWrapperLRecord) 
                              : UExpression PhantomType false .
 refine {{ return_ {} }} .  
Defined .

Definition save_persistent_data_left { R a1 a2 }  
                                  ( a : URValue XCell a1 ) 
                                  ( b : URValue DWrapperLRecord a2 ) 
: UExpression R ( orb a2 a1 ) := 
 wrapULExpression (ursus_call_with_args ( LedgerableWithArgs:= λ2 ) save_persistent_data a b ) . 
 
Notation " 'save_persistent_data_' '(' a ',' b ')' " := ( save_persistent_data_left a b ) 
 (in custom ULValue at level 0 ,
     a custom URValue at level 0 , b custom URValue at level 0 ) : ursus_scope . 

Definition _on_bounced 
( _ :  (TvmCell ) ) 
( msg_body : ( XSlice ) ) 
: UExpression XUInteger true. 
     refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ new 'Args : ( PhantomType (* auto *) ) @ "Args" := {}  
 	 	                 (* args_struct_t<&ITONTokenWallet::accept> *) ; {_} }} . 
(*  	 	 refine {{ parser p ( (#{ msg_body }) ) ; {_} }} .  *)
 	 	 refine {{ require_ ( ( (* p ^^ ldi (32) *) {} == #{(-1)%Z} ) , error_code::wrong_bounced_header ) ; {_} }} . 
 	 	 refine {{ new 'opt_hdr : ( PhantomType (* auto *) ) @ "opt_hdr" := {} ; {_} }} . 
(*  	 	 refine {{ [ opt_hdr , =p ] := parse_continue < abiv1::internal_msg_header > ( p ) ; {_} }} .  *)
(*  	 	 refine {{ require_ ( ( ? !{opt_hdr} (* && opt_hdr -> function_id == id_v < &ITONTokenWallet::accept > *) ) , 1 (* error_code::wrong_bounced_header *) ) ; {_} }} .  *)
 	 	 refine {{ new 'args : ( PhantomType (* auto *) ) @ "args" := {} 
                          (*  parse ( p , error_code::wrong_bounced_args ) *) ; {_} }} . 
 	 	 refine {{ new 'bounced_val : ( XUInteger128 ) @ "bounced_val" := {} 
                      (* (!{ args }) ↑ tokens *) ; {_} }} .
 	 	 refine {{ new ( 'hdr:XCell , 'persist:DWrapperLRecord ) @
                   ( "hdr" , "persist" ) := load_persistent_data_ ( )
(*                 load_persistent_data < IWrapper , wrapper_replay_protection_t , DWrapper > ()  *) ; {_} }} . 

 	 	 refine {{ require_ ( ( (!{ bounced_val }) <= ((!{persist}) ↑ DWrapper.total_granted_) ) , error_code::wrong_bounced_args ) ; {_} }} . 

 	 	 refine {{ ({persist} ↑ DWrapper.total_granted_) -= (!{ bounced_val }) ; {_} }} . 
 	 	 refine {{ save_persistent_data_ ( !{hdr} , !{persist} ) ; {_} }} .  
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 Definition getInternalWalletCodeHash : UExpression XUInteger256 true . 
refine  {{ return_  tvm_hash ( _internal_wallet_code_ -> get () )  }} . 
 Defined . 
 
 
 
 
 Definition _fallback ( cell :  (TvmCell ) ) : UExpression XUInteger false . 
refine  {{ return_ 0 }} . 
 Defined . 
 
 
 
 
Definition prepare_wrapper_state_init_and_addr ( wrapper_code : ( XCell ) ) ( wrapper_data : ( DWrapperLRecord ) ) : UExpression ( StateInitLRecord # XUInteger256 ) false . 
 refine {{ new 'wrapper_data_cl : ( XCell ) @ "wrapper_data_cl" := {} ; {_} }} . 
 	 	 refine {{ { wrapper_data_cl } := prepare_persistent_data_ ( {} (* wrapper_replay_protection_t::init () *) , (#{ wrapper_data }) ) ; {_} }} . 
 	 	 refine {{ new 'wrapper_init : ( StateInitLRecord ) @ "wrapper_init" := 	 	 
 	 	 	 [ {} , {} , (#{ wrapper_code }) -> set (), (!{ wrapper_data_cl }) -> set () , {} ] ; {_} }} . 
 	 	 refine {{ new 'wrapper_init_cl : ( XCell ) @ "wrapper_init_cl" := {} ; {_} }} . 
 	 	 refine {{ { wrapper_init_cl } := {} (* build ( (!{ wrapper_init }) ) . make_cell () *) ; {_} }} . 
 	 	 refine {{ return_ [ (!{ wrapper_init }) , tvm_hash ( (!{ wrapper_init_cl }) ) ] }} . 
 Defined . 
 
 
 
End Funcs.
