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

(*Fully qualified name are mandatory in multi-contract environment*)
Require Import RootTokenContract.Ledger.
Require Import RootTokenContract.Functions.FuncSig.
Require Import RootTokenContract.Functions.FuncNotations.

Require RootTokenContract.Interface.

Require Import TONTokenWallet.ClassTypes.

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.

Module Funcs (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .

Import co.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module TONTokenWalletClassTypes := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Definition optional_owner ( owner : address ) : UExpression (XMaybe address) false . 
	refine {{ return_ ( ? (#{ owner }) ↑ address.address ) ? (#{owner}) -> set () : {} }} . 
Defined . 

Definition optional_owner_right { a1 }  ( owner : URValue address a1 ) : URValue (optional address) a1 := 
	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) optional_owner owner ) . 
 
Notation " 'optional_owner_' '(' owner ')' " := ( optional_owner_right owner ) 
 (in custom URValue at level 0 , owner custom URValue at level 0 ) : ursus_scope . 

Definition is_internal_owner : UExpression boolean false . 
	refine {{ return_ (_owner_address_ -> has_value ()) }} . 
Defined. 

Definition is_internal_owner_right  : URValue boolean false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) is_internal_owner ) . 
 
Notation " 'is_internal_owner_' '(' ')' " := ( is_internal_owner_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition check_internal_owner : UExpression PhantomType true . 
	refine {{ require_ ( ( is_internal_owner_ ( ) ) , error_code::internal_owner_disabled ) ; { _ } }} . 
	(*AL: get under require *)
	refine {{ require_ ( ( (_owner_address_ -> get_default () == int_sender ()) ) , error_code::message_sender_is_not_my_owner ) ; {_} }} . 
	refine {{ return_ {} }} .
Defined . 
 
Definition check_internal_owner_left { R } : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_internal_owner ) . 
 
Notation " 'check_internal_owner_' '(' ')' " := ( check_internal_owner_left ) 
 (in custom ULValue at level 0 ) : ursus_scope . 
 
Definition check_external_owner ( allow_pubkey_owner_in_internal_node : boolean ) : UExpression PhantomType true . 
	refine {{ require_ ( ( (#{ allow_pubkey_owner_in_internal_node }) \\ ~ (is_internal_owner_ ( )) ) , error_code::internal_owner_enabled ) ; { _ } }} . 
	refine {{ require_ ( ( msg_pubkey () == _root_public_key_ ) , error_code::message_sender_is_not_my_owner ) ; {_} }} . 
	refine {{ return_ {} }} . 
Defined . 
 
Definition check_external_owner_left { R a1 }  ( allow_pubkey_owner_in_internal_node : URValue ( boolean ) a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) check_external_owner allow_pubkey_owner_in_internal_node ) . 
 
Notation " 'check_external_owner_' '(' allow_pubkey_owner_in_internal_node ')' " := 
 ( check_external_owner_left allow_pubkey_owner_in_internal_node ) 
 (in custom ULValue at level 0 , allow_pubkey_owner_in_internal_node custom URValue at level 0 ) : ursus_scope . 

Definition check_owner ( allow_pubkey_owner_in_internal_node : boolean ) : UExpression PhantomType true . 
	refine {{ if ( #{ Internal } ) then { {_:UEt} } else { {_:UEt} } ; { _ } }} . 
	refine {{ check_internal_owner_ ( ) }} . 
	refine {{ check_external_owner_ ( #{allow_pubkey_owner_in_internal_node} ) }} . 
	refine {{ return_ {} }} .
Defined .

Definition check_owner_left { R a1 }  ( x : URValue boolean a1 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) check_owner x ) . 
 
Notation " 'check_owner_' '(' x ')' " := ( check_owner_left x ) 
 (in custom ULValue at level 0 , x custom URValue at level 0 ) : ursus_scope . 

Definition constructor ( name : String ) ( symbol : String ) ( decimals : uint8 ) 
					   ( root_public_key : uint256 ) ( root_owner : address ) 
					   ( total_supply : uint128 ) : UExpression PhantomType true . 
	refine {{ require_ ( (#{ root_public_key } != 0) \\ 
						 (#{ root_owner }) ↑ address.address != 0 , error_code::define_pubkey_or_internal_owner ) ; { _ } }} . 
	refine {{ require_ ( (#{ decimals }) < #{4} , error_code::too_big_decimals ) ; { _ } }} . 
	refine {{ _name_ := #{ name } ; { _ } }} . 
	refine {{ _symbol_ := #{ symbol } ; { _ } }} . 
	refine {{ _decimals_ := #{ decimals } ; { _ } }} . 
	refine {{ _root_public_key_ := #{ root_public_key } ; { _ } }} . 
	refine {{ _total_supply_ := #{ total_supply } ; { _ } }} . 
	refine {{ _total_granted_ := 0 ; { _ } }} . 
	refine {{ _owner_address_ := optional_owner_ ( #{ root_owner } ) ; { _ } }} . 
	refine {{ _start_balance_ := tvm_balance () ; {_} }} . 
	refine {{ return_ {} }} .
Defined . 
 

Definition setWalletCode ( wallet_code : cell ) : UExpression boolean true . 
	refine {{ check_owner_ ( TRUE ) ; { _ } }} . 
	refine {{ tvm_accept () ; { _ } }} . 
	refine {{ require_ ( ( ~ _wallet_code_ ) , error_code::cant_override_wallet_code ) ; { _ } }} . 
	refine {{ _wallet_code_ := ( (#{ wallet_code }) -> set () ) ; { _ } }} . 
	refine {{ if ( #{Internal} ) then { {_:UEf} } ; { _ } }} . 
	refine {{ new 'value_gr : XUInteger @ "value_gr" := int_value () ; { _ } }} . 
	refine {{ tvm_rawreserve ( (tvm_balance ()) - (!{value_gr}) , rawreserve_flag::up_to ) }} . 	
	refine {{ set_int_return_flag ( SEND_ALL_GAS ) }} . 
	refine {{ return_ TRUE }} . 
Defined . 

(* DTONTokenWallet prepare_wallet_data(
  string name, string symbol, uint8 decimals, uint256 root_public_key,
  uint256 wallet_public_key, address root_address, std::optional<address> owner_address,
  cell code, int8 workchain_id
) {
  return {
    name, symbol, decimals,
    uint128(0), root_public_key, wallet_public_key,
    root_address, owner_address,
#ifdef TIP3_ENABLE_LEND_OWNERSHIP
    {},
#endif
    code,
#ifdef TIP3_ENABLE_ALLOWANCE
    {},
#endif
    workchain_id }; }  *)

Definition prepare_wallet_data (name:XString)(symbol:XString)(decimals:XUInteger8)(root_public_key:XUInteger256)
                               (wallet_public_key:XUInteger256)(root_address:address)(owner_address:XMaybe address)
                               (code:cell)(workchain_id:XUInteger8) :
UExpression TONTokenWalletClassTypes.DTONTokenWalletLRecord false.
 	 refine {{ return_ [ #{name} , #{symbol} , #{decimals} , 0 , 
                       #{root_public_key} , #{wallet_public_key} , 
                       #{root_address} , #{owner_address} , {} ,
                       #{code} , {} , #{workchain_id} ] }} .
Defined .

 Definition prepare_wallet_data_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  
( name : URValue ( XString ) a1 ) 
( symbol : URValue ( XString ) a2 ) 
( decimals : URValue ( XUInteger8 ) a3 ) 
( root_public_key : URValue ( XUInteger256 ) a4 ) 
( wallet_public_key : URValue ( XUInteger256 ) a5 ) 
( root_address : URValue ( address ) a6 ) 
( owner_address : URValue ( XMaybe address ) a7 ) 
( code : URValue cell a8 ) 
( workchain_id : URValue ( XUInteger8 ) a9 ) : URValue TONTokenWalletClassTypes.DTONTokenWalletLRecord  
( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_wallet_data 
 name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
 Notation " 'prepare_wallet_data_' '(' x1 ',' x2 ',' x3 ',' x4 ',' x5 ',' x6 ',' x7 ',' x8 ',' x9 ')' " := 
 ( prepare_wallet_data_right 
 x1 x2 x3 x4 x5 x6 x7 x8 x9 ) 
 (in custom URValue at level 0 , 
   x1 custom URValue at level 0 
 , x2 custom URValue at level 0 
 , x3 custom URValue at level 0 
 , x4 custom URValue at level 0 
 , x5 custom URValue at level 0 
 , x6 custom URValue at level 0 
 , x7 custom URValue at level 0 
 , x8 custom URValue at level 0 
 , x9 custom URValue at level 0 ) : ursus_scope . 

(*************************************************************)
(*AL: ???????????????*)
 Definition workchain_id : UExpression XUInteger8 false . 
 	 	 	 refine {{ return_ {} (* Std :: get < addr_std > ( Address { tvm_myaddr () } () ) . workchain_id_ *) }} . 
 Defined . 

 Definition workchain_id_right  : URValue XUInteger8 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) workchain_id ) . 
 
 Notation " 'workchain_id_' '(' ')' " := ( workchain_id_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

 (*************************************************************)
 
Definition prepare_wallet_state_init_and_addr (wallet_data : TONTokenWalletClassTypes.DTONTokenWalletLRecord )
 : UExpression ( StateInitLRecord # uint256 ) false .
(* refine {{ if ( #{TIP3_ENABLE_EXTERNAL} )
                        then  { { _:UEf } } (* wallet_replay_protection_t::init()  *)
                        else  { { _:UEf } } ; { _ } }}. *)
 	 	 refine {{ new 'wallet_data_cl : cell @ "price_data_cl" :=  
                       prepare_persistent_data_ ( {} , #{wallet_data} )  ; { _ } }} .
 	 	 refine {{ new 'wallet_init : StateInitLRecord @ "pair_init" :=
                   [$
                         {} ⇒ { StateInit_ι_split_depth } ;
                         {} ⇒ { StateInit_ι_special } ;
                         {} ⇒ { StateInit_ι_code } ;
                         {} ⇒ { StateInit_ι_data } ;
                         {} ⇒ { StateInit_ι_library }
                    $] ; { _ } }}.
 	 	 refine {{ new 'wallet_init_cl : cell @ "price_init_cl" := {} (* build(wallet_init).make_cell() *) ; { _ } }} .
 	 	 refine {{ return_ [ !{wallet_init} , tvm_hash(!{wallet_init_cl}) ] }} .
Defined.

Definition prepare_wallet_state_init_and_addr_right {b1} 
(x0: URValue TONTokenWalletClassTypes.DTONTokenWalletLRecord b1 ) 
: URValue (StateInitLRecord # uint256) ( orb false b1 ) :=
   wrapURExpression (ursus_call_with_args (LedgerableWithArgs:=λ1) prepare_wallet_state_init_and_addr x0).    

Notation " 'prepare_wallet_state_init_and_addr_' '(' x0  ')' " := 
                                         (prepare_wallet_state_init_and_addr_right x0)  
   (in custom URValue at level 0 , 
    x0 custom URValue at level 0) : ursus_scope.

 Definition calc_wallet_init ( pubkey : ( XUInteger256 ) ) ( owner_addr : ( address ) ) 
: UExpression ( StateInitLRecord # address ) false . 
(*  	 	 refine {{ new 'wallet_data : ( TONTokenWalletClassTypes.DTONTokenWalletLRecord ) @ "wallet_data" := 
                  prepare_wallet_data_ ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ pubkey }) , tvm_myaddr () , optional_owner_ ( (#{ owner_addr }) ) , _wallet_code_ ->get_default () ,  workchain_id_ ( ) ) ; { _:UEf } }} . 
 *) 	 	 refine {{ new ( 'wallet_init:StateInitLRecord , 'dest_addr:address ) @ ( "wallet_init" , "dest_addr" ) := 
                              prepare_wallet_state_init_and_addr_ ( {} (*TODO! !{wallet_data} *) ) ; { _ } }} . 
 	 	 refine {{ new 'dest : ( address ) @ "dest" := 
                         {} (* Address :: make_std ( workchain_id_ () , dest_addr ) *) ; { _ } }} . 
 	 	 refine {{ return_ [ !{wallet_init} , (!{ dest }) ] }} . 
 Defined . 
 
 Definition calc_wallet_init_right { a1 a2 }  ( pubkey : URValue ( XUInteger256 ) a1 ) ( owner_addr : URValue ( address ) a2 ) : URValue ( StateInitLRecord # address ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_wallet_init 
 pubkey owner_addr ) . 
 
 Notation " 'calc_wallet_init_' '(' pubkey ',' owner_addr ')' " := 
 ( calc_wallet_init_right 
 pubkey owner_addr ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 
 , owner_addr custom URValue at level 0 ) : ursus_scope . 

 
 
 Definition deployWallet ( pubkey : ( XUInteger256 ) ) ( internal_owner : ( address ) ) ( tokens : ( XUInteger128 ) ) ( grams : ( XUInteger128 ) ) : UExpression address true . 
 	 	 	 refine {{ check_owner_ ( FALSE ) ; { _ } }} . 
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ require_ ( ( (_total_granted_ + (#{ tokens })) <= _total_supply_ ) , error_code::not_enough_balance ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( ( (#{ pubkey }) != 0 ) \\ 
             ( (* std::get < addr_std > ( (#{ internal_owner }) () ) . address *) {} ) != 0 ) , error_code::define_pubkey_or_internal_owner ) ; { _ } }} . 
 	 	 refine {{ new 'answer_addr : address @ "answer_addr" := {} ; { _ } }} . 
 	 	 refine {{ if ( #{Internal} ) then { {_:UEf} } else { {_:UEf} } ; { _ } }} . 
 	 	 	 refine {{ new 'value_gr:XUInteger @ "value_gr" := int_value () ; { _ } }} . 
 	 	 	 refine {{ tvm_rawreserve ( (tvm_balance ()) - !{value_gr} , rawreserve_flag::up_to ) ; { _ } }} . 
 	 	 	 refine {{ {answer_addr} := int_sender () }} . 
 	     refine {{ {answer_addr} := tvm_myaddr () }} . 

 	 	 refine {{ new ( 'wallet_init:StateInitLRecord , 'dest:address ) @ ( "wallet_init" , "dest" ) :=  
                           calc_wallet_init_  ( (#{ pubkey }) , (#{ internal_owner }) ) ; { _ } }} . 


(*      refine {{ temporary_data::setglob ( global_id::answer_id , return_func_id () - > get () ) ; { _ } }} .  *)
(*      refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; { _ } }} .  *)
(*      refine {{ dest_handle.deploy ( wallet_init , Grams ( (#{ grams }) . get () ) ) . accept ( (#{ tokens }) , answer_addr , (#{ grams }) ) ; { _ } }} .  *)
     refine {{ _total_granted_ += (#{ tokens }) ; { _ } }} . 
(*      refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; { _ } }} .  *)
     refine {{ return_ !{dest} }} . 
 Defined . 
 
 
 
 
 Definition deployEmptyWallet ( pubkey : ( XUInteger256 ) ) ( internal_owner : ( address ) ) ( grams : ( XUInteger128 ) ) : UExpression address true . 
 	 	 	 refine {{ require_ ( ( ( (#{pubkey}) != 0 ) \\ ((*std::get<addr_std>((#{ internal_owner })()).address*) {} != 0 ) ) , error_code::define_pubkey_or_internal_owner ) ; { _ } }} . 
 	 	 refine {{ new 'value_gr : ( XUInteger ) @ "value_gr" := int_value () ; { _ } }} . 
 	 	 refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr }) , rawreserve_flag::up_to ) ; { _ } }} . 
 	 	 refine {{ new ( 'wallet_init:StateInitLRecord , 'dest:address ) @ ( "wallet_init" , "dest" ) := 
                                   calc_wallet_init_ ( (#{ pubkey }) , (#{ internal_owner }) ) ; { _ } }} . 
(*  	 	 refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; { _ } }} .  *)
(*  	 	 refine {{ dest_handle.deploy_noop ( wallet_init , Grams ( (#{ grams }) . get () ) ) ; { _ } }} .  *)
(*  	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; { _ } }} .  *)
 	 	 refine {{ return_ !{dest} }} . 
 Defined . 
 
 
 
 
 Definition grant ( dest : ( address ) ) ( tokens : ( XUInteger128 ) ) ( grams : ( XUInteger128 ) ) : UExpression PhantomType true . 
 	 	 refine {{ check_owner_ ( FALSE ) ; { _ } }} . 
 	 	 refine {{ require_ ( ( (_total_granted_ + (#{ tokens })) <= _total_supply_ ) , error_code::not_enough_balance ) ; { _ } }} . 
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ new 'answer_addr:address @ "answer_addr" := {} ; { _ } }} . 
 	 	 refine {{ new 'msg_flags : ( XUInteger ) @ "msg_flags" := 0 ; { _ } }} . 
refine {{ new 'grams_:XUInteger128 @ "grams_" := #{grams} ; { _ } }}.
 	 	 refine {{ if ( #{Internal} ) then { {_:UEf} } else { {_:UEf} } ; { _ } }} . 
 	 	 	 refine {{ new 'value_gr:XUInteger @ "value_gr" := int_value () ; { _ } }} . 
 	 	 	 refine {{ tvm_rawreserve ( tvm_balance () - (!{value_gr} ) , rawreserve_flag::up_to ) ; { _ } }} . 
 	 	 	 refine {{ { msg_flags } := 1 (* SEND_ALL_GAS *) ; { _ } }} . 
 	 	 	 refine {{ { grams_ } := 0 ; { _ } }} . 
 	 	 	 refine {{ {answer_addr} := int_sender () }} . 
 	     refine {{ {answer_addr} := tvm_myaddr () }} . 

(*      refine {{ ITONTokenWalletPtr dest_handle ( (#{ dest }) ) ; { _ } }} .  *)
(*      refine {{ dest_handle ( Grams ( (#{ grams_ }) . get () ) , (!{ msg_flags }) ) . accept ( (#{ tokens }) , answer_addr , uint128 ( 0 ) ) ; { _ } }} .  *)
     refine {{ _total_granted_ += (#{ tokens }) ; { _ } }} . 
     refine {{ return_ {} }} . 
 Defined . 
 
Definition mint ( tokens : ( XUInteger128 ) ) : UExpression boolean true . 
 	 	 refine {{ check_owner_ ( FALSE ) ; { _ } }} .  
 	 	 refine {{ tvm_accept () ; { _ } }} . 
 	 	 refine {{ if ( #{Internal} ) then { {_:UEf} } ; { _ } }} . 
 	 	 	 refine {{ new 'value_gr:XUInteger@"value_gr" := int_value () ; { _ } }} . 
 	 	 	 refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr }) , rawreserve_flag::up_to ) }} . 
 	 refine {{ _total_supply_ += (#{ tokens }) ; { _ } }} . 
(*  	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; { _ } }} .  *)
 	 refine {{ return_ TRUE }} . 
Defined . 
 
 
 
 
 Definition requestTotalGranted : UExpression XUInteger128 false . 
 	 	 	 refine {{ new 'value_gr : ( XUInteger ) @ "value_gr" := int_value () ; { _ } }} . 
 	 	 refine {{ tvm_rawreserve ( tvm_balance () - (!{ value_gr }) , rawreserve_flag::up_to ) ; { _ } }} . 
(*  	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; { _ } }} .  *)
 	 	 refine {{ return_ _total_granted_ }} . 
 Defined . 
 
 
 
 
 Definition getName : UExpression XString false . 
 	 	 	 refine {{ return_ _name_ }} . 
 Defined . 
 
 
 
 
 Definition getSymbol : UExpression XString false . 
 	 	 	 refine {{ return_ _symbol_ }} . 
 Defined . 
 
 
 
 
 Definition getDecimals : UExpression XUInteger8 false . 
 	 	 	 refine {{ return_ _decimals_ }} . 
 Defined . 
 
 
 
 
 Definition getRootKey : UExpression XUInteger256 false . 
 	 	 	 refine {{ return_ _root_public_key_ }} . 
 Defined . 
 
 
 
 
 Definition getTotalSupply : UExpression XUInteger128 false . 
 	 	 	 refine {{ return_ _total_supply_ }} . 
 Defined . 
 
 
 
 
 Definition getTotalGranted : UExpression XUInteger128 false . 
 	 	 	 refine {{ return_ _total_granted_ }} . 
 Defined . 
 
 
 
 
 Definition hasWalletCode : UExpression boolean false . 
 	 	 	 refine {{ return_ (? _wallet_code_) }} . 
 Defined . 
 
 
 
 
 Definition getWalletCode : UExpression cell true . 
 	 	 	 refine {{ return_ (_wallet_code_ -> get ()) }} . 
 Defined . 
 
 
 
 
 Definition getWalletAddress ( pubkey : ( XUInteger256 ) ) ( owner : ( address ) ) : UExpression address false . 
 	 	 	 refine {{ return_ second ( calc_wallet_init_ ( (#{ pubkey }) , (#{ owner }) ) ) }} . 
 Defined . 
 
 
(*  Definition Args := args_struct_t<&ITONTokenWallet::accept>; *)
 
 Definition _on_bounced ( msg : cell ) ( msg_body : ( XSlice ) ) : UExpression XUInteger true . 
 	 	 refine {{ tvm_accept () ; { _ } }} . 
(*  	 	 refine {{ new 'p : parser @ "p" := ( (#{ msg_body }) ) ; { _ } }} .  *)
 	 	 refine {{ require_ ( ( (* p ↑ ldi ( #{32} ) *) {} == #{(-1)%Z} ) , error_code::wrong_bounced_header ) ; { _ } }} . 
 	 	 refine {{ new 'opt_hdr : ( XMaybe address ) @ "opt_hdr" := {} ; { _ } }} . 
(*  	 	 refine {{ [ opt_hdr , =p ] := parse_continue < abiv2::internal_msg_header_with_answer_id > ( p ) ; { _ } }} .  *)
 	 	 refine {{ require_ ( ( ? !{opt_hdr} && {} (* opt_hdr -> function_id == id_v < &ITONTokenWallet::accept > *) ) , 
                                               error_code::wrong_bounced_header ) ; { _ } }} . 
 	 	 refine {{ new 'args : ( address ) @ "args" := {} 
                              (* parse ( p , error_code::wrong_bounced_args ) *) ; { _ } }} . 
 	 	 refine {{ new 'bounced_val : ( XUInteger (* auto *) ) @ "bounced_val" := {} (* (!{ args }) ↑ auto:tokens *) ; { _ } }} . 

(* very controversial things: *)

 	 	 refine {{ new ( 'hdr:XUInteger , 'persist:DRootTokenContractLRecord ) @ ( "hdr" , "persist" ) := {}
(*      load_persistent_data < IRootTokenContract , root_replay_protection_t , DRootTokenContract > ()*) ; { _ } }} .  
 	 	 refine {{ require_ ( ( (!{bounced_val}) <= ((!{persist}) ↑ DRootTokenContract.total_granted_) ) , error_code::wrong_bounced_args ) ; { _ } }} . 
 	 	 refine {{ (({persist}) ↑ DRootTokenContract.total_granted_) -= (!{ bounced_val }) ; { _ } }} . 
(*  	 	 refine {{ save_persistent_data < IRootTokenContract , root_replay_protection_t > ( hdr , persist ) ; { _ } }} .  *)
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 
 
 
 Definition getWalletCodeHash : UExpression XUInteger256 false . 
 	 	 	 refine {{ return_ {} (* __builtin_tvm_hashcu ( _wallet_code_ ) *) }} . 
 Defined . 
 
 
 
 
 Definition _fallback ( _ : cell ) ( _ : XSlice ) : UExpression XUInteger false . 
 	 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 
 Definition prepare_root_state_init_and_addr ( root_code : cell ) ( root_data : ( DRootTokenContractLRecord ) ) : UExpression ( StateInitLRecord * XUInteger256 ) false . 
 	 	 	 refine {{ new 'root_data_cl : cell @ "root_data_cl" := 
            prepare_persistent_data_ ( (* root_replay_protection_t::init () *) {} , (#{ root_data }) ) ; { _ } }} . 
 	 	 refine {{ new 'root_init : ( StateInitLRecord ) @ "root_init" := 	 	 
 	 	 	                        [ {} , {} , (#{ root_code }) ->set ()  , (!{ root_data_cl }) ->set () , {} ] ; { _ } }} . 
 	 	 refine {{ new 'root_init_cl : cell @ "root_init_cl" := {} 
                          (*  build ( (!{ root_init }) ) . make_cell () *) ; { _ } }} . 
 	 	 refine {{ return_ [ (!{ root_init }) , tvm_hash ( (!{ root_init_cl }) ) ] }} . 
 Defined . 
 
End FuncsInternal.
End Funcs.








