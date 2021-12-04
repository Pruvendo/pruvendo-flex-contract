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

Require Import Project.CommonTypes.
Require Import Project.CommonConstSig.

Require Import TONTokenWallet.Ledger.
Require Import TONTokenWallet.ClassTypesNotations.
Require Import TONTokenWallet.ClassTypes.
Require Import TONTokenWallet.Functions.FuncSig.
Require Import TONTokenWallet.Functions.FuncNotations.

Require TONTokenWallet.Interface.

Require Import TradingPair.ClassTypes.
Require Import XchgPair.ClassTypes.
Require Import Wrapper.ClassTypes.
Require Import TONTokenWallet.ClassTypes.
Require Import Wrapper.ClassTypesNotations.

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.

Module Funcs (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .
Import co.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 

Module TradingPairClassTypes := TradingPair.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module XchgPairClassTypes := XchgPair.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module WrapperClassTypesModule := Wrapper.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module TONTokenWalletClassTypesModule := TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule.

Module Import TONTokenWalletModuleForTON := Contracts.TONTokenWallet.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module Import WrapperModuleForTON := Wrapper.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.


Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

(*move this somewhere*)
Existing Instance LedgerPruvendoRecord.

Definition filter_lend_ownerhip_map : UExpression ( (lend_ownership_map) # uint128 ) false . 
	refine {{ if ( _lend_ownership_ -> empty () ) then { return_ {} } ; {_} }} .
	refine {{ new 'now_v : uint256 @ "now_v" := tvm_now () ; {_} }} . 
	refine {{ new 'rv : lend_ownership_map @ "rv" := {} ; {_} }} . 
	refine {{ new 'lend_balance : uint128 @ "lend_balance" := {} ; {_} }} . 
    refine {{ for ( 'v : _lend_ownership_) do { {_ : UEf} } ; { _ } }}.
	refine {{ if ( ( !{now_v} ) < second ( {v} )  ↑ lend_record.lend_finish_time ) then { {_ : UEf } } }}.
	refine {{ {rv}  -> insert ( {v} ) ; { _ } }}.

	refine {{ {lend_balance} += second ({v}) ↑ lend_record.lend_balance }}.
    refine {{ _lend_ownership_ := ( !{rv} ) ; {_} }} .
    refine {{ return_ [ !{rv} , !{lend_balance} ] }} .
Defined .
 
Definition filter_lend_ownerhip_map_right : URValue ( lend_ownership_map # uint128 ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) filter_lend_ownerhip_map ) . 
 
Notation " 'filter_lend_ownerhip_map_' '(' ')' " := ( filter_lend_ownerhip_map_right ) 
 												    ( in custom URValue at level 0 ) : ursus_scope . 

Definition is_internal_owner : UExpression boolean false . 
   refine {{ return_ _owner_address_ -> has_value () }} . 
Defined . 
 
Definition is_internal_owner_right : URValue boolean false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) is_internal_owner ) . 
 
Notation " 'is_internal_owner_' '(' ')' " := ( is_internal_owner_right ) 
 											 ( in custom URValue at level 0 ) : ursus_scope . 

Definition check_internal_owner ( original_owner_only : boolean ) 
								( allowed_for_original_owner_in_lend_state : boolean )  
								: UExpression uint128 true . 
	refine {{ new ( 'filtered_map: mapping addr_std_fixed lend_recordLRecord, 'actual_lend_balance: uint128 ) 
					@ ( "filtered_map" , "actual_lend_balance" ) := filter_lend_ownerhip_map_ ( ) ; {_} }} . 
	refine {{ if ( !{actual_lend_balance} > 0 ) then { {_:UEt} } else { {_:UEt} } }} . 
	refine {{ if ( (#{ allowed_for_original_owner_in_lend_state }) ) then { {_:UEt} } ; {_} }} .
	refine {{ require_ ( (is_internal_owner_ ( )) ,  error_code::internal_owner_disabled  ) ; {_} }} . 
	refine {{ if ( _owner_address_ -> get () == int_sender () ) then { {_:UEf} } }} . 
	refine {{ return_ (_balance_ - (!{actual_lend_balance}) ) }} . 
	refine {{ require_ ( ( ~ (#{ original_owner_only }) ) ,  error_code::only_original_owner_allowed ) ; {_} }} . 
	refine {{ new 'elem : ( optional lend_recordLRecord ) @ "elem" := !{filtered_map} -> lookup ( int_sender () ) ; {_} }} . 
	refine {{ require_ ( !{ elem } ,  error_code::message_sender_is_not_my_owner  ) ; {_} }} . 
	refine {{ return_ min ( _balance_ , ( *!{elem} ) ↑ lend_record.lend_balance ) }} . 
	refine {{ require_ ( (is_internal_owner_ ( )) , error_code::internal_owner_disabled  ) ; {_} }} . 
	refine {{ require_ ( ( ( * _owner_address_ ) == int_sender () ) , error_code::message_sender_is_not_my_owner  ) ; {_} }} . 
	refine {{ return_ _balance_ }} .  
Defined. 

Definition check_internal_owner_right { a1 a2 }  ( original_owner_only : URValue boolean a1 ) 
												 ( allowed_for_original_owner_in_lend_state : URValue boolean a2 ) : URValue uint128 true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_internal_owner original_owner_only allowed_for_original_owner_in_lend_state ) . 
 
Notation " 'check_internal_owner_' '(' original_owner_only ',' allowed_for_original_owner_in_lend_state ')' " := 
 ( check_internal_owner_right original_owner_only allowed_for_original_owner_in_lend_state ) 
 (in custom URValue at level 0 , original_owner_only custom URValue at level 0 
 , allowed_for_original_owner_in_lend_state custom URValue at level 0 ) : ursus_scope . 

Definition check_external_owner : UExpression uint128 true . 
	refine {{ require_ ( ( ~  is_internal_owner_ ( ) ) ,  error_code::internal_owner_enabled  ) ; {_} }} . 
	refine {{ require_ ( ( msg_pubkey () == _wallet_public_key_ ) , error_code::message_sender_is_not_my_owner ) ; {_} }} . 
	refine {{ tvm_accept () ; {_} }} . 
	refine {{ new ( 'filtered_map: mapping addr_std_fixed lend_recordLRecord , 'lend_balance:uint128 ) @
			( "filtered_map" , "lend_balance" ) := filter_lend_ownerhip_map_ ( ) ; {_} }} . 
	refine {{ require_ ( !{filtered_map} -> empty ()  ,  error_code::wallet_in_lend_owneship  ) ; {_} }} . 
	refine {{ return_ _balance_ }} . 
Defined . 
 
Definition check_external_owner_right  : URValue uint128 true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) check_external_owner ) . 
 
Notation " 'check_external_owner_' '(' ')' " := ( check_external_owner_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition check_owner ( original_owner_only : boolean ) ( allowed_in_lend_state : boolean ) : UExpression uint128 true . 
	refine {{ {if Internal then _ else _} ; {_} }} .
	refine {{ exit_ (check_internal_owner_ ( #{original_owner_only} , #{allowed_in_lend_state} ) ) }} . 
	refine {{ exit_ (check_external_owner_ ( ) ) }} . 
	refine {{ return {} }}.
Defined.

Definition check_owner_right { a1 a2 }  ( original_owner_only : URValue boolean a1 ) 
                                        ( allowed_in_lend_state : URValue boolean a2 ) : URValue uint128 true := 
wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_owner original_owner_only allowed_in_lend_state ) . 
 
Notation " 'check_owner_' '(' original_owner_only ',' allowed_in_lend_state ')' " := 
( check_owner_right original_owner_only allowed_in_lend_state ) 
(in custom URValue at level 0 , original_owner_only custom URValue at level 0 , allowed_in_lend_state custom URValue at level 0 ) : ursus_scope .

Definition check_owner_left { R a1 a2 }  ( original_owner_only : URValue boolean a1 ) 
                                         ( allowed_in_lend_state : URValue boolean a2 ) 
										  : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_owner original_owner_only allowed_in_lend_state ) . 
 
Notation " 'check_owner_' '(' original_owner_only ',' allowed_in_lend_state ')' " := 
 ( check_owner_left original_owner_only allowed_in_lend_state ) 
 (in custom ULValue at level 0 , original_owner_only custom URValue at level 0 , allowed_in_lend_state custom URValue at level 0 ) : ursus_scope .

Definition check_transfer_requires ( tokens : uint128 ) ( grams : uint128 ) : UExpression uint128 true . 
	refine {{ new 'active_balance : uint128 @ "active_balance" := 	check_owner_ ( FALSE , FALSE ) ; {_} }} . 
	refine {{ require_ ( (#{ tokens }) <= !{ active_balance } , error_code::not_enough_balance ) ; {_} }} . 
	refine {{ { if Internal then _ else _ } ; { _ } }} . 
	refine {{ require_ ( int_value () >= # {min_transfer_costs} ,  error_code::not_enough_tons_to_process  ) }} . 
	refine {{ require_ ( ( #{ grams } >= # {min_transfer_costs} )  && 
	                     ( tvm_balance () > #{ grams } )  ,  error_code::not_enough_tons_to_process ) }} . 
	refine {{ return_ !{ active_balance } }} . 
Defined . 
 
Definition check_transfer_requires_right { a1 a2 } ( tokens : URValue uint128 a1 ) 
 												   ( grams : URValue uint128 a2 ) : 
													  URValue uint128 true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) check_transfer_requires tokens grams ) . 
 
Notation " 'check_transfer_requires_' '(' tokens ',' grams ')' " := 
 ( check_transfer_requires_right  tokens grams ) 
 (in custom URValue at level 0 , tokens custom URValue at level 0 , grams custom URValue at level 0 ) : ursus_scope . 

Definition fixup_answer_addr ( answer_addr : address ) : UExpression address true . 
	refine {{ if (#{ answer_addr }) ↑ address.address == 0 then { {_:UEt} } ; {_} }} . 
 	refine ( if Internal then {{ exit_ int_sender () }}
                         else {{ exit_ tvm_myaddr () }} ) . 
 	refine {{ return_ (#{ answer_addr }) }} . 
Defined . 
 
Definition fixup_answer_addr_right { a1 }  ( answer_addr : URValue address a1 ) : URValue address true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) fixup_answer_addr answer_addr ) . 
 
Notation " 'fixup_answer_addr_' '(' answer_addr ')' " := 
 ( fixup_answer_addr_right answer_addr ) 
 (in custom URValue at level 0 , answer_addr custom URValue at level 0 ) : ursus_scope . 

Definition prepare_transfer_message_flags ( grams : ULValue uint128 ) : UExpression uint false . 
	refine {{ new 'msg_flags : uint @ "msg_flags" := #{IGNORE_ACTION_ERRORS} ; {_} }} . 
	refine (if Internal then _ else  _).
	refine {{ tvm_rawreserve ( tvm_balance () - int_value () , rawreserve_flag::up_to ) ; {_} }} . 
	refine {{ { msg_flags } := # {SEND_ALL_GAS} ; {_} }} . 
	refine {{ {grams} := 0 }} . 
	refine {{ return_ !{ msg_flags } }} . 
Defined. 

Definition prepare_transfer_message_flags_right  (grams : ULValue uint128 ) : URValue uint false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1L ) prepare_transfer_message_flags grams ) . 
 
Notation " 'prepare_transfer_message_flags_' '(' grams ')' " := 
 ( prepare_transfer_message_flags_right grams ) 
 (in custom URValue at level 0 , grams custom URValue at level 0 ) : ursus_scope . 
 
Definition update_spent_balance ( tokens : uint128 ) 
								( return_ownership : boolean ) : UExpression PhantomType true . 
	refine {{ _balance_ -= #{ tokens } ; {_} }} . 
	refine {{ if ( _lend_ownership_ -> empty () ) then { exit_ {} } ; {_} }} . 
	refine {{ new 'sender : address @ "sender" := int_sender () ; {_} }} . 
	refine {{ if #{ return_ownership } then { {_:UEf} } else { {_:UEf} } }} . 
	refine {{ _lend_ownership_ -> erase ( !{ sender } ) }} . 
	refine {{ new 'v : lend_recordLRecord @ "v" := _lend_ownership_ [[ !{ sender } ]]  ; {_} }} . 
	refine {{ {v} ↑ lend_record.lend_balance -= #{ tokens } ; {_} }} . 
	refine {{ if ( ~ (!{ v } ↑ lend_record.lend_balance) ) then { {_:UEf} } else { {_:UEf} } }} . 
	refine {{ _lend_ownership_ -> erase ( !{ sender } ) }} . 
	refine {{ _lend_ownership_ -> set_at ( !{ sender } , !{v} ) }} . 
Defined . 

Definition update_spent_balance_left { R a1 a2 }  ( tokens : URValue uint128 a1 ) 
 												   ( return_ownership : URValue boolean a2 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) update_spent_balance tokens return_ownership ) . 
 
Notation " 'update_spent_balance_' '(' tokens ',' return_ownership ')' " := 
 ( update_spent_balance_left tokens return_ownership ) 
 (in custom ULValue at level 0 , tokens custom URValue at level 0 , return_ownership custom URValue at level 0 ) : ursus_scope .

Definition get_owner_addr : UExpression address false. 
	refine {{ return_ ( (? _owner_address_ ) ? ( * _owner_address_ )  : [ #{0%Z} , 0 ] ) }} . 
Defined . 
 
Definition get_owner_addr_right  : URValue address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) get_owner_addr ) . 
 
Notation " 'get_owner_addr_' '(' ')' " := 
 ( get_owner_addr_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 


Definition transfer_impl ( answer_addr : address ) 
						 ( too : address ) 
                         ( tokens : uint128 ) 
                         ( grams : uint128 ) 
                         ( return_ownership : boolean ) 
                         ( send_notify : boolean ) 
                         ( payload : cell ) : UExpression PhantomType true . 
	refine {{ new 'active_balance : uint128 @ "active_balance" := 
              check_transfer_requires_ ( #{tokens} , #{grams} ) ; {_} }} . 
 	refine {{ require_ ( (#{ too }) ↑ address.address != 0  ,  error_code::transfer_to_zero_address ) ; {_} }} . 
 	refine {{ tvm_accept () ; {_} }} . 
 	refine {{ new 'answer_addr_fxd : address @ "answer_addr_fxd" := fixup_answer_addr_ ( #{ answer_addr } ) ; {_} }} . 
    refine {{ new 'grams_ : uint128 @ "grams_" := #{grams} ; {_} }} .
    refine {{ new 'msg_flags : uint @ "msg_flags" := prepare_transfer_message_flags_ ( {grams_} ) ; {_} }} . 
	refine ( let dest_handle_ptr := {{ ITONTokenWalletPtr [[ #{ too }  ]] }} in 
              {{ {dest_handle_ptr} with [$ #{ grams } ⇒ { Messsage_ι_value } ;
			  							   !{ msg_flags } ⇒ { Messsage_ι_flags } $] 
                  ⤳ .internalTransfer_ ( #{ tokens } , !{answer_addr_fxd} , _wallet_public_key_ ,
										  get_owner_addr_ ( ) , #{ send_notify } , #{ payload } ) ; {_} }} ). 
	refine {{ update_spent_balance_ ( #{ tokens } , #{ return_ownership } ) }} . 
Defined. 

Definition transfer_impl_left { R a1 a2 a3 a4 a5 a6 a7 } ( answer_addr : URValue address a1 ) 
														 ( too : URValue address a2 ) 
														 ( tokens : URValue uint128 a3 ) 
														 ( grams : URValue uint128 a4 ) 
														 ( return_ownership : URValue boolean a5 ) 
														 ( send_notify : URValue boolean a6 ) 
														 ( payload : URValue cell a7 ) : UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) transfer_impl answer_addr too tokens grams return_ownership send_notify payload ) . 
 
Notation " 'transfer_impl_' '(' answer_addr ',' too ',' tokens ',' grams ',' return_ownership ',' send_notify ',' payload ')' " := 
 ( transfer_impl_left answer_addr too tokens grams return_ownership send_notify payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 , too custom URValue at level 0 
 , tokens custom URValue at level 0 , grams custom URValue at level 0 , return_ownership custom URValue at level 0 
 , send_notify custom URValue at level 0 , payload custom URValue at level 0 ) : ursus_scope . 

Definition transfer ( answer_addr : address ) ( too : address ) ( tokens : uint128 ) 
				    ( grams : uint128 ) ( return_ownership : boolean ) : UExpression PhantomType true . 
 refine {{ transfer_impl_ ( #{ answer_addr } , #{ too } , #{ tokens } , #{ grams } , 
                            #{ return_ownership } , FALSE , builder () -> endc ()  ) }} . 
Defined . 

Definition transferWithNotify ( answer_addr : address ) ( too : address ) ( tokens : uint128 ) 
							  ( grams : uint128 ) ( return_ownership : boolean ) ( payload : cell ) 
							  : UExpression PhantomType true . 
	refine {{ temporary_data::setglob ( global_id::answer_id , 
										return_func_id_ () -> get () ) ; {_} }} . 
	refine {{ transfer_impl_ ( #{ answer_addr } , 
							#{ too } , 
							#{ tokens } , 
							#{ grams } , 
							#{ return_ownership }, 
							TRUE , 
							#{ payload }) ; {_} }} . 
	refine {{ return_ {} }}.
Defined . 

Definition prepare_wallet_data  ( name : String ) 
								( symbol : String ) 
								( decimals : uint8 ) 
								( root_public_key : uint256 ) 
								( wallet_public_key : uint256 ) 
								( root_address : address ) 
								( owner_address : optional address ) 
								( code : cell ) 
								( workchain_id : int ) 
								: UExpression DTONTokenWalletLRecord false . 
	refine {{ return_ [ #{ name } , 
	                     #{ symbol } , 
						 #{ decimals } , 
						 0 , 
						 #{ root_public_key } , 
						 #{ wallet_public_key } , 
						 #{ root_address } , 
						 #{ owner_address } , 
						 {} , 
						 #{ code } , {} , 
						 #{ workchain_id } ] }} . 
Defined . 
 
Definition prepare_wallet_data_right { a1 a2 a3 a4 a5 a6 a7 a8 a9 }  
    ( name : URValue String a1 ) 
	( symbol : URValue String a2 ) 
	( decimals : URValue uint8 a3 ) 
	( root_public_key : URValue uint256 a4 ) 
	( wallet_public_key : URValue uint256 a5 ) 
	( root_address : URValue address a6 ) 
	( owner_address : URValue (optional address) a7 ) 
	( code : URValue cell a8 ) 
	( workchain_id : URValue int a9 ) : URValue DTONTokenWalletLRecord ( orb ( orb ( orb ( orb ( orb ( orb ( orb ( orb a9 a8 ) a7 ) a6 ) a5 ) a4 ) a3 ) a2 ) a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) prepare_wallet_data name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) . 
 
Notation " 'prepare_wallet_data_' '(' name ',' symbol ',' decimals ',' root_public_key ',' wallet_public_key ',' root_address ',' owner_address ',' code ',' workchain_id ')' " := 
 ( prepare_wallet_data_right name symbol decimals root_public_key wallet_public_key root_address owner_address code workchain_id ) 
 (in custom URValue at level 0 , name custom URValue at level 0 , symbol custom URValue at level 0 
 , decimals custom URValue at level 0 , root_public_key custom URValue at level 0 , wallet_public_key custom URValue at level 0 
 , root_address custom URValue at level 0 , owner_address custom URValue at level 0 
 , code custom URValue at level 0 , workchain_id custom URValue at level 0 ) : ursus_scope . 

Definition prepare_wallet_state_init_and_addr ( wallet_data : DTONTokenWalletLRecord ) 
           									  : UExpression ( StateInitLRecord # uint256 ) false . 
	refine {{ new 'wallet_data_cl : cell @ "wallet_data_cl" := 
                        prepare_persistent_data_ ( {} , #{ wallet_data} ) ; {_} }} . 
	refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 	 	 
	         [ {} , {} , ((#{ wallet_data}) ↑ DTONTokenWallet.code_) -> set () , !{wallet_data_cl} -> set () , {} ] ; {_} }} . 
	refine {{ new 'wallet_init_cl : cell @ "wallet_init_cl" :=  
				 build ( σ (!{ wallet_init }) ) -> make_cell ()  ; {_} }} . 
	refine {{ return_ [ (!{ wallet_init }) , tvm_hash ( !{ wallet_init_cl } ) ] }} . 
Defined . 
 
Definition prepare_wallet_state_init_and_addr_right { a1 }  ( wallet_data : URValue DTONTokenWalletLRecord a1 ) 
                                                                        : URValue ( StateInitLRecord * uint256 ) a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) prepare_wallet_state_init_and_addr wallet_data ) . 
 
Notation " 'prepare_wallet_state_init_and_addr_' '(' wallet_data ')' " := 
 ( prepare_wallet_state_init_and_addr_right wallet_data ) 
 (in custom URValue at level 0 , wallet_data custom URValue at level 0 ) : ursus_scope . 

Definition optional_owner ( owner : address ) : UExpression (optional address) false . 
	 refine {{ return_ ( ( ? ( (#{owner}) ↑ address.address ) ) ? (#{owner}) -> set () : {} )  }} . 
 Defined . 
 
Definition optional_owner_right { a1 }  ( owner : URValue address a1 ) : URValue (optional address) a1 := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ1 ) optional_owner owner ) . 
 
Notation " 'optional_owner_' '(' owner ')' " := ( optional_owner_right owner ) 
 (in custom URValue at level 0 , owner custom URValue at level 0 ) : ursus_scope .

Definition calc_wallet_init_hash ( pubkey : uint256 ) ( internal_owner : address ) 
								 : UExpression ( StateInitLRecord # uint256 ) false . 
	refine {{ new 'wallet_data : DTONTokenWalletLRecord @ "wallet_data" := 
		prepare_wallet_data_ ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ pubkey }) , _root_address_ , optional_owner_ ( (#{ internal_owner }) ) , _code_ , _workchain_id_ ) ; {_} }} . 
	refine {{ return_ prepare_wallet_state_init_and_addr_ ( (!{ wallet_data }) ) }} . 
Defined . 
 
Definition calc_wallet_init_hash_right { a1 a2 }  ( pubkey : URValue uint256 a1 ) 
 									               ( internal_owner : URValue address a2 ) : URValue ( StateInitLRecord # uint256 ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_wallet_init_hash pubkey internal_owner ) . 
 
Notation " 'calc_wallet_init_hash_' '(' pubkey ',' internal_owner ')' " := ( calc_wallet_init_hash_right pubkey internal_owner ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 , internal_owner custom URValue at level 0 ) : ursus_scope . 

Definition expected_sender_address ( sender_public_key : uint256 ) ( sender_owner : address ) : UExpression uint256 false . 
 	 	 refine {{ return_ second ( calc_wallet_init_hash_ ( #{ sender_public_key } , #{ sender_owner } ) ) }} . 
Defined . 
 
Definition expected_sender_address_right { a1 a2 }  ( sender_public_key : URValue uint256 a1 ) 
                                                    ( sender_owner : URValue address a2 ) : URValue uint256 ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) expected_sender_address sender_public_key sender_owner ) . 
 
Notation " 'expected_sender_address_' '(' sender_public_key ',' sender_owner ')' " := 
 ( expected_sender_address_right sender_public_key sender_owner ) 
 (in custom URValue at level 0 , sender_public_key custom URValue at level 0 
 , sender_owner custom URValue at level 0 ) : ursus_scope .

Definition calc_wallet_init ( pubkey : uint256 ) ( internal_owner : address ) 
                            : UExpression ( StateInitLRecord # address ) false . 
	refine {{ new ( 'wallet_init:StateInitLRecord , 'dest_addr:uint256 ) @ 
                ( "wallet_init" , "dest_addr" ) := 
	             calc_wallet_init_hash_ ( (#{ pubkey }) , (#{ internal_owner }) ) ; {_} }} . 
	refine {{ new 'dest : address @ "dest" := [ _workchain_id_ , !{dest_addr} ] ; {_} }} . 
 	refine {{ return_ [ !{wallet_init} , (!{ dest }) ] }} . 
Defined . 

Definition calc_wallet_init_right { a1 a2 }  ( pubkey : URValue uint256 a1 ) 
 											  ( internal_owner : URValue address a2 ) 
											   : URValue ( StateInitLRecord # address ) ( orb a2 a1 ) := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ2 ) calc_wallet_init pubkey internal_owner ) . 
 
Notation " 'calc_wallet_init_' '(' pubkey ',' internal_owner ')' " := ( calc_wallet_init_right pubkey internal_owner ) 
 (in custom URValue at level 0 , pubkey custom URValue at level 0 , internal_owner custom URValue at level 0 ) : ursus_scope .

Definition transfer_to_recipient_impl ( answer_addr : address ) ( recipient_public_key : uint256 ) 
									  ( recipient_internal_owner : address ) ( tokens : uint128 ) 
								      ( grams : uint128 ) ( deploy : boolean ) 
									  ( return_ownership : boolean ) ( send_notify : boolean ) ( payload : cell ) 
								      : UExpression PhantomType true . 
	refine {{ new 'active_balance : uint128 @ "active_balance" := check_transfer_requires_ ( #{ tokens } , #{ grams } ) ; {_} }} . 
	refine {{ tvm_accept () ; {_} }} . 
 	refine {{ new 'answer_addr_fxd : address @ "answer_addr_fxd" := fixup_answer_addr_ ( (#{ answer_addr }) ) ; {_} }} .
	refine {{ new 'grams_ : uint128 @ "grams_" := #{grams} ; {_} }} .
 	refine {{ new 'msg_flags : uint @ "msg_flags" := prepare_transfer_message_flags_ ( ({ grams_ }) ) ; {_} }} . 
 	refine {{ new ( 'wallet_init:StateInitLRecord , 'dest:address ) @
                   ( "wallet_init" , "dest" ) := calc_wallet_init_ ( #{ recipient_public_key } , #{ recipient_internal_owner } ) ; {_} }} . 
	refine {{ if ( (#{ deploy }) ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
	refine ( let dest_handle_ptr := {{ ITONTokenWalletPtr [[ !{ dest }  ]] }} in 
              {{ {dest_handle_ptr} with {} ⤳ TONTokenWallet.deploy (!{wallet_init} ) ; {_} }} ).
	refine ( let dest_handle_ptr := {{ ITONTokenWalletPtr [[ !{ dest }  ]] }} in 
              {{ {dest_handle_ptr} with [$ #{ grams } ⇒ { Messsage_ι_value } ;
			  								!{ msg_flags } ⇒ { Messsage_ι_flags } $] 
                                         ⤳ .internalTransfer_ ( #{ tokens } , !{answer_addr_fxd} , _wallet_public_key_ ,
										  get_owner_addr_ ( ) , #{ send_notify } , #{ payload } ) }} ).
	refine ( let dest_handle_ptr := {{ ITONTokenWalletPtr [[ !{ dest }  ]] }} in 
              {{ {dest_handle_ptr} with [$ #{ grams } ⇒ { Messsage_ι_value } ;
			  								!{ msg_flags } ⇒ { Messsage_ι_flags } $] 
                                         ⤳ .internalTransfer_ ( #{ tokens } , !{answer_addr_fxd} , _wallet_public_key_ ,
										 get_owner_addr_ ( ) , #{ send_notify } , #{ payload } ) }} ).
 	refine {{ update_spent_balance_ ( (#{ tokens }) , (#{ return_ownership }) ) ; {_} }} . 
 	refine {{ return_ {} }} .
Defined . 

Definition transfer_to_recipient_impl_left { R a1 a2 a3 a4 a5 a6 a7 a8 a9 }  
 											( answer_addr : URValue address a1 ) 
											( recipient_public_key : URValue uint256 a2 ) 
											( recipient_internal_owner : URValue address a3 ) 
											( tokens : URValue uint128 a4 ) 
											( grams : URValue uint128 a5 ) 
											( deploy : URValue boolean a6 ) 
											( return_ownership : URValue boolean a7 ) 
											( send_notify : URValue boolean a8 ) 
											( payload : URValue cell a9 ) 
											: UExpression R true := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ9 ) transfer_to_recipient_impl answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ) . 
 
Notation " 'transfer_to_recipient_impl_' '(' answer_addr ',' recipient_public_key ',' recipient_internal_owner ',' tokens ',' grams ',' deploy ',' return_ownership ',' send_notify ',' payload ')' " := 
 ( transfer_to_recipient_impl_left answer_addr recipient_public_key recipient_internal_owner tokens grams deploy return_ownership send_notify payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 , recipient_public_key custom URValue at level 0 
 , recipient_internal_owner custom URValue at level 0 , tokens custom URValue at level 0 , grams custom URValue at level 0 
 , deploy custom URValue at level 0 , return_ownership custom URValue at level 0 , send_notify custom URValue at level 0 
 , payload custom URValue at level 0 ) : ursus_scope . 

 
Definition transferToRecipient ( answer_addr : address ) ( recipient_public_key : uint256 ) 
							   ( recipient_internal_owner : address ) ( tokens : uint128 ) 
                               ( grams : uint128 ) ( deploy : boolean ) ( return_ownership : boolean ) 
							   : UExpression PhantomType true . 
	refine {{ transfer_to_recipient_impl_ ( #{ answer_addr } , 
                                        #{ recipient_public_key } , 
                                        #{ recipient_internal_owner } , 
                                        #{ tokens } , 
                                        #{ grams } , 
                                        #{ deploy } , 
                                        #{ return_ownership } , 
                                        FALSE , 
                                        builder () -> endc () ) ; {_} }} . 
	refine {{ return_ {} }} .
Defined . 
 
Definition transferToRecipientWithNotify ( answer_addr : address ) 
										 ( recipient_public_key : uint256 ) 
										 ( recipient_internal_owner : address ) 
                                         ( tokens : uint128 ) 
                                         ( grams : uint128 )   
										 ( deploy : boolean ) 
										 ( return_ownership : boolean ) 
										 ( payload : cell ) : UExpression PhantomType true . 
	refine {{ temporary_data::setglob ( global_id::answer_id , return_func_id_ () ->  get () ) ; {_} }} .
 	refine {{ transfer_to_recipient_impl_ (  #{ answer_addr } , 
                                             #{ recipient_public_key } , 
                                             #{ recipient_internal_owner } , 
                                             #{ tokens } , 
                                             #{ grams } , 
                                             #{ deploy } , 
                                             #{ return_ownership } , 
                                             TRUE , 
                                             #{ payload } ) ; {_} }} . 
 	refine {{ return_ {} }} . 
Defined . 
 
Definition requestBalance : UExpression uint128 false . 
	refine {{ tvm_rawreserve ( tvm_balance () - int_value () , rawreserve_flag::up_to ) ; {_} }} .
	refine {{ set_int_return_flag ( #{SEND_ALL_GAS} ) ; {_} }} . 
	refine {{ return_ _balance_ }} . 
Defined . 
 
Definition accept ( tokens : uint128 ) ( answer_addr : address ) ( keep_grams : uint128 ) : UExpression boolean true . 
	refine {{ new ( 'sender:address , 'value_gr:uint ) @
		          ( "sender" , "value_gr" ) := int_sender_and_value () ; {_} }} . 
	refine {{ require_ ( ( _root_address_ == !{sender} ) , error_code::message_sender_is_not_my_root ) ; {_} }} . 
	refine {{ tvm_accept () ; {_} }} . 
	refine {{ _balance_ += #{ tokens } ; {_} }} . 
	refine {{ tvm_rawreserve ( tvm_balance () + (#{ keep_grams }) - !{value_gr} , rawreserve_flag::up_to ) ; {_} }} . 
	refine {{ set_int_sender ( #{ answer_addr } ) ; {_} }} . 
	refine {{ set_int_return_value ( 0 ) ; {_} }} . 
	refine {{ set_int_return_flag ( #{SEND_ALL_GAS} \\ #{IGNORE_ACTION_ERRORS} ) ; {_} }} . 
	refine {{ return_ TRUE }} . 
Defined . 

Definition internalTransfer ( tokens : uint128 ) ( answer_addr : address ) 
						    ( sender_pubkey : uint256 ) ( sender_owner : address ) 
						    ( notify_receiver : boolean ) ( payload : cell ) : UExpression PhantomType true . 
	refine {{ new 'expected_address : uint256 @ "expected_address" :=          
                     expected_sender_address_ ( #{ sender_pubkey } , #{ sender_owner } ) ; {_} }} . 
	refine {{ new ( 'sender:address , 'value_gr:uint ) @
				( "sender" , "value_gr" ) := int_sender_and_value () ; {_} }} . 
	refine {{ require_ ( !{sender} ↑ address.address == !{ expected_address }  , error_code::message_sender_is_not_good_wallet  ) ; {_} }} . 
	refine {{ _balance_ += #{ tokens } ; {_} }} . 
	refine {{ tvm_rawreserve ( tvm_balance () - !{value_gr} , rawreserve_flag::up_to ) ; {_} }} . 
	refine {{ if ( #{ notify_receiver } && 
				( ? _owner_address_) ) then { {_:UEt} } else { {_:UEf} } }} . 
	refine {{ temporary_data::setglob ( global_id::answer_id , return_func_id_ () -> get () ) ; {_} }} .
	refine ( let _owner_address__ptr := {{ ITONTokenWalletNotifyPtr [[  * _owner_address_  ]] }} in (* need get *)
			{{ {_owner_address__ptr} with [$ 0 ⇒ { Messsage_ι_value } ;
										#{SEND_ALL_GAS} ⇒ { Messsage_ι_flags } $] 
										⤳ TONTokenWallet.onTip3Transfer ( #{ answer_addr } , _balance_ , #{tokens}, #{sender_pubkey}, #{ sender_owner } , #{ payload } ) }} ). 
	refine {{ if #{ answer_addr } != tvm_myaddr () then { {_:UEf} } ; {_} }} .
	refine {{ tvm_transfer ( (#{ answer_addr }) , 0 , FALSE , #{SEND_ALL_GAS} ) }} . 
	refine {{ return_ {} }} . 
Defined . 
 
Definition destroy ( dest : address ) : UExpression PhantomType true . 
	refine {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
	refine {{ require_ ( _balance_ == 0 ,  error_code::destroy_non_empty_wallet  ) ; {_} }} . 
	refine {{ tvm_accept () ; {_} }} . 
	refine {{ tvm_transfer ( #{ dest } , 0 , FALSE , SEND_ALL_GAS_ \\ 
							                         SENDER_WANTS_TO_PAY_FEES_SEPARATELY_ \\ 
										             DELETE_ME_IF_I_AM_EMPTY_ \\
										             IGNORE_ACTION_ERRORS_ ) }} . 
Defined . 
 
Definition getBalance : UExpression uint128 false . 
	refine {{ return_ _balance_ }} . 
Defined . 
 
Definition getBalance_right : URValue uint128 false := 
	wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getBalance ) . 
 
Notation " 'getBalance_' '(' ')' " := ( getBalance_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition burn ( out_pubkey : uint256 ) ( out_internal_owner : address ) : UExpression PhantomType true . 
	refine {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
	refine {{ tvm_accept () ; {_} }} . 
	refine {{ new 'root_ptr : address @ "root_ptr" := _root_address_ ; {_} }}.
	refine {{ new 'flags : uint @ "flags" := 
                                   SEND_ALL_GAS_ \\ 
                   SENDER_WANTS_TO_PAY_FEES_SEPARATELY_ \\ 
                              DELETE_ME_IF_I_AM_EMPTY_ \\ 
                                IGNORE_ACTION_ERRORS_ ; {_} }} . 
	refine ( let root_ptr_ptr := {{ IWrapperPtr [[ !{root_ptr}  ]] }} in 
              {{ {root_ptr_ptr} with [$ 0 ⇒ { Messsage_ι_value } ;
			  							!{ flags } ⇒ { Messsage_ι_flags } $] 
                                         ⤳ .burn ( int_sender () , _wallet_public_key_ ,
										 get_owner_addr_ ( ) , (#{ out_pubkey }) , (#{ out_internal_owner }) ,
										 getBalance_ ( ) ) ; {_} }}  ).
	refine {{ return_ {} }} .   
Defined . 

Definition lendOwnership ( answer_addr : address ) ( grams : uint128 ) 
						 ( std_dest : uint256 ) ( lend_balance : uint128 ) 
						 ( lend_finish_time : uint32 ) ( deploy_init_cl : cell ) ( payload : cell ) 
						 : UExpression PhantomType true . 
	refine {{ new 'allowed_balance : uint128 @ "allowed_balance" := check_owner_ ( TRUE , TRUE ) ; {_} }} . 
	refine {{ require_ ( (#{ lend_balance } > 0)  && 
	                      (#{ lend_balance } <= !{ allowed_balance }) , error_code::not_enough_balance ) ; {_} }} . 
	refine {{ require_ ( #{ lend_finish_time } > tvm_now () ,  error_code::finish_time_must_be_greater_than_now  ) ; {_} }} . 
	refine {{ tvm_accept () ; {_} }} . 
	refine {{ new 'answer_addr_fxd : address @ "answer_addr_fxd" := 
					fixup_answer_addr_ ( #{ answer_addr } ) ; {_} }} . 
	refine {{ new 'dest : address @ "dest" := [ _workchain_id_ , #{ std_dest } ] ; {_} }} . 
	refine {{ new 'sum_lend_balance : uint128 @ "sum_lend_balance" := #{ lend_balance } ; {_} }} . 
	refine {{ new 'sum_lend_finish_time : uint32 @ "sum_lend_finish_time" := #{ lend_finish_time } ; {_} }} . 
	refine {{ if  _lend_ownership_ -> lookup ( !{ dest } ) then { {_:UEf} } ; {_} }} .
	refine {{ new 'existing_lend : optional lend_recordLRecord @ "existing_lend" :=  
                                  _lend_ownership_ -> lookup ( !{ dest } )  ; {_} }} .
 	refine {{ { sum_lend_balance } += ( *!{existing_lend} ) ↑ lend_record.lend_balance  ; {_} }} . 
 	refine {{ { sum_lend_finish_time } := max ( #{ lend_finish_time } , ( *!{existing_lend} ) ↑ lend_record.lend_finish_time ) }} . 
 	refine {{ _lend_ownership_ -> set_at ( !{ dest } , [ (!{ sum_lend_balance }) , (!{ sum_lend_finish_time }) ] ) ; {_} }} . 
 	refine {{ new 'deploy_init : StateInitLRecord @ "deploy_init" := parse ( (#{ deploy_init_cl }) -> ctos () , 0 )  ; {_} }} . 
   	refine {{ new 'grams_ : uint128 @ "grams_" := #{grams} ; {_} }} .
 	refine {{ new 'msg_flags : uint @ "msg_flags" := prepare_transfer_message_flags_ ( { grams_ } ) ; {_} }} . 
 	refine {{ if (  !{deploy_init} ↑ StateInit.code && 
	  				 !{deploy_init} ↑ StateInit.data  ) then { {_:UEt} } else { {_:UEt} } }} . 
 	refine {{ temporary_data::setglob ( global_id::answer_id , return_func_id_ () -> get () ) ; {_} }} .
	refine ( let dest_ptr := {{ ITONTokenWalletNotifyPtr [[ !{ dest } ]] }} in
             {{ {dest_ptr} with {} ⤳ TONTokenWalletNotify.deploy ( !{deploy_init} ) ; {_} }} ). 
    refine ( {{ {dest_ptr} with [$ !{grams_} ⇒ { Messsage_ι_value } ;
								   !{ msg_flags } ⇒ { Messsage_ι_flags }; 
								   FALSE ⇒ {Messsage_ι_bounce} $] 
							⤳ .onTip3LendOwnership ( !{ answer_addr_fxd } , 
                                       #{lend_balance} , 
                                       #{lend_finish_time}, 
                                       _wallet_public_key_ ,
							           get_owner_addr_ ( ) , 
                                       #{ payload } ) }} ).  
    refine {{ temporary_data::setglob ( global_id::answer_id , return_func_id_ () -> get () ) ; {_} }} .     
	refine ( let dest_ptr := {{ ITONTokenWalletNotifyPtr [[ !{dest} ]] }} in 
			 {{ {dest_ptr} with [$ !{grams_} ⇒ { Messsage_ι_value } ;
								   !{ msg_flags } ⇒ { Messsage_ι_flags } ; 
								   FALSE ⇒ { Messsage_ι_bounce } $] 
							⤳ .onTip3LendOwnership ( !{ answer_addr_fxd } , #{lend_balance} , 
                                       #{lend_finish_time}, _wallet_public_key_ ,get_owner_addr_ ( ) ,
							            #{payload} ) }} ). 
Defined . 
 
Definition filter_lend_ownerhip_array : UExpression ( lend_ownership_array # uint128 ) false . 
	refine {{ if ( _lend_ownership_ -> empty () ) then { return_ {} } ; {_} }} . 
	refine {{ new 'now_v : uint256 @ "now_v" := tvm_now () ; {_} }} . 
	refine {{ new 'rv : lend_ownership_array @ "rv" := {} ; {_} }} . 
	refine {{ new 'lend_balance:uint128 @ "lend_balance" := {} ; {_} }} .
	refine {{ for ( 'v : _lend_ownership_) do { {_ : UEf} } ; { _ } }}. 
	refine {{ if ( ( !{now_v} ) < second ( {v} )  ↑ lend_record.lend_finish_time ) then { {_ : UEf } } }}.
	refine {{ {rv}  -> push ( [ first ({v}) , 
					(second ({v})) ↑ lend_record.lend_balance  ,
					(second ({v})) ↑ lend_record.lend_finish_time ] ) ; { _ } }}.
	refine {{ {lend_balance} += second ({v}) ↑ lend_record.lend_balance }}.
	refine {{ return_ [ !{rv} , !{lend_balance} ] }} .
Defined . 

Definition filter_lend_ownerhip_array_right  : URValue ( lend_ownership_array # uint128 ) false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) filter_lend_ownerhip_array ) . 
 
Notation " 'filter_lend_ownerhip_array_' '(' ')' " := ( filter_lend_ownerhip_array_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition returnOwnership ( tokens : uint128 ) : UExpression PhantomType true . 
	refine {{ check_owner_ ( FALSE , FALSE ) ; {_} }} . 
	refine {{ new 'sender : address @ "sender" := int_sender () ; {_} }} . 
	refine {{ new 'v : lend_recordLRecord @ "v" := _lend_ownership_ [[ (!{ sender }) ]] ; {_} }} . 
	refine {{ if ( !{ v } ↑ lend_record.lend_balance <= (#{ tokens }) ) 
			  then { {_:UEf} } else { {_:UEf} } }} . 
	refine {{ _lend_ownership_ -> erase ( !{ sender } ) }} . 
	refine {{ { v } ↑ lend_record.lend_balance -= (#{ tokens }) ; {_} }} . 
	refine {{ _lend_ownership_ -> set_at ( !{ sender } , !{ v } ) }} . 
Defined . 
 
Definition getName : UExpression String false . 
	refine {{ return_ _name_ }} . 
Defined.

Definition getSymbol : UExpression String false . 
	refine {{ return_ _symbol_ }} . 
Defined . 
 
Definition getDecimals : UExpression uint8 false . 
	refine {{ return_ _decimals_ }} . 
Defined . 

Definition getRootKey : UExpression uint256 false . 
	refine {{ return_ _root_public_key_ }} . 
Defined . 

Definition getWalletKey : UExpression uint256 false . 
	refine {{ return_ _wallet_public_key_ }} . 
Defined . 

Definition getRootAddress : UExpression address false . 
	refine {{ return_ _root_address_ }} . 
Defined . 
 
Definition getOwnerAddress : UExpression address false . 
	refine {{ return_ ( ( ? _owner_address_ ) ? * _owner_address_ : [ #{0%Z} , 0 ] )  }} . 
Defined . 

Definition getCode : UExpression cell false . 
	refine {{ return_ _code_ }} . 
Defined . 

Definition getName_right : URValue String false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getName ) . 
 
Notation " 'getName_' '(' ')' " := ( getName_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getSymbol_right : URValue String false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getSymbol ) . 
 
Notation " 'getSymbol_' '(' ')' " := ( getSymbol_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getDecimals_right  : URValue uint8 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getDecimals ) . 
 
Notation " 'getDecimals_' '(' ')' " := ( getDecimals_right ) 
 (in custom URValue at level 0 ) : ursus_scope .

Notation " 'getBalance_' '(' ')' " := ( getBalance_right ) 
 (in custom URValue at level 0 ) : ursus_scope .
 
Definition getRootKey_right  : URValue uint256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootKey ) . 
 
Notation " 'getRootKey_' '(' ')' " := ( getRootKey_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getWalletKey_right  : URValue uint256 false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getWalletKey ) . 
 
Notation " 'getWalletKey_' '(' ')' " := ( getWalletKey_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getRootAddress_right  : URValue address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getRootAddress) . 
 
Notation " 'getRootAddress_' '(' ')' " := ( getRootAddress_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getOwnerAddress_right  : URValue address false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getOwnerAddress ) . 
 
Notation " 'getOwnerAddress_' '(' ')' " := ( getOwnerAddress_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 

Definition getCode_right  : URValue cell false := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) getCode ) . 
 
Notation " 'getCode_' '(' ')' " := ( getCode_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
Definition allowance : UExpression allowance_infoLRecord true . 
	refine {{ if _allowance_ then { exit_ ( * _allowance_ ) } ; {_} }}.
    refine {{ return_ [ [ #{0%Z}, 0 ] , 0 ]  }}.	
Defined . 
 
Definition allowance_right  : URValue allowance_infoLRecord true := 
 wrapURExpression (ursus_call_with_args (LedgerableWithArgs:= λ0 ) allowance ) . 
 
Notation " 'allowance_' '(' ')' " := ( allowance_right ) 
 (in custom URValue at level 0 ) : ursus_scope . 
 
Definition getDetails : UExpression details_infoLRecord true . 
	refine {{ new ( 'filtered_lend_array : lend_ownership_array , 'lend_balance : uint128 ) 
	                    @ ( "filtered_lend_array" , "lend_balance" ) := filter_lend_ownerhip_array_ ( ) ; {_} }} . 
	refine {{ return_ [ getName_ ( ) , getSymbol_ ( ) , getDecimals_ ( ) , 
                         getBalance_ ( ) , getRootKey_ ( ) , getWalletKey_ ( ) , 
                         getRootAddress_ ( ) , getOwnerAddress_ ( ) , 
                         !{filtered_lend_array} , !{lend_balance} , getCode_ ( ) , 
                         allowance_ ( ) , _workchain_id_ ] }} . 
Defined . 

Definition approve ( spender : address ) 
				   ( remainingTokens : uint128 ) 
				   ( tokens : uint128 ) : UExpression PhantomType true . 
	refine {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
	refine {{ require_ ( ( (#{ tokens }) <= _balance_ ) , error_code::not_enough_balance ) ; {_} }} . 
	refine {{ tvm_accept () ; {_} }} . 
 	refine {{ if ( _allowance_ ) then { {_:UEf} } else { {_:UEt} } }} . 
	refine {{ if ( ( ( * _allowance_  ) ↑ allowance_info.remainingTokens ) == #{ remainingTokens } ) 
                          then { {_:UEf} } }} .
	refine {{  ( * _allowance_  ) ↑ allowance_info.remainingTokens  := #{ tokens } ; {_} }} .  
	refine {{  ( * _allowance_  ) ↑ allowance_info.spender := #{ spender } }} .	
 	refine {{ require_ ( #{ remainingTokens } == 0 ,  error_code::non_zero_remaining  ) ; {_} }} . 
 	refine {{ _allowance_ := [ #{ spender } , #{ tokens } ] -> set ()  ; {_} }} . 
 	refine {{ return_ {}  }} .
Defined . 
 
Definition transfer_from_impl ( answer_addr : address ) 
							  ( from : address ) 
							  ( too : address ) 
							  ( tokens : uint128 ) 
							  ( grams : uint128 ) 
							  ( send_notify : boolean ) 
							  ( payload : cell ) : UExpression PhantomType true . 
	refine {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
	refine {{ tvm_accept () ; {_} }} . 
	refine {{ new 'answer_addr_fxd @ "answer_addr_fxd" := 
                            fixup_answer_addr_ ( (#{ answer_addr }) ) ; {_} }} . 

	refine {{ new 'grams_ : uint128 @ "grams_" := #{grams} ; {_} }} .
	refine {{ new 'msg_flags : uint @ "msg_flags" := prepare_transfer_message_flags_ ( { grams_ } )  ; {_}  }} . 
	refine ( let dest_wallet_ptr := {{ ITONTokenWalletPtr [[ #{ from }  ]] }} in 
              {{ {dest_wallet_ptr} with [$ #{ grams } ⇒ { Messsage_ι_value } ;
			  								!{ msg_flags } ⇒ { Messsage_ι_flags } $] 
                                         ⤳ .internalTransferFrom (!{answer_addr_fxd} , #{ too } , #{ tokens } , 
										  #{ send_notify } , #{ payload } ) }} ). 
Defined . 
 
Definition transfer_from_impl_left { R a1 a2 a3 a4 a5 a6 a7 } 
								   ( answer_addr : URValue address a1 ) 
								   ( from : URValue address a2 ) 
								   ( too : URValue address a3 ) 
								   ( tokens : URValue uint128 a4 ) 
								   ( grams : URValue uint128 a5 ) 
								   ( send_notify : URValue boolean a6 ) ( payload : URValue cell a7 )  : 
								   UExpression R true  := 
 wrapULExpression (ursus_call_with_args (LedgerableWithArgs:= λ7 ) transfer_from_impl answer_addr from too tokens grams send_notify payload ) . 
 
Notation " 'transfer_from_impl_' '(' answer_addr ',' from ',' too ',' tokens ',' grams ',' send_notify ',' payload ')' " := 
 ( transfer_from_impl_left  answer_addr from too tokens grams send_notify payload ) 
 (in custom ULValue at level 0 , answer_addr custom URValue at level 0 , from custom URValue at level 0 
 , too custom URValue at level 0 , tokens custom URValue at level 0 , grams custom URValue at level 0 
 , send_notify custom URValue at level 0 , payload custom URValue at level 0 ) : ursus_scope . 

Definition transferFrom ( answer_addr : address ) ( from : address ) ( too : address ) ( tokens : uint128 ) ( grams : uint128 ) : UExpression PhantomType true . 
	refine {{ transfer_from_impl_ ( #{ answer_addr }, 
									#{ from }, 
									#{ too }, 
									#{ tokens }, 
									#{ grams }, 
									FALSE , 
									builder () -> endc () ) ; {_} }} . 
	refine {{ return_ {} }}.
Defined . 
 
Definition transferFromWithNotify ( answer_addr : address ) ( from : address ) 
							      ( too : address ) ( tokens : uint128 )
                                  ( grams : uint128 ) ( payload : cell ) : UExpression PhantomType true . 
	refine {{ transfer_from_impl_ ( #{ answer_addr } , 
                                 #{ from }, 
                                 #{ too }, 
                                 #{ tokens }, 
                                 #{ grams }, 
                                 TRUE , 
                                 #{ payload } ) ; {_} }} . 
 	refine {{ return_ {} }}.
Defined . 
 
Definition internalTransferFrom ( answer_addr : address ) ( too : address ) ( tokens : uint128 ) 
								( notify_receiver : boolean ) ( payload : cell ) : UExpression PhantomType true . 
	refine {{ require_ ( _allowance_ ,  error_code::no_allowance_set  ) ; {_} }} . 
	refine {{ require_ ( int_sender () == ( * _allowance_ ) ↑ allowance_info.spender ,  error_code::wrong_spender  ) ; {_} }} . 
	refine {{ require_ ( (#{ tokens }) <= ( * _allowance_ ) ↑ allowance_info.remainingTokens , error_code::not_enough_allowance  ) ; {_} }} . 
	refine {{ require_ ( (#{ tokens }) <= _balance_ , error_code::not_enough_balance ) ; {_} }} . 

    refine ( let dest_wallet_ptr := {{ ITONTokenWalletPtr [[ #{ too }  ]] }} in 
              {{ tvm_rawreserve ( tvm_balance () - int_value () , rawreserve_flag::up_to ) ;
			     {dest_wallet_ptr} with [$ 0 ⇒ { Messsage_ι_value } ;
			  								SEND_ALL_GAS_ ⇒ { Messsage_ι_flags } $] 
                                         ⤳ .internalTransfer_ ((#{ tokens }) , (#{ answer_addr }) , _wallet_public_key_ , 
										 get_owner_addr_ ( ) , (#{ notify_receiver }) , (#{ payload }) ) ; {_} }} ). 
	refine {{ ( * _allowance_  ) ↑ allowance_info.remainingTokens  -= #{ tokens } ; {_} }} .
	refine {{ _balance_ -= #{ tokens } ; {_} }} . 
	refine {{ return_ {} }} .
Defined . 
 
Definition disapprove : UExpression PhantomType true . 
	refine {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
	refine {{ tvm_accept () ; {_} }} . 
	refine {{ _allowance_ -> reset () ; {_} }} . 
	refine {{ return_ {} }} .
Defined . 

(*AL: TODO*) 
Definition _on_bounced ( msg : cell ) ( msg_body : slice ) : UExpression uint true . 
	refine {{ tvm_accept () ; {_} }} . 
(*  	 	 refine {{ parser p ( (#{ msg_body }) ) ; {_} }} .  *)
 	 	 refine {{ require_ ( (* ( p ^^ ldi ( 32 ) *) {} == #{(-1)%Z} ,  error_code::wrong_bounced_header) ; {_} }} . 
(*  	 	 refine {{ opt_hdr : ( auto ) @ "opt_hdr" ; {_} }} .  *)
       refine {{ new 'opt_hdr @ "opt_hdr" := {} ; {_} }} .
(* 	 	 refine {{ [ opt_hdr , =p ] := parse_continue < abiv2::internal_msg_header > ( p ) ; {_} }} . *) 
 	 	 refine {{ require_ ( (  !{opt_hdr} ) , error_code::wrong_bounced_header ) ; {_} }} . 
 	 	 refine {{  new ( 'hdr:_ , 'persist:_ ) @ ( "hdr" , "persist" ) := {}
           (* load_persistent_data < ITONTokenWallet , wallet_replay_protection_t , DTONTokenWallet > () *) ; {_} }} . 
 	 	 refine {{  if (  (* ( * {opt_hdr} )  ↑ ???.function_id *) {} == {}
            (* id_v < &ITONTokenWalletNotify::onTip3LendOwnership > *) ) then { {_:UEf} } else { {_:UEt} } ; {_} }} .
(*  	 	 refine {{  auto parsed_msg = parse < int_msg_info > ( parser ( (#{ msg }) ) , error_code::bad_incoming_msg ) ; {_} }} .  *)
(*  	 	 refine {{ persist ^^ _lend_ownership_ . erase ( incoming_msg ( parsed_msg ) . int_sender () ) ; {_} }} .  *)
 	 	 refine {{ return_ {} }} .
 	 	 refine {{ require_ ( (* ( * {opt_hdr} )  ↑ ???.function_id *) {} == {}
                          (*  id_v < &ITONTokenWallet::internalTransfer > *) , error_code::wrong_bounced_header ) ; {_} }} . 
 	 	 refine {{ new 'Args @ "Args" := {}
                     (* args_struct_t<&ITONTokenWallet::internalTransfer> *) ; {_} }} . 
(*  	 	 refine {{ static_assert ( std::is_same_v < decltype ( (!{ Args }) {} . tokens ) , uint128 > ) ; {_} }} .  *)
 	 	 refine {{ new 'answer_id @ "answer_id" := {} ; {_} }} . 
(*  	 	 refine {{ =p : ( auto ) @ "=p" ; {_} }} .  *)
(*  	 	 refine {{ [ answer_id , =p ] := parse_continue < uint32 > ( p ) ; {_} }} .  *)
 	 	 refine {{ new 'bounced_val @ "bounced_val" := {}  
 	 	                   (*  parse ( p , error_code::wrong_bounced_args )  *); {_} }} . 
 	 	 refine {{ (* (!{persist}) ↑ _balance_ += (!{ bounced_val }) *) return_ {} }} . 
(*  refine {{ save_persistent_data < ITONTokenWallet , wallet_replay_protection_t > ( hdr , persist ) ; {_} }} .  *)
 refine {{ return_ 0 }} . 
Defined . 

Definition _fallback ( msg : cell ) ( msg_body : slice ) : UExpression uint true . 
	refine {{ require_ ( (  parser ( #{ msg_body } ) -> ldu ( 32 ) == 0 ) , error_code::wrong_public_call  ) ; {_} }} . 
	refine {{ return_ 0 }} . 
Defined . 

Definition prepare_external_wallet_state_init_and_addr ( name : String ) 
													   ( symbol : String ) 
													   ( decimals : uint8 ) 
													   ( root_public_key : uint256 ) 
													   ( wallet_public_key : uint256 ) 
													   ( root_address : address ) 
													   ( owner_address : optional address ) 
													   ( code : cell ) 
													   ( workchain_id : int ) 
													   : UExpression ( StateInitLRecord # uint256 ) false . 
	refine {{ new 'wallet_data : ( DTONTokenWalletExternalLRecord ) @ "wallet_data" := 	 	 
			[ #{ name } , #{ symbol } , #{ decimals } , 0 , 
			  #{ root_public_key } , #{ wallet_public_key } , 
			  #{ root_address } , #{ owner_address } , #{ code } , {} , #{ workchain_id } ] ; {_} }} . 
	refine {{ new 'wallet_data_cl : cell @ "wallet_data_cl" := 
			prepare_persistent_data_ ( external_wallet_replay_protection_t::init () , (!{ wallet_data }) ) ; {_} }} . 
	refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 	 	 
			      [ {} , {} , (#{ code }) -> set () , (!{ wallet_data_cl }) -> set () , {} ] ; {_} }} . 
	refine {{ new 'wallet_init_cl : cell @ "wallet_init_cl" := 
							build ( σ !{ wallet_init } ) -> make_cell ()  ; {_} }} . 
	refine {{ return_ [ !{ wallet_init } , tvm_hash ( !{ wallet_init_cl } ) ] }} . 
Defined . 
 
Definition prepare_internal_wallet_state_init_and_addr ( name : String ) 
													   ( symbol : String ) 
													   ( decimals : uint8 ) 
													   ( root_public_key : uint256 ) 
													   ( wallet_public_key : uint256 ) 
													   ( root_address : address ) 
													   ( owner_address : optional address ) 
													   ( code : cell ) 
													   ( workchain_id : int ) 
													   : UExpression ( StateInitLRecord # uint256 ) false . 
	refine {{ new 'wallet_data : ( DTONTokenWalletInternalLRecord ) @ "wallet_data" := 	 	 
 	 	 	 [ #{ name } , #{ symbol } , #{ decimals } , 0 , #{ root_public_key } , #{ wallet_public_key } , 
               #{ root_address } , #{ owner_address } , {} , #{ code } , #{ workchain_id } ] ; {_} }} . 
	refine {{ new 'wallet_data_cl : cell @ "wallet_data_cl" := prepare_persistent_data_ ( {} , (!{ wallet_data }) ) ; {_} }} . 
	refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := [ {} , {} , (#{ code }) -> set () , 
                   														   !{ wallet_data_cl } -> set () , {} ] ; {_} }} . 
	refine {{ new 'wallet_init_cl : cell @ "wallet_init_cl" := build ( σ !{ wallet_init } ) -> make_cell () ; {_} }} . 
	refine {{ return_ [ !{ wallet_init } , tvm_hash ( !{ wallet_init_cl } ) ] }} . 
Defined . 
 
End FuncsInternal.
End Funcs.








