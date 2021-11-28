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

Require Import Project.CommonTypes.
Require Import Project.CommonConstSig.

(*Fully qualified name are mandatory in multi-contract environment*)
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
(* Export SpecModuleForFuncNotations(* ForFuncs *).tvmNotationsModule.
 *)
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

Definition filter_lend_ownerhip_map : UExpression ( (mapping addr_std_fixedLRecord lend_recordLRecord) # uint128 ) false . 
	refine {{ if ( _lend_ownership_ -> empty () ) then { return_ {} } ; {_} }} .
	refine {{ new 'now_v : uint256 @ "now_v" := tvm_now () ; {_} }} . 
	refine {{ new 'rv : mapping addr_std_fixedLRecord lend_recordLRecord @ "rv" := {} ; {_} }} . 
	refine {{ new 'lend_balance : uint128 @ "lend_balance" := {} ; {_} }} . 
    refine {{ for ( 'v : _lend_ownership_) do { {_ : UEf} } ; { _ } }}.
	refine {{ if ( ( !{now_v} ) < second ( {v} )  ↑ lend_record.lend_finish_time ) then { {_ : UEf } } }}.
	refine {{ {rv}  -> insert ( {v} ) ; { _ } }}.
	refine {{ {lend_balance} += second ({v}) ↑ lend_record.lend_balance }}.
    refine {{ _lend_ownership_ := ( !{rv} ) ; {_} }} .
    refine {{ return_ [ !{rv} , !{lend_balance} ] }} .
Defined .
 
Definition filter_lend_ownerhip_map_right : URValue ( (XHMap addr_std_fixedLRecord lend_recordLRecord) # uint128 ) false := 
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

Definition check_internal_owner ( original_owner_only : boolean ) ( allowed_for_original_owner_in_lend_state : boolean ) : 
								UExpression uint128 true . 
 	 	 refine {{ new ( 'filtered_map: mapping addr_std_fixedLRecord lend_recordLRecord, 
                         'actual_lend_balance: uint128 ) @ ( "filtered_map" , "actual_lend_balance" ) := 
                   filter_lend_ownerhip_map_ ( ) ; {_} }} . 
 	 	 refine {{ if ( !{actual_lend_balance} > 0 ) then { {_:UEt} } else { {_:UEt} } ; {_} }} . 
 	 	 	 refine {{ if ( (#{ allowed_for_original_owner_in_lend_state }) ) then { {_:UEt} } ; {_} }} .
        refine {{ require_ ( (is_internal_owner_ ( )) , 1 (* error_code::internal_owner_disabled *) ) ; {_} }} . 
 	 	 	  refine {{ if ( _owner_address_ -> get () == int_sender () ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 	 refine {{ return_ _balance_ - #{actual_lend_balance} }} . 
 	 	 refine {{ require_ ( ( ~ (#{ original_owner_only }) ) , error_code::only_original_owner_allowed ) ; {_} }} . 
 	 	 refine {{ new 'elem : ( auto ) @ "elem" := {} ; {_} }} . 
 	 	 refine {{ { elem } := filtered_map ^^ auto:lookup ( int_sender () ) ; {_} }} . 
 	 	 refine {{ require_ ( ( ~ ~ (!{ elem }) ) , error_code::message_sender_is_not_my_owner ) ; {_} }} . 
 	 	 refine {{ return_ std::min ( _balance_ , (!{ elem }) - > lend_balance ) }} . 
 refine {{ { require ( is_internal_owner_ () , error_code::internal_owner_disabled ) ; {_} }} . 
 refine {{ require_ ( ( *owner_address_ == int_sender () ) , error_code::message_sender_is_not_my_owner ) ; {_} }} . 
 refine {{ return_ _balance_ }} . 

Defined . 
 
Definition check_external_owner : UExpression uint128 true . 
 refine {{ require_ ( ( ~ is_internal_owner_ () ) , error_code::internal_owner_enabled ) ; {_} }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _wallet_public_key_ ) , error_code::message_sender_is_not_my_owner ) ; {_} }} . 
 	 	 refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ filtered_map : ( auto ) @ "filtered_map" ; {_} }} . 
 	 	 refine {{ lend_balance : ( auto ) @ "lend_balance" ; {_} }} . 
 	 	 refine {{ [ filtered_map , lend_balance ] := filter_lend_ownerhip_map_ () ; {_} }} . 
 	 	 refine {{ require_ ( ( filtered_map ^^ auto:empty () ) , error_code::wallet_in_lend_owneship ) ; {_} }} . 
 	 	 refine {{ return_ _balance_ }} . 
Defined . 
 



Definition check_owner ( original_owner_only : ( XBool ) ) ( allowed_in_lend_state : ( XBool ) ) : UExpression uint128 FALSE . 
 	 	refine {{ if ( (#{Internal}) ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 refine {{ return_ check_internal_owner_ ( (#{ original_owner_only }) , (#{ allowed_in_lend_state }) ) }} . 
 	 	 refine {{ return_ check_external_owner_ () ; {_} }} . 
 
 
Defined . 


 Definition check_transfer_requires ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) : UExpression uint128 true . 
 	 	 refine {{ new 'active_balance : ( auto ) @ "active_balance" := {} ; {_} }} . 
 	 	 refine {{ { active_balance } := check_owner_ ( FALSE , FALSE ) ; {_} }} . 
 	 	 refine {{ require_ ( ( (#{ tokens }) <= (!{ active_balance }) ) , error_code::not_enough_balance ) ; {_} }} . 
 	 	 refine {{ if ( (#{Internal}) ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 refine {{ require_ ( ( int_value () . get () >= min_transfer_costs ) , error_code::not_enough_tons_to_process ) }} . 
 	 	 refine {{ require_ ( ( (#{ grams }) ^^ uint128:get () >= min_transfer_costs && tvm_balance () > (#{ grams }) ^^ uint128:get () ) , error_code::not_enough_tons_to_process ) ; {_} }} . 
 	 	 refine {{ return_ (!{ active_balance }) ; {_} }} . 
 
 
Defined . 


Definition transfer_impl ( answer_addr : ( XAddress ) ) ( too : ( XAddress ) ) ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) ( return_ownership : ( XBool ) ) ( send_notify : ( XBool ) ) ( payload : ( XCell ) ) : UExpression PhantomType true . 
 	 	 refine {{ new 'active_balance : ( auto ) @ "active_balance" := {} ; {_} }} . 
 	 	 refine {{ { active_balance } := check_transfer_requires_ ( (#{ tokens }) , (#{ grams }) ) ; {_} }} . 
 	 	 refine {{ require_ ( ( std::get < addr_std > ( (#{ too }) () ) . address != 0 ) , error_code::transfer_to_zero_address ) ; {_} }} . 
 	 	 refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ new 'answer_addr_fxd : ( auto ) @ "answer_addr_fxd" := {} ; {_} }} . 
 	 	 refine {{ { answer_addr_fxd } := fixup_answer_addr_ ( (#{ answer_addr }) ) ; {_} }} . 
 	 	 refine {{ new 'msg_flags : ( uint ) @ "msg_flags" := {} ; {_} }} . 
 	 	 refine {{ { msg_flags } := prepare_transfer_message_flags_ ( (#{ grams }) ) ; {_} }} . 
 	 	 refine {{ ITONTokenWalletPtr dest_wallet ( (#{ too }) ) ; {_} }} . 
 	 	 refine {{ dest_wallet ( Grams ( (#{ grams }) . get () ) , (!{ msg_flags }) ) . internalTransfer_ ( (#{ tokens }) , (!{ answer_addr_fxd }) , _wallet_public_key_ , get_owner_addr_ () , bool_t (#{ send_notify }) , (#{ payload }) ) ; {_} }} . 
 	 	 refine {{ update_spent_balance_ ( (#{ tokens }) , (#{ return_ownership }) ) }} . 
Defined . 

Definition transfer ( answer_addr : ( XAddress ) ) ( too : ( XAddress ) ) ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) ( return_ownership : ( XBool ) ) : UExpression PhantomType false . 
 refine {{ transfer_impl_ ( (#{ answer_addr }) , (#{ too }) , (#{ tokens }) , (#{ grams }) , (#{ return_ownership }) . get () , FALSE , builder () . endc () ) }} . 
Defined . 
 
Definition transferWithNotify ( answer_addr : ( XAddress ) ) ( too : ( XAddress ) ) ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) ( return_ownership : ( XBool ) ) ( payload : ( XCell ) ) : UExpression PhantomType false . 
 {{ temporary_data::setglob ( global_id::answer_id , return_func_id () - > get () ) ; {_} }} . 
 	 	 refine {{ transfer_impl_ ( (#{ answer_addr }) , (#{ too }) , (#{ tokens }) , (#{ grams }) , (#{ return_ownership }) . get () , TRUE , (#{ payload }) ) }} . 
Defined . 
 
Definition transferToRecipient ( answer_addr : ( XAddress ) ) ( recipient_public_key : ( uint256 ) ) ( recipient_internal_owner : ( XAddress ) ) ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) ( deploy : ( XBool ) ) ( return_ownership : ( XBool ) ) : UExpression PhantomType false . 
 {{ transfer_to_recipient_impl_ ( (#{ answer_addr }) , (#{ recipient_public_key }) , (#{ recipient_internal_owner }) , (#{ tokens }) , (#{ grams }) , (#{ deploy }) . get () , (#{ return_ownership }) . get () , FALSE , builder () . endc () ) }} . 
Defined . 

Definition transferToRecipientWithNotify ( answer_addr : ( XAddress ) ) ( recipient_public_key : ( uint256 ) ) ( recipient_internal_owner : ( XAddress ) ) ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) ( deploy : ( XBool ) ) ( return_ownership : ( XBool ) ) ( payload : ( XCell ) ) : UExpression PhantomType false . 
 {{ temporary_data::setglob ( global_id::answer_id , return_func_id () - > get () ) ; {_} }} . 
 	 	 refine {{ transfer_to_recipient_impl_ ( (#{ answer_addr }) , (#{ recipient_public_key }) , (#{ recipient_internal_owner }) , (#{ tokens }) , (#{ grams }) , (#{ deploy }) . get () , (#{ return_ownership }) . get () , TRUE , (#{ payload }) ) }} . 
Defined . 

Definition requestBalance : UExpression uint128 false . 
 {{ tvm_rawreserve ( tvm_balance () - int_value () . get () , rawreserve_flag::up_to ) ; {_} }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; {_} }} . 
 	 	 refine {{ return_ _balance_ }} . 
Defined . 
 
Definition accept ( tokens : ( uint128 ) ) ( answer_addr : ( XAddress ) ) ( keep_grams : ( uint128 ) ) : UExpression XBool true . 
 {{ sender : ( auto ) @ "sender" ; {_} }} . 
 	 	 refine {{ value_gr : ( auto ) @ "value_gr" ; {_} }} . 
 	 	 refine {{ [ sender , value_gr ] := int_sender_and_value () ; {_} }} . 
 	 	 refine {{ require_ ( ( _root_address_ == sender ) , error_code::message_sender_is_not_my_root ) ; {_} }} . 
 	 	 refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ _balance_ += (#{ tokens }) ; {_} }} . 
 	 	 refine {{ tvm_rawreserve ( tvm_balance () + (#{ keep_grams }) . get () - value_gr () , rawreserve_flag::up_to ) ; {_} }} . 
 	 	 refine {{ set_int_sender ( (#{ answer_addr }) ) ; {_} }} . 
 	 	 refine {{ set_int_return_value ( 0 ) ; {_} }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS | IGNORE_ACTION_ERRORS ) ; {_} }} . 
 	 	 refine {{ return bool_t TRUE }} . 
Defined . 
 
Definition internalTransfer ( tokens : ( uint128 ) ) ( answer_addr : ( XAddress ) ) ( sender_pubkey : ( uint256 ) ) ( sender_owner : ( XAddress ) ) ( notify_receiver : ( XBool ) ) ( payload : ( XCell ) ) : UExpression PhantomType true . 
 {{ new 'expected_address : ( uint256 ) @ "expected_address" := {} ; {_} }} . 
 	 	 refine {{ { expected_address } := expected_sender_address_ ( (#{ sender_pubkey }) , (#{ sender_owner }) ) ; {_} }} . 
 	 	 refine {{ sender : ( auto ) @ "sender" ; {_} }} . 
 	 	 refine {{ value_gr : ( auto ) @ "value_gr" ; {_} }} . 
 	 	 refine {{ [ sender , value_gr ] := int_sender_and_value () ; {_} }} . 
 	 	 refine {{ require_ ( ( std::get < addr_std > ( sender () ) . address == (!{ expected_address }) ) , error_code::message_sender_is_not_good_wallet ) ; {_} }} . 
 	 	 refine {{ _balance_ += (#{ tokens }) ; {_} }} . 
 	 	 refine {{ tvm_rawreserve ( tvm_balance () - value_gr () , rawreserve_flag::up_to ) ; {_} }} . 
 	 	 refine {{ if ( (#{ notify_receiver }) && _owner_address_ ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 refine {{ { temporary_data::setglob ( global_id::answer_id , return_func_id () - > get () ) ; {_} }} . 
 	 	 	 refine {{ ITONTokenWalletNotifyPtr ( *owner_address_ ) ( Grams ( 0 ) , SEND_ALL_GAS ) . onTip3Transfer ( (#{ answer_addr }) , _balance_ , (#{ tokens }) , (#{ sender_pubkey }) , (#{ sender_owner }) , (#{ payload }) ) }} . 
 	 refine {{ { if ( (#{ answer_addr }) ~ = address { tvm_address () } ) tvm_transfer ( (#{ answer_addr }) , 0 , FALSE , SEND_ALL_GAS ) }} . 
 
 
Defined . 
 
Definition destroy ( dest : ( XAddress ) ) : UExpression PhantomType true . 
 {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
 	 	 refine {{ require_ ( ( _balance_ == 0 ) , error_code::destroy_non_empty_wallet ) ; {_} }} . 
 	 	 refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ tvm_transfer ( (#{ dest }) , 0 , FALSE , SEND_ALL_GAS | SENDER_WANTS_TO_PAY_FEES_SEPARATELY | DELETE_ME_IF_I_AM_EMPTY | IGNORE_ACTION_ERRORS ) }} . 
Defined . 
 
Definition burn ( out_pubkey : ( uint256 ) ) ( out_internal_owner : ( XAddress ) ) : UExpression PhantomType false . 
 {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
 	 	 refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ IWrapperPtr root_ptr ( _root_address_ ) ; {_} }} . 
 	 	 refine {{ new 'flags : ( uint ) @ "flags" := {} ; {_} }} . 
 	 	 refine {{ { flags } := SEND_ALL_GAS | SENDER_WANTS_TO_PAY_FEES_SEPARATELY | DELETE_ME_IF_I_AM_EMPTY | IGNORE_ACTION_ERRORS ; {_} }} . 
 	 	 refine {{ root_ptr ( Grams ( 0 ) , (!{ flags }) ) . burn_ ( int_sender () , _wallet_public_key_ , get_owner_addr_ () , (#{ out_pubkey }) , (#{ out_internal_owner }) , getBalance_ () ) }} . 
Defined . 

Definition lendOwnership ( answer_addr : ( XAddress ) ) ( grams : ( uint128 ) ) ( std_dest : ( uint256 ) ) ( lend_balance : ( uint128 ) ) ( lend_finish_time : ( uint32 ) ) ( deploy_init_cl : ( XCell ) ) ( payload : ( XCell ) ) : UExpression PhantomType true . 
 {{ new 'allowed_balance : ( auto ) @ "allowed_balance" := {} ; {_} }} . 
 	 	 refine {{ { allowed_balance } := check_owner_ ( TRUE , TRUE ) ; {_} }} . 
 	 	 refine {{ require_ ( ( (#{ lend_balance }) > 0 && (#{ lend_balance }) <= (!{ allowed_balance }) ) , error_code::not_enough_balance ) ; {_} }} . 
 	 	 refine {{ require_ ( ( (#{ lend_finish_time }) > tvm_now () ) , error_code::finish_time_must_be_greater_than_now ) ; {_} }} . 
 	 	 refine {{ #ifdef TIP3_ENABLE_ALLOWANCE require ( ~ _allowance_ , error_code::allowance_is_set ) ; {_} }} . 
 	 	 refine {{ #endif tvm_accept () ; {_} }} . 
 	 	 refine {{ new 'answer_addr_fxd : ( auto ) @ "answer_addr_fxd" := {} ; {_} }} . 
 	 	 refine {{ { answer_addr_fxd } := fixup_answer_addr_ ( (#{ answer_addr }) ) ; {_} }} . 
 	 	 refine {{ new 'dest : ( auto ) @ "dest" := {} ; {_} }} . 
 	 	 refine {{ { dest } := Address :: make_std ( _workchain_id_ , (#{ std_dest }) ) ; {_} }} . 
 	 	 refine {{ new 'sum_lend_balance : ( auto ) @ "sum_lend_balance" := {} ; {_} }} . 
 	 	 refine {{ { sum_lend_balance } := (#{ lend_balance }) ; {_} }} . 
 	 	 refine {{ new 'sum_lend_finish_time : ( auto ) @ "sum_lend_finish_time" := {} ; {_} }} . 
 	 	 refine {{ { sum_lend_finish_time } := (#{ lend_finish_time }) ; {_} }} . 
 	 	 refine {{ if ( auto existing_lend = _lend_ownership_ ^^ lookup ( (!{ dest }) ) ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 refine {{ { (!{ sum_lend_balance }) + = existing_lend - > (#{ lend_balance }) ; {_} }} . 
 	 	 	 refine {{ { sum_lend_finish_time } := std::max ( (#{ lend_finish_time }) , existing_lend - > (#{ lend_finish_time }) ) }} . 
 	 refine {{ _lend_ownership_ ^^ set_at ( (!{ dest }) , { (!{ sum_lend_balance }) , (!{ sum_lend_finish_time }) } ) ; {_} }} . 
 	 refine {{ new 'deploy_init : ( auto ) @ "deploy_init" := {} ; {_} }} . 
 	 refine {{ { deploy_init } := parse ( (#{ deploy_init_cl }) . ctos () ) ; {_} }} . 
 	 refine {{ new 'msg_flags : ( uint ) @ "msg_flags" := {} ; {_} }} . 
 	 refine {{ { msg_flags } := prepare_transfer_message_flags_ ( (#{ grams }) ) ; {_} }} . 
 	 refine {{ if ( (!{ deploy_init }) ^^ auto:code && (!{ deploy_init }) ^^ auto:data ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 refine {{ { temporary_data::setglob ( global_id::answer_id , return_func_id () - > get () ) ; {_} }} . 
 	 	 refine {{ ITONTokenWalletNotifyPtr ( (!{ dest }) ) . deploy ( (!{ deploy_init }) , Grams ( (#{ grams }) . get () ) , (!{ msg_flags }) , FALSE ) . onTip3LendOwnership ( (!{ answer_addr_fxd }) , (#{ lend_balance }) , (#{ lend_finish_time }) , _wallet_public_key_ , get_owner_addr_ () , (#{ payload }) ) }} . 
 refine {{ { temporary_data::setglob ( global_id::answer_id , return_func_id () - > get () ) ; {_} }} . 
 refine {{ ITONTokenWalletNotifyPtr ( (!{ dest }) ) ( Grams ( (#{ grams }) . get () ) , (!{ msg_flags }) , FALSE ) . onTip3LendOwnership ( (!{ answer_addr_fxd }) , (#{ lend_balance }) , (#{ lend_finish_time }) , _wallet_public_key_ , get_owner_addr_ () , (#{ payload }) ) }} . 

Defined . 
 
Definition returnOwnership ( tokens : ( uint128 ) ) : UExpression PhantomType false . 
 {{ check_owner_ ( FALSE , FALSE ) ; {_} }} . 
 	 	 refine {{ new 'sender : ( auto ) @ "sender" := {} ; {_} }} . 
 	 	 refine {{ { sender } := int_sender () ; {_} }} . 
 	 	 refine {{ new 'v : ( auto ) @ "v" := {} ; {_} }} . 
 	 	 refine {{ { v } := _lend_ownership_ [ (!{ sender }) ] ; {_} }} . 
 	 	 refine {{ if ( (!{ v }) ^^ auto:lend_balance <= (#{ tokens }) ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 refine {{ { _lend_ownership_ . erase ( (!{ sender }) ) }} . 
 	 refine {{ { (!{ v }) . lend_balance - = (#{ tokens }) ; {_} }} . 
 	 refine {{ _lend_ownership_ ^^ set_at ( (!{ sender }) , (!{ v }) ) }} . 
 
 
Defined . 
 
Definition getDetails : UExpression details_infoLRecord false . 
 {{ filtered_lend_array : ( auto ) @ "filtered_lend_array" ; {_} }} . 
 	 	 refine {{ lend_balance : ( auto ) @ "lend_balance" ; {_} }} . 
 	 	 refine {{ [ filtered_lend_array , lend_balance ] := filter_lend_ownerhip_array_ () ; {_} }} . 
 	 	 refine {{ return_ [ getName_ () , getSymbol_ () , getDecimals_ () , getBalance_ () , getRootKey_ () , getWalletKey_ () , getRootAddress_ () , getOwnerAddress_ () , filtered_lend_array , lend_balance , getCode_ () , allowance_ () , _workchain_id_ ] }} . 
Defined . 
 
Definition getName : UExpression XString false . 
 {{ return_ _name_ }} . 
Defined . 

Definition getSymbol : UExpression XString false . 
 {{ return_ _symbol_ }} . 
Defined . 
 
Definition getDecimals : UExpression uint8 false . 
 {{ return_ _decimals_ }} . 
Defined . 

Definition getBalance : UExpression uint128 false . 
 {{ return_ _balance_ }} . 
Defined . 
 
Definition getRootKey : UExpression uint256 false . 
 {{ return_ _root_public_key_ }} . 
Defined . 
 
Definition getWalletKey : UExpression uint256 false . 
 {{ return_ _wallet_public_key_ }} . 
Defined . 
 
Definition getRootAddress : UExpression XAddress false . 
 {{ return_ _root_address_ }} . 
Defined . 
 
Definition getOwnerAddress : UExpression XAddress false . 
 {{ return_ _owner_address_ ? *owner_address_ : Address :: make_std ( 0 , 0 ) }} . 
Defined . 
 
Definition getCode : UExpression XCell false . 
 {{ return_ _code_ }} . 
Defined . 
 
Definition allowance : UExpression allowance_infoLRecord false . 
 {{ #ifdef TIP3_ENABLE_ALLOWANCE if ( _allowance_ ) return *allowance_ ; {_} }} . 
 	 	 refine {{ #endif return allowance_info { address::make_std ( int8 ( 0 ) , uint256 ( 0 ) ) , uint128 ( 0 ) } }} . 
Defined . 
 
Definition approve ( spender : ( XAddress ) ) ( remainingTokens : ( uint128 ) ) ( tokens : ( uint128 ) ) : UExpression PhantomType true . 
 {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
 	 	 refine {{ require_ ( ( (#{ tokens }) <= _balance_ ) , error_code::not_enough_balance ) ; {_} }} . 
 	 	 refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ if ( _allowance_ ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 refine {{ { if ( _allowance_ - > (#{ remainingTokens }) == (#{ remainingTokens }) ) { _allowance_ - > (#{ remainingTokens }) = (#{ tokens }) ; {_} }} . 
 	 	 	 refine {{ _allowance_ - > (#{ spender }) = (#{ spender }) }} . 
 refine {{ { require ( (#{ remainingTokens }) == 0 , error_code::non_zero_remaining ) ; {_} }} . 
 refine {{ _allowance_ := { (#{ spender }) , (#{ tokens }) } }} . 
 
 
Defined . 
 
Definition transferFrom ( answer_addr : ( XAddress ) ) ( from : ( XAddress ) ) ( too : ( XAddress ) ) ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) : UExpression PhantomType false . 
 {{ transfer_from_impl_ ( (#{ answer_addr }) , (#{ from }) , (#{ too }) , (#{ tokens }) , (#{ grams }) , FALSE , builder () . endc () ) }} . 
Defined . 
 
 
 
 
 Definition transferFromWithNotify ( answer_addr : ( XAddress ) ) ( from : ( XAddress ) ) ( too : ( XAddress ) ) ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) ( payload : ( XCell ) ) : UExpression PhantomType false . 
 {{ transfer_from_impl_ ( (#{ answer_addr }) , (#{ from }) , (#{ too }) , (#{ tokens }) , (#{ grams }) , TRUE , (#{ payload }) ) }} . 
 Defined . 
 
 
 
 
 Definition internalTransferFrom ( answer_addr : ( XAddress ) ) ( too : ( XAddress ) ) ( tokens : ( uint128 ) ) ( notify_receiver : ( XBool ) ) ( payload : ( XCell ) ) : UExpression PhantomType true . 
 {{ require_ ( ( ~ ~ _allowance_ ) , error_code::no_allowance_set ) ; {_} }} . 
 	 	 refine {{ require_ ( ( int_sender () == _allowance_ - > spender ) , error_code::wrong_spender ) ; {_} }} . 
 	 	 refine {{ require_ ( ( (#{ tokens }) <= _allowance_ - > remainingTokens ) , error_code::not_enough_allowance ) ; {_} }} . 
 	 	 refine {{ require_ ( ( (#{ tokens }) <= _balance_ ) , error_code::not_enough_balance ) ; {_} }} . 
 	 	 refine {{ ITONTokenWalletPtr dest_wallet ( (#{ too }) ) ; {_} }} . 
 	 	 refine {{ tvm_rawreserve ( tvm_balance () - int_value () . get () , rawreserve_flag::up_to ) ; {_} }} . 
 	 	 refine {{ dest_wallet ( Grams ( 0 ) , SEND_ALL_GAS ) . internalTransfer_ ( (#{ tokens }) , (#{ answer_addr }) , _wallet_public_key_ , get_owner_addr_ () , (#{ notify_receiver }) , (#{ payload }) ) ; {_} }} . 
 	 	 refine {{ _allowance_ - > remainingTokens - = (#{ tokens }) ; {_} }} . 
 	 	 refine {{ _balance_ -= (#{ tokens }) }} . 
 Defined . 
 
 
 
 
 Definition disapprove : UExpression PhantomType false . 
 {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
 	 	 refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ _allowance_ ^^ reset () }} . 
 Defined . 
 
 
 
 
 Definition _on_bounced ( msg : ( XCell ) ) ( msg_body : ( XSlice ) ) : UExpression uint true . 
 {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ parser p ( (#{ msg_body }) ) ; {_} }} . 
 	 	 refine {{ require_ ( ( p ^^ ldi ( 32 ) == - 1 ) , error_code::wrong_bounced_header ) ; {_} }} . 
 	 	 refine {{ opt_hdr : ( auto ) @ "opt_hdr" ; {_} }} . 
 	 	 refine {{ =p : ( auto ) @ "=p" ; {_} }} . 
 	 	 refine {{ [ opt_hdr , =p ] := parse_continue < abiv2::internal_msg_header > ( p ) ; {_} }} . 
 	 	 refine {{ require_ ( ( ~ ~ opt_hdr ) , error_code::wrong_bounced_header ) ; {_} }} . 
 	 	 refine {{ #ifdef TIP3_ENABLE_ALLOWANCE if ( opt_hdr - > function_id == id_v < &ITONTokenWallet::internalTransferFrom > ) return 0 ; {_} }} . 
 	 	 refine {{ #endif auto [ hdr , persist ] = load_persistent_data < ITONTokenWallet , wallet_replay_protection_t , DTONTokenWallet > () ; {_} }} . 
 	 	 refine {{ #ifdef TIP3_ENABLE_LEND_OWNERSHIP if ( opt_hdr - > function_id == id_v < &ITONTokenWalletNotify::onTip3LendOwnership > ) { auto parsed_msg = parse < int_msg_info > ( parser ( (#{ msg }) ) , error_code::bad_incoming_msg ) ; {_} }} . 
 	 	 refine {{ persist ^^ _lend_ownership_ . erase ( incoming_msg ( parsed_msg ) . int_sender () ) ; {_} }} . 
 	 	 refine {{ #else if ( FALSE ) #endif else { require ( opt_hdr - > function_id == id_v < &ITONTokenWallet::internalTransfer > , error_code::wrong_bounced_header ) ; {_} }} . 
 	 	 refine {{ new 'Args : ( usingLRecord ) @ "Args" := {} ; {_} }} . 
 	 	 refine {{ { Args } := args_struct_t ; {_} }} . 
 	 	 refine {{ static_assert ( std::is_same_v < decltype ( (!{ Args }) {} . tokens ) , uint128 > ) ; {_} }} . 
 	 	 refine {{ answer_id : ( auto ) @ "answer_id" ; {_} }} . 
 	 	 refine {{ =p : ( auto ) @ "=p" ; {_} }} . 
 	 	 refine {{ [ answer_id , =p ] := parse_continue < uint32 > ( p ) ; {_} }} . 
 	 	 refine {{ new 'bounced_val : ( auto ) @ "bounced_val" := {} ; {_} }} . 
 	 	 refine {{ { bounced_val } := parse ( p , error_code::wrong_bounced_args ) ; {_} }} . 
 	 	 refine {{ persist ^^ _balance_ + = (!{ bounced_val }) }} . 
 refine {{ save_persistent_data < ITONTokenWallet , wallet_replay_protection_t > ( hdr , persist ) ; {_} }} . 
 refine {{ return_ 0 }} . 
 Defined . 
 
 
 
 
 Definition _fallback ( cell : ( (LRecord ) ) ( msg_body : ( XSlice ) ) : UExpression uint true . 
 {{ require_ ( ( parser ( (#{ msg_body }) ) . ldu ( 32 ) == 0 ) , error_code::wrong_public_call ) ; {_} }} . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 
 
 
 Definition transfer_to_recipient_impl ( answer_addr : ( XAddress ) ) ( recipient_public_key : ( uint256 ) ) ( recipient_internal_owner : ( XAddress ) ) ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) ( deploy : ( XBool ) ) ( return_ownership : ( XBool ) ) ( send_notify : ( XBool ) ) ( payload : ( XCell ) ) : UExpression PhantomType false . 
 {{ new 'active_balance : ( auto ) @ "active_balance" := {} ; {_} }} . 
 	 	 refine {{ { active_balance } := check_transfer_requires_ ( (#{ tokens }) , (#{ grams }) ) ; {_} }} . 
 	 	 refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ new 'answer_addr_fxd : ( auto ) @ "answer_addr_fxd" := {} ; {_} }} . 
 	 	 refine {{ { answer_addr_fxd } := fixup_answer_addr_ ( (#{ answer_addr }) ) ; {_} }} . 
 	 	 refine {{ new 'msg_flags : ( uint ) @ "msg_flags" := {} ; {_} }} . 
 	 	 refine {{ { msg_flags } := prepare_transfer_message_flags_ ( (#{ grams }) ) ; {_} }} . 
 	 	 refine {{ wallet_init : ( auto ) @ "wallet_init" ; {_} }} . 
 	 	 refine {{ (!{ dest }) : ( auto ) @ "dest" ; {_} }} . 
 	 	 refine {{ [ wallet_init , { dest } ] := calc_wallet_init_ ( (#{ recipient_public_key }) , (#{ recipient_internal_owner }) ) ; {_} }} . 
 	 	 refine {{ ITONTokenWalletPtr dest_wallet ( (!{ dest }) ) ; {_} }} . 
 	 	 refine {{ if ( (#{ deploy }) ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 refine {{ { dest_wallet . (#{ deploy }) ( wallet_init , Grams ( (#{ grams }) . get () ) , (!{ msg_flags }) ) . internalTransfer_ ( (#{ tokens }) , (!{ answer_addr_fxd }) , _wallet_public_key_ , get_owner_addr_ () , bool_t (#{ send_notify }) , (#{ payload }) ) }} . 
 	 refine {{ { dest_wallet ( Grams ( (#{ grams }) . get () ) , (!{ msg_flags }) ) . internalTransfer_ ( (#{ tokens }) , (!{ answer_addr_fxd }) , _wallet_public_key_ , get_owner_addr_ () , bool_t (#{ send_notify }) , (#{ payload }) ) }} . 
 refine {{ update_spent_balance_ ( (#{ tokens }) , (#{ return_ownership }) ) ; {_} }} . 
 
 
 Defined . 
 
 
 
 
 Definition transfer_from_impl ( answer_addr : ( XAddress ) ) ( from : ( XAddress ) ) ( too : ( XAddress ) ) ( tokens : ( uint128 ) ) ( grams : ( uint128 ) ) ( send_notify : ( XBool ) ) ( payload : ( XCell ) ) : UExpression PhantomType false . 
 {{ check_owner_ ( TRUE , FALSE ) ; {_} }} . 
 	 	 refine {{ tvm_accept () ; {_} }} . 
 	 	 refine {{ new 'answer_addr_fxd : ( auto ) @ "answer_addr_fxd" := {} ; {_} }} . 
 	 	 refine {{ { answer_addr_fxd } := fixup_answer_addr_ ( (#{ answer_addr }) ) ; {_} }} . 
 	 	 refine {{ new 'msg_flags : ( uint ) @ "msg_flags" := {} ; {_} }} . 
 	 	 refine {{ { msg_flags } := prepare_transfer_message_flags_ ( (#{ grams }) ) ; {_} }} . 
 	 	 refine {{ ITONTokenWalletPtr dest_wallet ( (#{ from }) ) ; {_} }} . 
 	 	 refine {{ dest_wallet ( Grams ( (#{ grams }) . get () ) , (!{ msg_flags }) ) . internalTransferFrom_ ( (!{ answer_addr_fxd }) , (#{ too }) , (#{ tokens }) , bool_t (#{ send_notify }) , (#{ payload }) ) }} . 
 Defined . 
 
 
 
 
 Definition get_owner_addr : UExpression XAddress false . 
 {{ return_ _owner_address_ ? *owner_address_ : Address :: make_std ( 0 , 0 ) }} . 
 Defined . 
 
 
 
 
 Definition fixup_answer_addr ( answer_addr : ( XAddress ) ) : UExpression XAddress false . 
 {{ if ( std::get < addr_std > ( (#{ answer_addr }) () ) . address == 0 ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 refine {{ { if constexpr ( (#{Internal}) ) return address { int_sender () } }} . 
 	 	 refine {{ return address { tvm_address () } }} . 
 refine {{ return_ (#{ answer_addr }) ; {_} }} . 
 
 
 Defined . 
 
 
 
 
 Definition prepare_transfer_message_flags ( &grams : ( uint128 ) ) : UExpression uint false . 
 {{ new 'msg_flags : ( uint ) @ "msg_flags" := {} ; {_} }} . 
 	 	 refine {{ { msg_flags } := IGNORE_ACTION_ERRORS ; {_} }} . 
 	 	 refine {{ if ( (#{Internal}) ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 refine {{ { tvm_rawreserve ( tvm_balance () - int_value () . get () , rawreserve_flag::up_to ) ; {_} }} . 
 	 	 	 refine {{ { msg_flags } := SEND_ALL_GAS ; {_} }} . 
 	 	 	 refine {{ grams := 0 }} . 
 	 refine {{ return_ (!{ msg_flags }) ; {_} }} . 
 
 Defined . 
 
 
 
 
 Definition update_spent_balance ( tokens : ( uint128 ) ) ( return_ownership : ( XBool ) ) : UExpression PhantomType false . 
 {{ _balance_ -= (#{ tokens }) ; {_} }} . 
 	 	 refine {{ #ifdef TIP3_ENABLE_LEND_OWNERSHIP if ( _lend_ownership_ . empty () ) return ; {_} }} . 
 	 	 refine {{ new 'sender : ( auto ) @ "sender" := {} ; {_} }} . 
 	 	 refine {{ { sender } := int_sender () ; {_} }} . 
 	 	 refine {{ if ( (#{ return_ownership }) ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 	 refine {{ { _lend_ownership_ . erase ( (!{ sender }) ) }} . 
 	 refine {{ { auto (!{ v }) = _lend_ownership_ [ (!{ sender }) ] ; {_} }} . 
 	 refine {{ (!{ v }) ^^ lend_balance - = (#{ tokens }) ; {_} }} . 
 	 refine {{ if ( ~ (!{ v }) ^^ lend_balance ) then { {_:UEf} } else { {_:UEf} } ; {_} }} . 
 	 	 refine {{ _lend_ownership_ ^^ erase ( (!{ sender }) ) }} . 
 
 
 
 
 Defined . 
 
 
 
 
 Definition optional_owner ( owner : ( XAddress ) ) : UExpression XMaybe XAddress false . 
 {{ return_ Std :: get < addr_std > ( (#{ owner }) () ) . address ? std::optional ( (#{ owner }) ) : std::optional () }} . 
 Defined . 
 
 
 
 
 Definition calc_wallet_init_hash ( pubkey : ( uint256 ) ) ( internal_owner : ( XAddress ) ) : UExpression ( StateInitLRecord * uint256 ) false . 
 {{ new 'wallet_data : ( DTONTokenWalletLRecord ) @ "wallet_data" := {} ; {_} }} . 
 	 	 refine {{ { wallet_data } := prepare_wallet_data_ ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ pubkey }) , _root_address_ , optional_owner_ ( (#{ internal_owner }) ) , _code_ , _workchain_id_ ) ; {_} }} . 
 	 	 refine {{ return_ prepare_wallet_state_init_and_addr_ ( (!{ wallet_data }) ) }} . 
 Defined . 
 
 
 
 
 Definition expected_sender_address ( sender_public_key : ( uint256 ) ) ( sender_owner : ( XAddress ) ) : UExpression uint256 false . 
 {{ return_ calc_wallet_init_hash_ ( (#{ sender_public_key }) , (#{ sender_owner }) ) . second }} . 
 Defined . 
 
 
 
 
 Definition calc_wallet_init ( pubkey : ( uint256 ) ) ( internal_owner : ( XAddress ) ) : UExpression ( StateInitLRecord * XAddress ) false . 
 {{ wallet_init : ( auto ) @ "wallet_init" ; {_} }} . 
 	 	 refine {{ dest_addr : ( auto ) @ "dest_addr" ; {_} }} . 
 	 	 refine {{ [ wallet_init , dest_addr ] := calc_wallet_init_hash_ ( (#{ pubkey }) , (#{ internal_owner }) ) ; {_} }} . 
 	 	 refine {{ new 'dest : ( XAddress ) @ "dest" := {} ; {_} }} . 
 	 	 refine {{ { dest } := Address :: make_std ( _workchain_id_ , dest_addr ) ; {_} }} . 
 	 	 refine {{ return_ [ wallet_init , (!{ dest }) ] }} . 
 Defined . 
 
 
 
 
 Definition filter_lend_ownerhip_array : UExpression ( lend_ownership_arrayLRecord * uint128 ) false . 
 {{ #ifdef TIP3_ENABLE_LEND_OWNERSHIP if ( _lend_ownership_ . empty () ) return {} ; {_} }} . 
 	 	 refine {{ new 'now_v : ( auto ) @ "now_v" := {} ; {_} }} . 
 	 	 refine {{ { now_v } := tvm_now () ; {_} }} . 
 	 	 refine {{ lend_ownership_array rv ; {_} }} . 
 	 	 refine {{ uint128 lend_balance ; {_} }} . 
 	 	 refine {{ for ( auto (!{ v }) : _lend_ownership_ ) { _ } ; {_} }} . 
 
 Defined . 

 Definition prepare_wallet_data ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( uint8 ) ) ( root_public_key : ( uint256 ) ) ( wallet_public_key : ( uint256 ) ) ( root_address : ( XAddress ) ) ( owner_address : ( XMaybe XAddress ) ) ( code : ( XCell ) ) ( workchain_id : ( uint8 ) ) : UExpression DTONTokenWalletLRecord false . 
 {{ return_ [ (#{ name }) , (#{ symbol }) , (#{ decimals }) , 0 , (#{ root_public_key }) , (#{ wallet_public_key }) , (#{ root_address }) , (#{ owner_address }) , #ifdef TIP3_ENABLE_LEND_OWNERSHIP {} , #endif (#{ code }) , #ifdef TIP3_ENABLE_ALLOWANCE {} , #endif (#{ workchain_id }) ] }} . 
 Defined . 
 
 
 
 
 Definition prepare_wallet_state_init_and_addr ( (!{ wallet_data }) : ( DTONTokenWalletLRecord ) ) : UExpression ( StateInitLRecord * uint256 ) false . 
 {{ new 'wallet_data_cl : ( XCell ) @ "wallet_data_cl" := {} ; {_} }} . 
 	 	 refine {{ { wallet_data_cl } := prepare_persistent_data ( #ifdef TIP3_ENABLE_EXTERNAL wallet_replay_protection_t::init () , #else {} , #endif (#{ (!{ wallet_data }) }) ) ; {_} }} . 
 	 	 refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 	 	 
 	 	 	 [$ $] ; {_} }} . 
 	 	 refine {{ new 'wallet_init_cl : ( XCell ) @ "wallet_init_cl" := {} ; {_} }} . 
 	 	 refine {{ { wallet_init_cl } := build ( (!{ wallet_init }) ) . make_cell () ; {_} }} . 
 	 	 refine {{ return_ [ (!{ wallet_init }) , tvm_hash ( (!{ wallet_init_cl }) ) ] }} . 
 Defined . 
 
 
 
 
 Definition prepare_external_wallet_state_init_and_addr ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( uint8 ) ) ( root_public_key : ( uint256 ) ) ( wallet_public_key : ( uint256 ) ) ( root_address : ( XAddress ) ) ( owner_address : ( XMaybe XAddress ) ) ( code : ( XCell ) ) ( workchain_id : ( uint8 ) ) : UExpression ( StateInitLRecord * uint256 ) false . 
 {{ new 'wallet_data : ( DTONTokenWalletExternalLRecord ) @ "wallet_data" := 	 	 
 	 	 	 [ (#{ name }) , (#{ symbol }) , (#{ decimals }) , uint128 ( 0 ) , (#{ root_public_key }) , (#{ wallet_public_key }) , (#{ root_address }) , (#{ owner_address }) , (#{ code }) , {} , (#{ workchain_id }) ] ; {_} }} . 
 	 	 refine {{ new 'wallet_data_cl : ( XCell ) @ "wallet_data_cl" := {} ; {_} }} . 
 	 	 refine {{ { wallet_data_cl } := prepare_persistent_data ( external_wallet_replay_protection_t::init () , (!{ wallet_data }) ) ; {_} }} . 
 	 	 refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 	 	 
 	 	 	 [ {} , {} , (#{ code }) , (!{ wallet_data_cl }) , {} ] ; {_} }} . 
 	 	 refine {{ new 'wallet_init_cl : ( XCell ) @ "wallet_init_cl" := {} ; {_} }} . 
 	 	 refine {{ { wallet_init_cl } := build ( (!{ wallet_init }) ) . make_cell () ; {_} }} . 
 	 	 refine {{ return_ [ (!{ wallet_init }) , tvm_hash ( (!{ wallet_init_cl }) ) ] }} . 
 Defined . 
 
 
 
 
 Definition prepare_internal_wallet_state_init_and_addr ( name : ( XString ) ) ( symbol : ( XString ) ) ( decimals : ( uint8 ) ) ( root_public_key : ( uint256 ) ) ( wallet_public_key : ( uint256 ) ) ( root_address : ( XAddress ) ) ( owner_address : ( XMaybe XAddress ) ) ( code : ( XCell ) ) ( workchain_id : ( uint8 ) ) : UExpression ( StateInitLRecord * uint256 ) false . 
 {{ new 'wallet_data : ( DTONTokenWallet(#{Internal})LRecord ) @ "wallet_data" := 	 	 
 	 	 	 [ (#{ name }) , (#{ symbol }) , (#{ decimals }) , uint128 ( 0 ) , (#{ root_public_key }) , (#{ wallet_public_key }) , (#{ root_address }) , (#{ owner_address }) , {} , (#{ code }) , (#{ workchain_id }) ] ; {_} }} . 
 	 	 refine {{ new 'wallet_data_cl : ( XCell ) @ "wallet_data_cl" := {} ; {_} }} . 
 	 	 refine {{ { wallet_data_cl } := prepare_persistent_data ( {} , (!{ wallet_data }) ) ; {_} }} . 
 	 	 refine {{ new 'wallet_init : ( StateInitLRecord ) @ "wallet_init" := 	 	 
 	 	 	 [ {} , {} , (#{ code }) , (!{ wallet_data_cl }) , {} ] ; {_} }} . 
 	 	 refine {{ new 'wallet_init_cl : ( XCell ) @ "wallet_init_cl" := {} ; {_} }} . 
 	 	 refine {{ { wallet_init_cl } := build ( (!{ wallet_init }) ) . make_cell () ; {_} }} . 
 	 	 refine {{ return_ [ (!{ wallet_init }) , tvm_hash ( (!{ wallet_init_cl }) ) ] }} . 
 Defined . 
 
 
 
 
 Definition prepare_root_state_init_and_addr ( root_code : ( XCell ) ) ( root_data : ( DRootTokenContractLRecord ) ) : UExpression ( StateInitLRecord * uint256 ) false . 
 {{ new 'root_data_cl : ( XCell ) @ "root_data_cl" := {} ; {_} }} . 
 	 	 refine {{ { root_data_cl } := prepare_persistent_data ( root_replay_protection_t::init () , (#{ root_data }) ) ; {_} }} . 
 	 	 refine {{ new 'root_init : ( StateInitLRecord ) @ "root_init" := 	 	 
 	 	 	 [ {} , {} , (#{ root_code }) , (!{ root_data_cl }) , {} ] ; {_} }} . 
 	 	 refine {{ new 'root_init_cl : ( XCell ) @ "root_init_cl" := {} ; {_} }} . 
 	 	 refine {{ { root_init_cl } := build ( (!{ root_init }) ) . make_cell () ; {_} }} . 
 	 	 refine {{ return_ [ (!{ root_init }) , tvm_hash ( (!{ root_init_cl }) ) ] }} . 
 Defined . 
 
 
 
 
 .


End Funcs(#{Internal}).
End Funcs.








