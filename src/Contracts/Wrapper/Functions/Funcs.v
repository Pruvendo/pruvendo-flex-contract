Definition getStateInit ( &msg : () ) : UExpression StateInitLRecord flase . 
 {{ if ( msg_init - > isa < ref < StateInit > > () ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ { return msg_init - > get < ref < StateInit > > () () }} . 
 	 refine {{ { return msg_init - > get < StateInit > () }} . 
 
 
 Defined . 
 
 
 
 
 Definition init ( external_wallet : ( XAddress ) ) : UExpression XBool true . 
 {{ require_ ( ( ~ _external_wallet_ ) , error_code::cant_override_external_wallet ) ; _ }} . 
 	 	 refine {{ new 'parsed_msg : ( auto ) @ "parsed_msg" := {} ; _ }} . 
 	 	 refine {{ { parsed_msg } := parse ( parser ( msg_slice () ) , error_code::bad_incoming_msg ) ; _ }} . 
 	 	 refine {{ require_ ( ( ~ ~ parsed_msg_init ) , error_code::bad_incoming_msg ) ; _ }} . 
 	 	 refine {{ new 'init : ( auto ) @ "init" := {} ; _ }} . 
 	 	 refine {{ init_ := getStateInit_ ( (!{ parsed_msg }) ) ; _ }} . 
 	 	 refine {{ require_ ( ( ~ ~ init_ ^^ auto:code ) , error_code::bad_incoming_msg ) ; _ }} . 
 	 	 refine {{ new 'mycode : ( auto ) @ "mycode" := {} ; _ }} . 
 	 	 refine {{ { mycode } := *init ^^ code ; _ }} . 
 	 	 refine {{ require_ ( ( (!{ mycode }) ^^ auto:ctos () . srefs () == 3 ) , error_code::unexpected_refs_count_in_code ) ; _ }} . 
 	 	 refine {{ parser mycode_parser ( (!{ mycode }) . ctos () ) ; _ }} . 
 	 	 refine {{ mycode_parser ^^ ldref () ; _ }} . 
 	 	 refine {{ mycode_parser ^^ ldref () ; _ }} . 
 	 	 refine {{ new 'mycode_salt : ( auto ) @ "mycode_salt" := {} ; _ }} . 
 	 	 refine {{ { mycode_salt } := mycode_parser ^^ ldrefrtos () ; _ }} . 
 	 	 refine {{ new 'flex_addr : ( auto ) @ "flex_addr" := {} ; _ }} . 
 	 	 refine {{ { flex_addr } := parse ( (!{ mycode_salt }) ) ; _ }} . 
 	 	 refine {{ require_ ( ( (!{ flex_addr }) == int_sender () ) , error_code::only_flex_may_deploy_me ) ; _ }} . 
 	 	 refine {{ _external_wallet_ := (#{ external_wallet }) ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( _start_balance_ . get () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ return bool_t TRUE }} . 
 Defined . 
 
 
 
 
 Definition setInternalWalletCode ( wallet_code : ( XCell ) ) : UExpression XBool true . 
 {{ check_owner_ () ; _ }} . 
 	 	 refine {{ tvm.accept () ; _ }} . 
 	 	 refine {{ require_ ( ( ~ _internal_wallet_code_ ) , error_code::cant_override_wallet_code ) ; _ }} . 
 	 	 refine {{ _internal_wallet_code_ := (#{ wallet_code }) ; _ }} . 
 	 	 refine {{ if ( Internal ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ { auto value_gr = int_value () ; _ }} . 
 	 	 	 refine {{ tvm.rawreserve ( tvm.balance () - value_gr () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) }} . 
 	 refine {{ return bool_t TRUE ; _ }} . 
 
 Defined . 
 
 
 
 
 Definition deployEmptyWallet ( pubkey : ( XUInteger256 ) ) ( internal_owner : ( XAddress ) ) ( grams : ( XUInteger128 ) ) : UExpression XAddress flase . 
 {{ new 'value_gr : ( auto ) @ "value_gr" := {} ; _ }} . 
 	 	 refine {{ { value_gr } := int_value () ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
 	 	 refine {{ dest : ( auto ) @ "dest" ; _ }} . 
 	 	 refine {{ [ wallet_init , dest ] := calc_internal_wallet_init_ ( (#{ pubkey }) , (#{ internal_owner }) ) ; _ }} . 
 	 	 refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; _ }} . 
 	 	 refine {{ dest_handle ^^ deploy_noop ( wallet_init , Grams ( (#{ grams }) . get () ) ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ return_ dest }} . 
 Defined . 
 
 
 
 
 Definition onTip3Transfer ( answer_addr : ( XAddress ) ) ( balance : ( XUInteger128 ) ) ( new_tokens : ( XUInteger128 ) ) ( sender_pubkey : ( XUInteger256 ) ) ( sender_owner : ( XAddress ) ) ( payload : ( XCell ) ) : UExpression WrapperRetLRecord true . 
 {{ require_ ( ( int_sender () == _external_wallet_ - > get () ) , error_code::not_my_wallet_notifies ) ; _ }} . 
 	 	 refine {{ set_int_sender ( (#{ answer_addr }) ) ; _ }} . 
 	 	 refine {{ set_int_return_value ( 0 ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ new 'args : ( auto ) @ "args" := {} ; _ }} . 
 	 	 refine {{ { args } := parse ( (#{ payload }) . ctos () ) ; _ }} . 
 	 	 refine {{ new 'value_gr : ( auto ) @ "value_gr" := {} ; _ }} . 
 	 	 refine {{ { value_gr } := int_value () ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
 	 	 refine {{ dest : ( auto ) @ "dest" ; _ }} . 
 	 	 refine {{ [ wallet_init , dest ] := calc_internal_wallet_init_ ( (!{ args }) . pubkey , (!{ args }) . internal_owner ) ; _ }} . 
 	 	 refine {{ ITONTokenWalletPtr dest_handle ( dest ) ; _ }} . 
 	 	 refine {{ dest_handle ^^ deploy ( wallet_init , Grams ( (!{ args }) . grams . get () ) ) . accept ( (#{ new_tokens }) , int_sender () , (!{ args }) . grams ) ; _ }} . 
 	 	 refine {{ _total_granted_ += (#{ new_tokens }) ; _ }} . 
 	 	 refine {{ return_ [ 0 , dest_handle ^^ get () ] }} . 
 Defined . 
 
 
 
 
 Definition burn ( answer_addr : ( XAddress ) ) ( sender_pubkey : ( XUInteger256 ) ) ( sender_owner : ( XAddress ) ) ( out_pubkey : ( XUInteger256 ) ) ( out_internal_owner : ( XAddress ) ) ( tokens : ( XUInteger128 ) ) : UExpression PhantomType true . 
 {{ require_ ( ( _total_granted_ >= (#{ tokens }) ) , error_code::burn_unallocated ) ; _ }} . 
 	 	 refine {{ sender : ( auto ) @ "sender" ; _ }} . 
 	 	 refine {{ (!{ value_gr }) : ( auto ) @ "value_gr" ; _ }} . 
 	 	 refine {{ [ sender , { value_gr } ] := int_sender_and_value () ; _ }} . 
 	 	 refine {{ require_ ( ( sender == expected_internal_address_ ( (#{ sender_pubkey }) ) , (#{ sender_owner }) ) ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ ( *external_wallet_ ) ( Grams ( 0 ) , SEND_ALL_GAS ) . transferToRecipient ( (#{ answer_addr }) , (#{ out_pubkey }) , (#{ out_internal_owner }) , (#{ tokens }) , uint128 ( 0 ) , bool_t TRUE , bool_t FALSE ) ; _ }} . 
 	 	 refine {{ _total_granted_ -= (#{ tokens }) }} . 
 Defined . 
 
 
 
 
 Definition requestTotalGranted : UExpression XUInteger128 flase . 
 {{ new 'value_gr : ( auto ) @ "value_gr" := {} ; _ }} . 
 	 	 refine {{ { value_gr } := int_value () ; _ }} . 
 	 	 refine {{ tvm.rawreserve ( tvm.balance () - (!{ value_gr }) () , rawreserve_flag::up_to ) ; _ }} . 
 	 	 refine {{ Set_int_return_flag ( SEND_ALL_GAS ) ; _ }} . 
 	 	 refine {{ return_ _total_granted_ }} . 
 Defined . 
 
 
 
 
 Definition getDetails : UExpression wrapper_details_infoLRecord flase . 
 {{ return_ [ getName_ () , getSymbol_ () , getDecimals_ () , getRootKey_ () , getTotalGranted_ () , getInternalWalletCode_ () , getOwnerAddress_ () , getExternalWallet_ () ] }} . 
 Defined . 
 
 
 
 
 Definition getName : UExpression XString flase . 
 {{ return_ _name_ }} . 
 Defined . 
 
 
 
 
 Definition getSymbol : UExpression XString flase . 
 {{ return_ _symbol_ }} . 
 Defined . 
 
 
 
 
 Definition getDecimals : UExpression XUInteger8 flase . 
 {{ return_ _decimals_ }} . 
 Defined . 
 
 
 
 
 Definition getRootKey : UExpression XUInteger256 flase . 
 {{ return_ _root_public_key_ }} . 
 Defined . 
 
 
 
 
 Definition getTotalGranted : UExpression XUInteger128 flase . 
 {{ return_ _total_granted_ }} . 
 Defined . 
 
 
 
 
 Definition hasInternalWalletCode : UExpression XBool flase . 
 {{ return bool_t { ~ ~ _internal_wallet_code_ } }} . 
 Defined . 
 
 
 
 
 Definition getInternalWalletCode : UExpression XCell flase . 
 {{ return_ _internal_wallet_code_ ^^ get () }} . 
 Defined . 
 
 
 
 
 Definition getOwnerAddress : UExpression XAddress flase . 
 {{ return_ _owner_address_ ? *owner_address_ : Address :: make_std ( 0 , 0 ) }} . 
 Defined . 
 
 
 
 
 Definition getExternalWallet : UExpression XAddress flase . 
 {{ return_ _external_wallet_ - > get () }} . 
 Defined . 
 
 
 
 
 Definition getWalletAddress ( pubkey : ( XUInteger256 ) ) ( owner : ( XAddress ) ) : UExpression XAddress flase . 
 {{ return_ calc_internal_wallet_init_ ( (#{ pubkey }) , (#{ owner }) ) . second }} . 
 Defined . 
 
 
 
 
 Definition _on_bounced ( cell : ( (LRecord ) ) ( msg_body : ( XSlice ) ) : UExpression XUInteger true . 
 {{ tvm.accept () ; _ }} . 
 	 	 refine {{ new 'Args : ( usingLRecord ) @ "Args" := {} ; _ }} . 
 	 	 refine {{ { Args } := args_struct_t ; _ }} . 
 	 	 refine {{ parser p ( (#{ msg_body }) ) ; _ }} . 
 	 	 refine {{ require_ ( ( p ^^ ldi ( 32 ) == - 1 ) , error_code::wrong_bounced_header ) ; _ }} . 
 	 	 refine {{ opt_hdr : ( auto ) @ "opt_hdr" ; _ }} . 
 	 	 refine {{ =p : ( auto ) @ "=p" ; _ }} . 
 	 	 refine {{ [ opt_hdr , =p ] := parse_continue < abiv1::internal_msg_header > ( p ) ; _ }} . 
 	 	 refine {{ require_ ( ( opt_hdr && opt_hdr - > function_id == id_v < &ITONTokenWallet::accept > ) , error_code::wrong_bounced_header ) ; _ }} . 
 	 	 refine {{ new 'args : ( auto ) @ "args" := {} ; _ }} . 
 	 	 refine {{ { args } := parse ( p , error_code::wrong_bounced_args ) ; _ }} . 
 	 	 refine {{ new 'bounced_val : ( auto ) @ "bounced_val" := {} ; _ }} . 
 	 	 refine {{ { bounced_val } := (!{ args }) ^^ auto:tokens ; _ }} . 
 	 	 refine {{ hdr : ( auto ) @ "hdr" ; _ }} . 
 	 	 refine {{ persist : ( auto ) @ "persist" ; _ }} . 
 	 	 refine {{ [ hdr , persist ] := load_persistent_data < IWrapper , wrapper_replay_protection_t , DWrapper > () ; _ }} . 
 	 	 refine {{ require_ ( ( (!{ bounced_val }) <= persist ^^ _total_granted_ ) , error_code::wrong_bounced_args ) ; _ }} . 
 	 	 refine {{ persist ^^ _total_granted_ - = (!{ bounced_val }) ; _ }} . 
 	 	 refine {{ save_persistent_data < IWrapper , wrapper_replay_protection_t > ( hdr , persist ) ; _ }} . 
 	 	 refine {{ return_ 0 }} . 
 Defined . 
 
 
 
 
 Definition getInternalWalletCodeHash : UExpression XUInteger256 flase . 
 {{ return uint256 { __builtin_tvm.hashcu ( _internal_wallet_code_ . get () ) } }} . 
 Defined . 
 
 
 
 
 Definition _fallback ( cell : ( (LRecord ) ) : UExpression XUInteger flase . 
 {{ return_ 0 }} . 
 Defined . 
 
 
 
 
 Definition optional_owner ( owner : ( XAddress ) ) : UExpression XMaybe XAddress flase . 
 {{ return_ Std :: get < addr_std > ( (#{ owner }) () ) . address ? std::optional ( (#{ owner }) ) : std::optional () }} . 
 Defined . 
 
 
 
 
 Definition expected_internal_address ( sender_public_key : ( XUInteger256 ) ) ( sender_owner_addr : ( XAddress ) ) : UExpression XAddress flase . 
 {{ new 'hash_addr : ( XUInteger256 ) @ "hash_addr" := {} ; _ }} . 
 	 	 refine {{ { hash_addr } := prepare_internal_wallet_state_init_and_addr ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ sender_public_key }) , Address { tvm.address () } , optional_owner_ ( (#{ sender_owner_addr }) ) , _internal_wallet_code_ ^^ get () , _workchain_id_ ) . second ; _ }} . 
 	 	 refine {{ return_ Address :: make_std ( _workchain_id_ , (!{ hash_addr }) ) }} . 
 Defined . 
 
 
 
 
 Definition calc_internal_wallet_init ( pubkey : ( XUInteger256 ) ) ( owner_addr : ( XAddress ) ) : UExpression ( StateInitLRecord * XAddress ) flase . 
 {{ wallet_init : ( auto ) @ "wallet_init" ; _ }} . 
 	 	 refine {{ dest_addr : ( auto ) @ "dest_addr" ; _ }} . 
 	 	 refine {{ [ wallet_init , dest_addr ] := prepare_internal_wallet_state_init_and_addr ( _name_ , _symbol_ , _decimals_ , _root_public_key_ , (#{ pubkey }) , address { tvm.address () } , optional_owner_ ( (#{ owner_addr }) ) , _internal_wallet_code_ . get () , _workchain_id_ ) ; _ }} . 
 	 	 refine {{ new 'dest : ( XAddress ) @ "dest" := {} ; _ }} . 
 	 	 refine {{ { dest } := Address :: make_std ( _workchain_id_ , dest_addr ) ; _ }} . 
 	 	 refine {{ return_ [ wallet_init , (!{ dest }) ] }} . 
 Defined . 
 
 
 
 
 Definition is_internal_owner : UExpression XBool flase . 
 {{ return_ _owner_address_ ^^ has_value () }} . 
 Defined . 
 
 
 
 
 Definition check_internal_owner : UExpression PhantomType true . 
 {{ require_ ( ( is_internal_owner_ () ) , error_code::internal_owner_disabled ) ; _ }} . 
 	 	 refine {{ require_ ( ( *owner_address_ == int_sender () ) , error_code::message_sender_is_not_my_owner ) }} . 
 Defined . 
 
 
 
 
 Definition check_external_owner : UExpression PhantomType true . 
 {{ require_ ( ( ~ is_internal_owner_ () ) , error_code::internal_owner_enabled ) ; _ }} . 
 	 	 refine {{ require_ ( ( msg.pubkey () == _root_public_key_ ) , error_code::message_sender_is_not_my_owner ) }} . 
 Defined . 
 
 
 
 
 Definition check_owner : UExpression PhantomType flase . 
 {{ if ( Internal ) then { _ } else { _ } ; _ }} . 
 	 	 	 refine {{ check_internal_owner_ () }} . 
 	 	 refine {{ check_external_owner_ () ; _ }} . 
 
 
 Defined . 
 
 
 
 
 Definition prepare_wrapper_state_init_and_addr ( wrapper_code : ( XCell ) ) ( wrapper_data : ( DWrapperLRecord ) ) : UExpression ( StateInitLRecord * XUInteger256 ) flase . 
 {{ new 'wrapper_data_cl : ( XCell ) @ "wrapper_data_cl" := {} ; _ }} . 
 	 	 refine {{ { wrapper_data_cl } := prepare_persistent_data ( wrapper_replay_protection_t::init () , (#{ wrapper_data }) ) ; _ }} . 
 	 	 refine {{ new 'wrapper_init : ( StateInitLRecord ) @ "wrapper_init" := 	 	 
 	 	 	 [ {} , {} , (#{ wrapper_code }) , (!{ wrapper_data_cl }) , {} ] ; _ }} . 
 	 	 refine {{ new 'wrapper_init_cl : ( XCell ) @ "wrapper_init_cl" := {} ; _ }} . 
 	 	 refine {{ { wrapper_init_cl } := build ( (!{ wrapper_init }) ) . make_cell () ; _ }} . 
 	 	 refine {{ return_ [ (!{ wrapper_init }) , tvm.hash ( (!{ wrapper_init_cl }) ) ] }} . 
 Defined . 
 
 
 
 
 .