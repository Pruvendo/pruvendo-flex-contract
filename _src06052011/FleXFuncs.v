
 Definition dealer_Ф_make_deal ( sell : SellInfoP ) ( buy : BuyInfoP ) 
 : SMLExpression (S:=Ledger) false ( XBool # XBool # XInteger128 ) XInteger := 
 WeakBinding ( ResultExpression ( init SellInfoP Л_sell0 := sell ) ) of 
 WeakBinding ( ResultExpression ( init BuyInfoP Л_buy0 := buy ) ) of 
 {{ 
 Л_deal_amount0_ := ^ std::min ( Л_sell0_ ^^ SellInfo_ι_amount , Л_buy0_ ^^ BuyInfo_ι_amount ) ; 
 Л_last_tip3_sell0_ { Л_sell0_ ^^ SellInfo_ι_amount == Л_deal_amount0_ } ; 
 Л_sell0_ ^^ SellInfo_ι_amount -= ^ Л_deal_amount0_ ; 
 Л_buy0_ ^^ BuyInfo_ι_amount -= ^ Л_deal_amount0_ ; 
 Л_cost0_ := ^ Ф_calc_cost ( Л_deal_amount0_ , price_ ) ; 
 Л_sell_costs0_ { 0 } ; 
 Л_buy_costs0_ := ^ *cost ; 
 if ^ ( Л_last_tip3_sell0_ ) then { sell_costs += ^ ( dealer_ι_tons_cfg_ ^^ transfer_tip3 + dealer_ι_tons_cfg_ ^^ send_notify ) } ; 
 else buy_costs += ^ ( dealer_ι_tons_cfg_ ^^ transfer_tip3 + dealer_ι_tons_cfg_ ^^ send_notify ) ; 
 Л_sell_out_of_tons0_ := ^ ( Л_sell0_ ^^ SellInfo_ι_account < Л_sell_costs0_ ) ; 
 Л_buy_out_of_tons0_ := ^ ( Л_buy0_ ^^ BuyInfo_ι_account < Л_buy_costs0_ ) ; 
 if ^ ( Л_sell_out_of_tons0_ || Л_buy_out_of_tons0_ ) then { ρ return [ Л_sell_out_of_tons0_ , Л_buy_out_of_tons0_ , uint128 ( 0 ) ] 
 }} Parameter Л_sell_idx1 : XString . 
 
 Definition dealer_Ф_process_queue ( sell_idx : XInteger ) ( buy_idx : XInteger ) 
 : SMLExpression (S:=Ledger) false True XInteger := 
 WeakBinding ( ResultExpression ( init int Л_sell_idx1 := sell_idx ) ) of 
 WeakBinding ( ResultExpression ( init int Л_buy_idx1 := buy_idx ) ) of 
 {{ 
 Л_sell_opt1_ := ^ dealer_ι_sells_ ^^ front_with_idx_opt ( ) ; 
 Л_buy_opt1_ := ^ dealer_ι_buys_ ^^ front_with_idx_opt ( ) ; 
 Л_deals_count1_ := ^ 0 ; 
 while ( Л_sell_opt1_ && buy_opt ) { [ Л_sell_idx_cur1_ Л_sell1_ ] := ^ *sell_opt ; 
 [ Л_buy_idx_cur1_ Л_buy1_ ] := ^ *buy_opt ; 
 if ^ ( + + Л_deals_count1_ > deals_limit_ ) then { IPricePtr ( address { tvm_myaddr ( ) } ) ( Grams ( dealer_ι_tons_cfg_ ^^ process_queue . 
 
 Definition DPrice_Ф_onTip3LendOwnership ( balance : XInteger128 ) ( lend_finish_time : XInteger32 ) ( pubkey : XInteger256 ) ( internal_owner : XInteger256 ) ( payload_cl : XCell ) ( answer_addr : XAddress ) 
 : SMLExpression (S:=Ledger) false OrderRetP XInteger := 
 WeakBinding ( ResultExpression ( init int Л_balance2 := balance ) ) of 
 WeakBinding ( ResultExpression ( init int Л_lend_finish_time2 := lend_finish_time ) ) of 
 WeakBinding ( ResultExpression ( init int Л_pubkey2 := pubkey ) ) of 
 WeakBinding ( ResultExpression ( init int Л_internal_owner2 := internal_owner ) ) of 
 WeakBinding ( ResultExpression ( init cell Л_payload_cl2 := payload_cl ) ) of 
 WeakBinding ( ResultExpression ( init addr Л_answer_addr2 := answer_addr ) ) of 
 {{ 
 [ Л_tip3_wallet2_ Л_value2_ ] := ^ int_sender_and_value ( ) ; 
 ITONTokenWalletPtr wallet_in ( Л_tip3_wallet2_ ) ; 
 Grams ret_owner_gr ( DPrice_ι_tons_cfg_ ^^ return_ownership . 
 
 Definition DPrice_Ф_buyTip3 ( amount : XInteger128 ) ( receive_tip3_wallet : XAddress ) 
 : SMLExpression (S:=Ledger) false OrderRetP XInteger := 
 WeakBinding ( ResultExpression ( init int Л_amount3 := amount ) ) of 
 WeakBinding ( ResultExpression ( init addr Л_receive_tip3_wallet3 := receive_tip3_wallet ) ) of 
 {{ 
 [ Л_sender3_ Л_value_gr3_ ] := ^ int_sender_and_value ( ) ; 
 Require ( amount >= ^ min_amount_ , ec::not_enough_tokens_amount ) ; 
 ; 
 Л_cost3_ := ^ Ф_calc_cost ( Л_amount3_ , price_ ) ; 
 Require ( ! ! Л_cost3_ , ec::too_big_tokens_amount ) ; 
 ; 
 Require ( Л_value_gr3_ ^^ get ( ) > *cost + DPrice_ι_tons_cfg_ ^^ process_queue + DPrice_ι_tons_cfg_ ^^ order_answer , ec::not_enough_tons_to_process ) ; 
 ; 
 set_int_return_value ( DPrice_ι_tons_cfg_ ^^ order_answer . 
 
 Definition DPrice_Ф_processQueue 
 : SMLExpression (S:=Ledger) false True XInteger := 
 {{ 
 if ^ ( DPrice_ι_sells_ ^^ empty ( ) || DPrice_ι_buys_ ^^ empty ( ) ) then { || DPrice_ι_buys_ ^^ empty ( ) ) ρ return I } ; 
 [ Л_sells_amount4_ Л_sells4_ Л_buys_amount4_ Л_buys4_ Л_ret4_ ] := ^ Ф_process_queue_impl ( DPrice_ι_tip3cfg_ ^^ root_address , notify_addr_ , price_ , deals_limit_ , tons_cfg_ , 0 , 0 , sells_amount_ , sells_ , buys_amount_ , buys_ ) ; 
 sells_ := ^ Л_sells4_ ; 
 buys_ := ^ Л_buys4_ ; 
 sells_amount_ := ^ Л_sells_amount4_ ; 
 buys_amount_ := ^ Л_buys_amount4_ ; 
 if ^ ( DPrice_ι_sells_ ^^ empty ( ) && DPrice_ι_buys_ ^^ empty ( ) ) then { && DPrice_ι_buys_ ^^ empty ( ) ) suicide ( stock_ ) } ; 
 
 }} Parameter Л_receive_wallet5 : XString . 
 
 Definition DPrice_Ф_cancelSell 
 : SMLExpression (S:=Ledger) false True XInteger := 
 {{ 
 Л_receive_wallet5_ := ^ int_sender ( ) ; 
 for ( Л_it5_ := ^ DPrice_ι_sells_ ^^ begin ( ) ; 
 it != ^ DPrice_ι_sells_ ^^ end ( ) ; 
 ) { Л_next_it5_ := ^ std::next ( Л_it5_ ) ; 
 Л_sell5_ := ^ *it ; 
 if ^ ( Л_sell5_ ^^ receive_wallet == receive_wallet ) then { ITONTokenWalletPtr ( Л_sell5_ ^^ tip3_wallet ) ( Grams ( DPrice_ι_tons_cfg_ ^^ return_ownership . 
 
 Definition DPrice_Ф_cancelBuy 
 : SMLExpression (S:=Ledger) false True XInteger := 
 {{ 
 Л_answer_addr6_ := ^ int_sender ( ) ; 
 for ( Л_it6_ := ^ DPrice_ι_buys_ ^^ begin ( ) ; 
 it != ^ DPrice_ι_buys_ ^^ end ( ) ; 
 ) { Л_next_it6_ := ^ std::next ( Л_it6_ ) ; 
 Л_buy6_ := ^ *it ; 
 if ^ ( Л_buy6_ ^^ answer_addr == answer_addr ) then { Л_ret6_ { uint32 ( ec::canceled ) , Л_buy6_ ^^ original_amount - Л_buy6_ ^^ amount , uint128 { 0 } } ; 
 IPriceCallbackPtr ( Л_buy6_ ^^ answer_addr ) ( Grams ( Л_buy6_ ^^ account . 
 
 Definition DPrice_Ф_getDetails 
 : SMLExpression (S:=Ledger) false DetailsInfoP XInteger := 
 {{ 
 ρ return [ DPrice_Ф_getPrice ( ) , DPrice_Ф_getMinimumAmount ( ) , DPrice_Ф_getSellAmount ( ) , DPrice_Ф_getBuyAmount ( ) ] 
 }} Definition DPrice_Ф_getPrice 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ price_ ; 
 ; 
 
 }} Definition DPrice_Ф_getMinimumAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ min_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getTonsCfg 
 : SMLExpression (S:=Ledger) false TonsConfigP XInteger := 
 {{ 
 ρ return ^ tons_cfg_ ; 
 ; 
 
 }} Definition DPrice_Ф_getSells 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < SellInfo > ( DPrice_ι_sells_ ^^ begin ( ) , DPrice_ι_sells_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getBuys 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < BuyInfo > ( DPrice_ι_buys_ ^^ begin ( ) , DPrice_ι_buys_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getSellAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ sells_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getBuyAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ buys_amount_ ; 
 ; 
 
 }} Parameter Л_msg15 : XString . 
 
 Definition DPrice_Ф_getPrice 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ price_ ; 
 ; 
 
 }} Definition DPrice_Ф_getMinimumAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ min_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getTonsCfg 
 : SMLExpression (S:=Ledger) false TonsConfigP XInteger := 
 {{ 
 ρ return ^ tons_cfg_ ; 
 ; 
 
 }} Definition DPrice_Ф_getSells 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < SellInfo > ( DPrice_ι_sells_ ^^ begin ( ) , DPrice_ι_sells_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getBuys 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < BuyInfo > ( DPrice_ι_buys_ ^^ begin ( ) , DPrice_ι_buys_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getSellAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ sells_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getBuyAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ buys_amount_ ; 
 ; 
 
 }} Parameter Л_msg15 : XString . 
 
 Definition DPrice_Ф_getMinimumAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ min_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getTonsCfg 
 : SMLExpression (S:=Ledger) false TonsConfigP XInteger := 
 {{ 
 ρ return ^ tons_cfg_ ; 
 ; 
 
 }} Definition DPrice_Ф_getSells 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < SellInfo > ( DPrice_ι_sells_ ^^ begin ( ) , DPrice_ι_sells_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getBuys 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < BuyInfo > ( DPrice_ι_buys_ ^^ begin ( ) , DPrice_ι_buys_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getSellAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ sells_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getBuyAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ buys_amount_ ; 
 ; 
 
 }} Parameter Л_msg15 : XString . 
 
 Definition DPrice_Ф_getTonsCfg 
 : SMLExpression (S:=Ledger) false TonsConfigP XInteger := 
 {{ 
 ρ return ^ tons_cfg_ ; 
 ; 
 
 }} Definition DPrice_Ф_getSells 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < SellInfo > ( DPrice_ι_sells_ ^^ begin ( ) , DPrice_ι_sells_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getBuys 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < BuyInfo > ( DPrice_ι_buys_ ^^ begin ( ) , DPrice_ι_buys_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getSellAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ sells_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getBuyAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ buys_amount_ ; 
 ; 
 
 }} Parameter Л_msg15 : XString . 
 
 Definition DPrice_Ф_getSells 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < SellInfo > ( DPrice_ι_sells_ ^^ begin ( ) , DPrice_ι_sells_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getBuys 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < BuyInfo > ( DPrice_ι_buys_ ^^ begin ( ) , DPrice_ι_buys_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getSellAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ sells_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getBuyAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ buys_amount_ ; 
 ; 
 
 }} Parameter Л_msg15 : XString . 
 
 Definition DPrice_Ф_getBuys 
 : SMLExpression (S:=Ledger) false ( XDictArray ) XInteger := 
 {{ 
 ρ return ^ dict_array < < BuyInfo > ( DPrice_ι_buys_ ^^ begin ( ) , DPrice_ι_buys_ ^^ end ( ) ) ; 
 
 }} Definition DPrice_Ф_getSellAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ sells_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getBuyAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ buys_amount_ ; 
 ; 
 
 }} Parameter Л_msg15 : XString . 
 
 Definition DPrice_Ф_getSellAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ sells_amount_ ; 
 ; 
 
 }} Definition DPrice_Ф_getBuyAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ buys_amount_ ; 
 ; 
 
 }} Parameter Л_msg15 : XString . 
 
 Definition DPrice_Ф_getBuyAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ buys_amount_ ; 
 ; 
 
 }} Parameter Л_msg15 : XString . 
 
 Definition DPrice_Ф__fallback ( msg : XCell ) ( msg_body : XSlice ) 
 : SMLExpression (S:=Ledger) false XInteger XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_msg15 := msg ) ) of 
 WeakBinding ( ResultExpression ( init slice Л_msg_body15 := msg_body ) ) of 
 {{ 
 ρ return ^ 0 ; 
 ; 
 
 }} Parameter Л_tip3_wallet16 : XString . 
 
 Definition DPrice_Ф_verify_tip3_addr ( tip3_wallet : XAddress ) ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) 
 : SMLExpression (S:=Ledger) false XBool XInteger := 
 WeakBinding ( ResultExpression ( init addr Л_tip3_wallet16 := tip3_wallet ) ) of 
 WeakBinding ( ResultExpression ( init int Л_wallet_pubkey16 := wallet_pubkey ) ) of 
 WeakBinding ( ResultExpression ( init int Л_internal_owner16 := internal_owner ) ) of 
 {{ 
 Л_expected_address16_ := ^ DPrice_Ф_expected_wallet_address ( Л_wallet_pubkey16_ , Л_internal_owner16_ ) ; 
 ρ return ^ std::: get < addr_std > ( Л_tip3_wallet16_ ( ) DPrice_ι_) ^^ address == Л_expected_address16_ ; 
 
 }} Parameter Л_wallet_pubkey17 : XString . 
 
 Definition DPrice_Ф_expected_wallet_address ( wallet_pubkey : XInteger256 ) ( internal_owner : XInteger256 ) 
 : SMLExpression (S:=Ledger) false XInteger256 XInteger := 
 WeakBinding ( ResultExpression ( init int Л_wallet_pubkey17 := wallet_pubkey ) ) of 
 WeakBinding ( ResultExpression ( init int Л_internal_owner17 := internal_owner ) ) of 
 {{ 
 std::optional < address > owner_addr ; 
 if ^ ( Л_internal_owner17_ ) then { owner_addr := ^ address::make_std ( workchain_id_ , Л_internal_owner17_ ) } ; 
 Л_wallet_data17_ { DPrice_ι_tip3cfg_ ^^ name , DPrice_ι_tip3cfg_ ^^ symbol , DPrice_ι_tip3cfg_ ^^ decimals , TokensType ( 0 ) , DPrice_ι_tip3cfg_ ^^ root_public_key , Л_wallet_pubkey17_ , DPrice_ι_tip3cfg_ ^^ root_address , owner_addr , { } , DPrice_ι_tip3cfg_ ^^ code , { } , workchain_id_ } ; 
 ρ return prepare_wallet_state_init_and_addr ( Л_wallet_data17_ DPrice_ι_) ^^ second ; 
 ) 
 }} Parameter Л_lend_finish_time18 : XString . 
 
 Definition DPrice_Ф_is_active_time ( lend_finish_time : XInteger32 ) 
 : SMLExpression (S:=Ledger) false XBool XInteger := 
 WeakBinding ( ResultExpression ( init int Л_lend_finish_time18 := lend_finish_time ) ) of 
 {{ 
 ρ return tvm_now ( ) + safe_delay_period < Л_lend_finish_time18_ ^^ int_ι_get ( ) ; 
 
 }} Parameter Л_ec19 : XString . 
 
 Definition DPrice_Ф_on_sell_fail ( ec : XInteger ) ( wallet_in : ITONTokenWalletPtrP ) 
 : SMLExpression (S:=Ledger) false OrderRetP XInteger := 
 WeakBinding ( ResultExpression ( init int Л_ec19 := ec ) ) of 
 WeakBinding ( ResultExpression ( init ITONTokenWalletPtrP Л_wallet_in19 := wallet_in ) ) of 
 {{ 
 Л_incoming_value19_ := ^ int_value ( DPrice_ι_) ^^ get ( ) ; 
 tvm_rawreserve ( tvm_balance ( ) - Л_incoming_value19_ , rawreserve_flag::up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 Л_wallet_in19_ ( Grams ( DPrice_ι_tons_cfg_ ^^ return_ownership . 
 
 Definition DStock_Ф_constructor ( deployer_pubkey : XInteger256 ) ( transfer_tip3 : XInteger128 ) ( return_ownership : XInteger128 ) ( trading_pair_deploy : XInteger128 ) ( order_answer : XInteger128 ) ( dealer_Ф_process_queue : XInteger128 ) ( send_notify : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( notify_addr : XAddress ) 
 : SMLExpression (S:=Ledger) false True XInteger := 
 WeakBinding ( ResultExpression ( init int Л_deployer_pubkey20 := deployer_pubkey ) ) of 
 WeakBinding ( ResultExpression ( init int Л_transfer_tip320 := transfer_tip3 ) ) of 
 WeakBinding ( ResultExpression ( init int Л_return_ownership20 := return_ownership ) ) of 
 WeakBinding ( ResultExpression ( init int Л_trading_pair_deploy20 := trading_pair_deploy ) ) of 
 WeakBinding ( ResultExpression ( init int Л_order_answer20 := order_answer ) ) of 
 WeakBinding ( ResultExpression ( init int Л_process_queue20 := dealer_Ф_process_queue ) ) of 
 WeakBinding ( ResultExpression ( init int Л_send_notify20 := send_notify ) ) of 
 WeakBinding ( ResultExpression ( init int Л_min_amount20 := min_amount ) ) of 
 WeakBinding ( ResultExpression ( init int Л_deals_limit20 := deals_limit ) ) of 
 WeakBinding ( ResultExpression ( init addr Л_notify_addr20 := notify_addr ) ) of 
 {{ 
 deployer_pubkey_ := ^ Л_deployer_pubkey20_ ; 
 min_amount_ := ^ Л_min_amount20_ ; 
 deals_limit_ := ^ Л_deals_limit20_ ; 
 notify_addr_ := ^ Л_notify_addr20_ ; 
 tons_cfg_ := ^ { transfer_tip3 , Л_return_ownership20_ , Л_trading_pair_deploy20_ , Л_order_answer20_ , Л_process_queue20_ , Л_send_notify20_ } ; 
 
 }} Parameter Л_code21 : XString . 
 
 Definition DStock_Ф_setPairCode ( code : XCell ) 
 : SMLExpression (S:=Ledger) false True XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_code21 := code ) ) of 
 {{ 
 Require ( ! DStock_Ф_isFullyInitialized ( ) , error_code::cant_override_code ) ; 
 ; 
 Require ( msg_pubkey ( ) == deployer_pubkey_ , error_code::sender_is_not_deployer ) ; 
 ; 
 tvm_accept ( ) ; 
 Require ( ! pair_code_ , error_code::cant_override_code ) ; 
 ; 
 Require ( Л_code21_ ^^ cell_ι_ctos ( DStock_ι_) ^^ srefs ( ) == 2 , error_code::unexpected_refs_count_in_code ) ; 
 pair_code_ := ^ builder ( DStock_ι_) ^^ stslice ( Л_code21_ ^^ cell_ι_ctos ( ) DStock_ι_) ^^ stref ( build ( address { tvm_myaddr ( ) } DStock_ι_) ^^ endc ( ) DStock_ι_) ^^ endc ( ) ; 
 ) ; 
 
 }} Parameter Л_code22 : XString . 
 
 Definition DStock_Ф_setPriceCode ( code : XCell ) 
 : SMLExpression (S:=Ledger) false True XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_code22 := code ) ) of 
 {{ 
 Require ( ! DStock_Ф_isFullyInitialized ( ) , error_code::cant_override_code ) ; 
 ; 
 Require ( msg_pubkey ( ) == deployer_pubkey_ , error_code::sender_is_not_deployer ) ; 
 ; 
 tvm_accept ( ) ; 
 Require ( ! price_code_ , error_code::cant_override_code ) ; 
 ; 
 price_code_ := ^ Л_code22_ ; 
 
 }} Definition DStock_Ф_isFullyInitialized 
 : SMLExpression (S:=Ledger) false XBool XInteger := 
 {{ 
 ρ return bool_t ( pair_code_ && price_code_ ) ; 
 
 }} Definition DStock_Ф_getTonsCfg 
 : SMLExpression (S:=Ledger) false TonsConfigP XInteger := 
 {{ 
 ρ return ^ tons_cfg_ ; 
 ; 
 
 }} Definition DStock_Ф_getTradingPairCode 
 : SMLExpression (S:=Ledger) false XCell XInteger := 
 {{ 
 ρ return ^ *pair_code_ ; 
 ; 
 
 }} Parameter Л_tip3_addr26 : XString . 
 
 Definition DStock_Ф_isFullyInitialized 
 : SMLExpression (S:=Ledger) false XBool XInteger := 
 {{ 
 ρ return bool_t ( pair_code_ && price_code_ ) ; 
 
 }} Definition DStock_Ф_getTonsCfg 
 : SMLExpression (S:=Ledger) false TonsConfigP XInteger := 
 {{ 
 ρ return ^ tons_cfg_ ; 
 ; 
 
 }} Definition DStock_Ф_getTradingPairCode 
 : SMLExpression (S:=Ledger) false XCell XInteger := 
 {{ 
 ρ return ^ *pair_code_ ; 
 ; 
 
 }} Parameter Л_tip3_addr26 : XString . 
 
 Definition DStock_Ф_getTonsCfg 
 : SMLExpression (S:=Ledger) false TonsConfigP XInteger := 
 {{ 
 ρ return ^ tons_cfg_ ; 
 ; 
 
 }} Definition DStock_Ф_getTradingPairCode 
 : SMLExpression (S:=Ledger) false XCell XInteger := 
 {{ 
 ρ return ^ *pair_code_ ; 
 ; 
 
 }} Parameter Л_tip3_addr26 : XString . 
 
 Definition DStock_Ф_getTradingPairCode 
 : SMLExpression (S:=Ledger) false XCell XInteger := 
 {{ 
 ρ return ^ *pair_code_ ; 
 ; 
 
 }} Parameter Л_tip3_addr26 : XString . 
 
 Definition DStock_Ф_getSellPriceCode ( tip3_addr : XAddress ) 
 : SMLExpression (S:=Ledger) false XCell XInteger := 
 WeakBinding ( ResultExpression ( init addr Л_tip3_addr26 := tip3_addr ) ) of 
 {{ 
 Require ( price_code_ - > ctos ( DStock_ι_) ^^ srefs ( ) == 2 , error_code::unexpected_refs_count_in_code ) ; 
 Л_salt26_ := ^ builder ( DStock_ι_) ^^ stslice ( tvm_myaddr ( ) DStock_ι_) ^^ stslice ( Л_tip3_addr26_ ^^ addr_ι_sl ( ) DStock_ι_) ^^ endc ( ) ; 
 ρ return builder ( DStock_ι_) ^^ stslice ( price_code_ - > ctos ( ) DStock_ι_) ^^ stref ( Л_salt26_ DStock_ι_) ^^ endc ( ) ; 
 ) ) 
 }} Parameter Л_tip3_addr127 : XString . 
 
 Definition DStock_Ф_getXchgPriceCode ( tip3_addr1 : XAddress ) ( tip3_addr2 : XAddress ) 
 : SMLExpression (S:=Ledger) false XCell XInteger := 
 WeakBinding ( ResultExpression ( init addr Л_tip3_addr127 := tip3_addr1 ) ) of 
 WeakBinding ( ResultExpression ( init addr Л_tip3_addr227 := tip3_addr2 ) ) of 
 {{ 
 Require ( price_code_ - > ctos ( DStock_ι_) ^^ srefs ( ) == 3 , error_code::unexpected_refs_count_in_code ) ; 
 Л_keys27_ := ^ std::make_tuple ( tip3_addr1 , tip3_addr2 ) ; 
 ρ return builder ( DStock_ι_) ^^ stslice ( price_code_ - > ctos ( ) DStock_ι_) ^^ stref ( build ( Л_keys27_ DStock_ι_) ^^ endc ( ) DStock_ι_) ^^ endc ( ) ; 
 ) ) 
 }} Parameter Л_tip3_root28 : XString . 
 
 Definition DStock_Ф_getSellTradingPair ( tip3_root : XAddress ) 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 WeakBinding ( ResultExpression ( init addr Л_tip3_root28 := tip3_root ) ) of 
 {{ 
 Л_myaddr28_ { tvm_myaddr ( ) } ; 
 Л_pair_data28_ { . 
 
 Definition DStock_Ф_getMinAmount 
 : SMLExpression (S:=Ledger) false XInteger128 XInteger := 
 {{ 
 ρ return ^ min_amount_ ; 
 ; 
 
 }} Definition DStock_Ф_getDealsLimit 
 : SMLExpression (S:=Ledger) false XInteger8 XInteger := 
 {{ 
 ρ return ^ deals_limit_ ; 
 ; 
 
 }} Definition DStock_Ф_getNotifyAddr 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ notify_addr_ ; 
 ; 
 
 }} Parameter Л_msg32 : XString . 
 
 Definition DStock_Ф_getDealsLimit 
 : SMLExpression (S:=Ledger) false XInteger8 XInteger := 
 {{ 
 ρ return ^ deals_limit_ ; 
 ; 
 
 }} Definition DStock_Ф_getNotifyAddr 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ notify_addr_ ; 
 ; 
 
 }} Parameter Л_msg32 : XString . 
 
 Definition DStock_Ф_getNotifyAddr 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ notify_addr_ ; 
 ; 
 
 }} Parameter Л_msg32 : XString . 
 
 Definition DStock_Ф__fallback ( msg : XCell ) ( msg_body : XSlice ) 
 : SMLExpression (S:=Ledger) false XInteger XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_msg32 := msg ) ) of 
 WeakBinding ( ResultExpression ( init slice Л_msg_body32 := msg_body ) ) of 
 {{ 
 ρ return ^ 0 ; 
 ; 
 
 }} Definition DTradingPair_Ф_onDeploy 
 : SMLExpression (S:=Ledger) false XBool XInteger := 
 {{ 
 Require ( int_value ( DTradingPair_ι_) ^^ get ( ) > deploy_value_ , error_code::not_enough_tons ) ; 
 tvm_rawreserve ( DTradingPair_ι_deploy_value_ ^^ get ( ) , rawreserve_flag::up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 ρ return ^ bool_t { { true } ; 
 ) ; 
 
 }} Definition DTradingPair_Ф_getStockAddr 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ stock_addr_ ; 
 ; 
 
 }} Definition DTradingPair_Ф_getTip3Root 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ tip3_root_ ; 
 ; 
 
 }} Parameter Л_msg36 : XString . 
 
 Definition DTradingPair_Ф_onDeploy 
 : SMLExpression (S:=Ledger) false XBool XInteger := 
 {{ 
 Require ( int_value ( DTradingPair_ι_) ^^ get ( ) > deploy_value_ , error_code::not_enough_tons ) ; 
 tvm_rawreserve ( DTradingPair_ι_deploy_value_ ^^ get ( ) , rawreserve_flag::up_to ) ; 
 set_int_return_flag ( SEND_ALL_GAS ) ; 
 ρ return ^ bool_t { { true } ; 
 ) ; 
 
 }} Definition DTradingPair_Ф_getStockAddr 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ stock_addr_ ; 
 ; 
 
 }} Definition DTradingPair_Ф_getTip3Root 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ tip3_root_ ; 
 ; 
 
 }} Parameter Л_msg36 : XString . 
 
 Definition DTradingPair_Ф_getStockAddr 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ stock_addr_ ; 
 ; 
 
 }} Definition DTradingPair_Ф_getTip3Root 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ tip3_root_ ; 
 ; 
 
 }} Parameter Л_msg36 : XString . 
 
 Definition DTradingPair_Ф_getTip3Root 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 {{ 
 ρ return ^ tip3_root_ ; 
 ; 
 
 }} Parameter Л_msg36 : XString . 
 
 Definition DTradingPair_Ф__fallback ( msg : XCell ) ( msg_body : XSlice ) 
 : SMLExpression (S:=Ledger) false XInteger XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_msg36 := msg ) ) of 
 WeakBinding ( ResultExpression ( init slice Л_msg_body36 := msg_body ) ) of 
 {{ 
 ρ return ^ 0 ; 
 ; 
 
 }} Parameter Л_pubkey37 : XString . 
 
 Definition DFLeXClient_Ф_constructor ( pubkey : XInteger256 ) ( trading_pair_code : XCell ) 
 : SMLExpression (S:=Ledger) false True XInteger := 
 WeakBinding ( ResultExpression ( init int Л_pubkey37 := pubkey ) ) of 
 WeakBinding ( ResultExpression ( init cell Л_trading_pair_code37 := trading_pair_code ) ) of 
 {{ 
 owner_ := ^ Л_pubkey37_ ; 
 trading_pair_code_ := ^ Л_trading_pair_code37_ ; 
 workchain_id_ := ^ std::get < addr_std > ( address { tvm_myaddr ( ) } . 
 
 Definition DFLeXClient_Ф_setStockCfg ( tons_cfg : TonsConfigP ) ( stock : XAddress ) ( notify_addr : XAddress ) 
 : SMLExpression (S:=Ledger) false True XInteger := 
 WeakBinding ( ResultExpression ( init TonsConfigP Л_tons_cfg38 := tons_cfg ) ) of 
 WeakBinding ( ResultExpression ( init addr Л_stock38 := stock ) ) of 
 WeakBinding ( ResultExpression ( init addr Л_notify_addr38 := notify_addr ) ) of 
 {{ 
 Require ( msg_pubkey ( ) == owner_ , error_code::message_sender_is_not_my_owner ) ; 
 ; 
 tvm_accept ( ) ; 
 tons_cfg_ := ^ Л_tons_cfg38_ ; 
 notify_addr_ := ^ Л_notify_addr38_ ; 
 
 }} Parameter Л_stock_addr39 : XString . 
 
 Definition DFLeXClient_Ф_deployTradingPair ( stock_addr : XAddress ) ( tip3_root : XAddress ) ( deploy_min_value : XInteger128 ) ( deploy_value : XInteger128 ) 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 WeakBinding ( ResultExpression ( init addr Л_stock_addr39 := stock_addr ) ) of 
 WeakBinding ( ResultExpression ( init addr Л_tip3_root39 := tip3_root ) ) of 
 WeakBinding ( ResultExpression ( init int Л_deploy_min_value39 := deploy_min_value ) ) of 
 WeakBinding ( ResultExpression ( init int Л_deploy_value39 := deploy_value ) ) of 
 {{ 
 Require ( msg_pubkey ( ) == owner_ , error_code::message_sender_is_not_my_owner ) ; 
 ; 
 tvm_accept ( ) ; 
 Л_pair_data39_ { . 
 
 Definition DFLeXClient_Ф_deployPriceWithSell ( args_cl : XCell ) 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_args_cl40 := args_cl ) ) of 
 {{ 
 Require ( msg_pubkey ( ) == owner_ , error_code::message_sender_is_not_my_owner ) ; 
 ; 
 tvm_accept ( ) ; 
 Л_args40_ := ^ parse < FLeXSellArgs > ( Л_args_cl40_ ^^ cell_ι_ctos ( ) ) ; 
 [ Л_state_init40_ Л_addr40_ Л_std_addr40_ ] := ^ DFLeXClient_Ф_preparePrice ( Л_args40_ ^^ price , Л_args40_ ^^ min_amount , Л_args40_ ^^ deals_limit , Л_args40_ ^^ tip3cfg ( ) , Л_args40_ ^^ price_code ) ; 
 Л_price_addr40_ := ^ IPricePtr ( Л_addr40_ ) ; 
 Л_deploy_init_cl40_ := ^ build ( Л_state_init40_ DFLeXClient_ι_) ^^ endc ( ) ; 
 Л_sell_args40_ := ^ { . 
 
 Definition DFLeXClient_Ф_deployPriceWithBuy ( args_cl : XCell ) 
 : SMLExpression (S:=Ledger) false XAddress XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_args_cl41 := args_cl ) ) of 
 {{ 
 Require ( msg_pubkey ( ) == owner_ , error_code::message_sender_is_not_my_owner ) ; 
 ; 
 tvm_accept ( ) ; 
 Л_args41_ := ^ parse < FLeXBuyArgs > ( Л_args_cl41_ ^^ cell_ι_ctos ( ) ) ; 
 [ Л_state_init41_ Л_addr41_ Л_std_addr41_ ] := ^ DFLeXClient_Ф_preparePrice ( Л_args41_ ^^ price , Л_args41_ ^^ min_amount , Л_args41_ ^^ deals_limit , Л_args41_ ^^ tip3cfg ( ) , Л_args41_ ^^ price_code ) ; 
 IPricePtr price_addr ( Л_addr41_ ) ; 
 DFLeXClient_ι_price_addr ^^ deploy ( Л_state_init41_ , Grams ( Л_args41_ ^^ deploy_value . 
 
 Definition DFLeXClient_Ф_cancelSellOrder ( args_cl : XCell ) 
 : SMLExpression (S:=Ledger) false True XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_args_cl42 := args_cl ) ) of 
 {{ 
 Require ( msg_pubkey ( ) == owner_ , error_code::message_sender_is_not_my_owner ) ; 
 ; 
 tvm_accept ( ) ; 
 Л_args42_ := ^ parse < FLeXCancelArgs > ( Л_args_cl42_ ^^ cell_ι_ctos ( ) ) ; 
 [ Л_state_init42_ Л_addr42_ Л_std_addr42_ ] := ^ DFLeXClient_Ф_preparePrice ( Л_args42_ ^^ price , Л_args42_ ^^ min_amount , Л_args42_ ^^ deals_limit , Л_args42_ ^^ tip3cfg ( ) , Л_args42_ ^^ price_code ) ; 
 IPricePtr price_addr ( Л_addr42_ ) ; 
 price_addr ( Grams ( Л_args42_ ^^ value . 
 
 Definition DFLeXClient_Ф_cancelBuyOrder ( args_cl : XCell ) 
 : SMLExpression (S:=Ledger) false True XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_args_cl43 := args_cl ) ) of 
 {{ 
 Require ( msg_pubkey ( ) == owner_ , error_code::message_sender_is_not_my_owner ) ; 
 ; 
 tvm_accept ( ) ; 
 Л_args43_ := ^ parse < FLeXCancelArgs > ( Л_args_cl43_ ^^ cell_ι_ctos ( ) ) ; 
 [ Л_state_init43_ Л_addr43_ Л_std_addr43_ ] := ^ DFLeXClient_Ф_preparePrice ( Л_args43_ ^^ price , Л_args43_ ^^ min_amount , Л_args43_ ^^ deals_limit , Л_args43_ ^^ tip3cfg ( ) , Л_args43_ ^^ price_code ) ; 
 IPricePtr price_addr ( Л_addr43_ ) ; 
 price_addr ( Grams ( Л_args43_ ^^ value . 
 
 Definition DFLeXClient_Ф_getOwner 
 : SMLExpression (S:=Ledger) false XInteger256 XInteger := 
 {{ 
 ρ return ^ owner_ ; 
 ; 
 
 }} Parameter Л_msg45 : XString . 
 
 Definition DFLeXClient_Ф__fallback ( msg : XCell ) ( msg_body : XSlice ) 
 : SMLExpression (S:=Ledger) false XInteger XInteger := 
 WeakBinding ( ResultExpression ( init cell Л_msg45 := msg ) ) of 
 WeakBinding ( ResultExpression ( init slice Л_msg_body45 := msg_body ) ) of 
 {{ 
 ρ return ^ 0 ; 
 ; 
 
 }} Parameter Л_price46 : XString . 
 
 Definition DFLeXClient_Ф_preparePrice ( price : XInteger128 ) ( min_amount : XInteger128 ) ( deals_limit : XInteger8 ) ( tip3cfg : Tip3ConfigP ) ( price_code : XCell ) 
 : SMLExpression (S:=Ledger) false ( StateInitP # XAddress # XInteger256 ) XInteger := 
 WeakBinding ( ResultExpression ( init int Л_price46 := price ) ) of 
 WeakBinding ( ResultExpression ( init int Л_min_amount46 := min_amount ) ) of 
 WeakBinding ( ResultExpression ( init int Л_deals_limit46 := deals_limit ) ) of 
 WeakBinding ( ResultExpression ( init Tip3ConfigP Л_tip3cfg46 := tip3cfg ) ) of 
 WeakBinding ( ResultExpression ( init cell Л_price_code46 := price_code ) ) of 
 {{ 
 Л_price_data46_ { . 
 
 Definition Ф_prepare_price_state_init_and_addr ( price_data : DPriceP ) ( price_code : XCell ) 
 : SMLExpression (S:=Ledger) false ( StateInitP # XInteger256 ) XInteger := 
 WeakBinding ( ResultExpression ( init DPriceP Л_price_data100 := price_data ) ) of 
 WeakBinding ( ResultExpression ( init cell Л_price_code100 := price_code ) ) of 
 {{ 
 Л_price_data_cl100_ := ^ prepare_persistent_data < IPrice , void , DPrice > ( { } , Л_price_data100_ ) ; 
 Л_price_init100_ { { } , { } , Л_price_code100_ , price_data_cl , { } } ; 
 Л_price_init_cl100_ := ^ build ( Л_price_init100_ _ι_) ^^ make_cell ( ) ; 
 ρ return [ Л_price_init100_ , uint256 ( tvm_hash ( Л_price_init_cl100_ ) ) ] 
 }} Parameter Л_pair_data101 : XString . 
 
 Definition Ф_prepare_trading_pair_state_init_and_addr ( pair_data : DTradingPairP ) ( pair_code : XCell ) 
 : SMLExpression (S:=Ledger) false ( StateInitP # XInteger256 ) XInteger := 
 WeakBinding ( ResultExpression ( init DTradingPairP Л_pair_data101 := pair_data ) ) of 
 WeakBinding ( ResultExpression ( init cell Л_pair_code101 := pair_code ) ) of 
 {{ 
 Л_pair_data_cl101_ := ^ prepare_persistent_data < ITradingPair , void , DTradingPair > ( { } , Л_pair_data101_ ) ; 
 Л_pair_init101_ { { } , { } , Л_pair_code101_ , pair_data_cl , { } } ; 
 Л_pair_init_cl101_ := ^ build ( Л_pair_init101_ _ι_) ^^ make_cell ( ) ; 
 ρ return [ Л_pair_init101_ , uint256 ( tvm_hash ( Л_pair_init_cl101_ ) ) ] 
 }} Parameter Л_amount102 : XString . 
 
 Definition Ф_calc_cost ( amount : XInteger128 ) ( price : XInteger128 ) 
 : SMLExpression (S:=Ledger) false ( XMaybe XInteger128 ) XInteger := 
 WeakBinding ( ResultExpression ( init int Л_amount102 := amount ) ) of 
 WeakBinding ( ResultExpression ( init int Л_price102 := price ) ) of 
 {{ 
 Л_tons_cost102_ := ^ Л_amount102_ ^^ int_ι_get ( ) * Л_price102_ ^^ int_ι_get ( ) ; 
 if ^ ( Л_tons_cost102_ > > 128 ) then { ρ return [ ] 
 }} Parameter Л_tip3root103 : XString . 
 
 Definition Ф_process_queue_impl ( tip3root : XAddress ) ( notify_addr : IStockNotifyPtrP ) ( price : XInteger128 ) ( deals_limit : XInteger8 ) ( tons_cfg : TonsConfigP ) ( sell_idx : XInteger ) ( buy_idx : XInteger ) ( sells_amount : XInteger128 ) ( sells : ( XQueue SellInfoP ) ) ( buys_amount : XInteger128 ) ( buys : ( XQueue BuyInfoP ) ) 
 : SMLExpression (S:=Ledger) false process_retP XInteger := 
 WeakBinding ( ResultExpression ( init addr Л_tip3root103 := tip3root ) ) of 
 WeakBinding ( ResultExpression ( init IStockNotifyPtrP Л_notify_addr103 := notify_addr ) ) of 
 WeakBinding ( ResultExpression ( init int Л_price103 := price ) ) of 
 WeakBinding ( ResultExpression ( init int Л_deals_limit103 := deals_limit ) ) of 
 WeakBinding ( ResultExpression ( init TonsConfigP Л_tons_cfg103 := tons_cfg ) ) of 
 WeakBinding ( ResultExpression ( init int Л_sell_idx103 := sell_idx ) ) of 
 WeakBinding ( ResultExpression ( init int Л_buy_idx103 := buy_idx ) ) of 
 WeakBinding ( ResultExpression ( init int Л_sells_amount103 := sells_amount ) ) of 
 WeakBinding ( ResultExpression ( init int Л_buys_amount103 := buys_amount ) ) of 
 {{ 
 Л_d103_ { Л_tip3root103_ , Л_notify_addr103_ , Л_price103_ , Л_deals_limit103_ ^^ int_ι_get ( ) , Л_tons_cfg103_ , Л_sells_amount103_ , sells , Л_buys_amount103_ , buys , { } } ; 
 Л_d103_ ^^ dealer_ι_process_queue ( Л_sell_idx103_ , Л_buy_idx103_ ) ; 
 ρ return [ Л_d103_ ^^ dealer_ι_sells_amount_ , Л_d103_ ^^ dealer_ι_sells_ , Л_d103_ ^^ dealer_ι_buys_amount_ , Л_d103_ ^^ dealer_ι_buys_ , Л_d103_ ^^ dealer_ι_ret_ ] 
 }} . 
 