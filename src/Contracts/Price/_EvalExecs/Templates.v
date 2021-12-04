Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Setoid.
Require Import ZArith.
Require Import Coq.Program.Equality.

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
Require Import FinProof.StateMonad21.
Require Import FinProof.EpsilonMonad.
Require Import FinProof.StateMonad21Instances.
Require Import FinProof.MonadTransformers21.


Require Import UMLang.UrsusLib.
Require Import UMLang.ProofEnvironment2.
(* Require Import UMLang.ExecGenerator.
 *)
Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.
Require Import Project.CommonNotations.
Require Import Project.CommonAxioms.
(*Fully qualified name are mandatory in multi-contract environment*)
Require Import Contracts.Price.Ledger.
Require Import Contracts.Price.Functions.FuncSig.
Require Import Contracts.Price.Functions.FuncNotations.
Require Import Contracts.TONTokenWallet.ClassTypesNotations.
Require Import Contracts.Flex.ClassTypesNotations.
Require Import Contracts.Price.Functions.Funcs.
Require Contracts.Price.Interface.

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.


Module PriceTemplate (co: CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .


Module Export FuncsModule := Funcs co dc.

Import FuncsInternal.

Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module Import TONTokenWalletModuleForPrice := Contracts.TONTokenWallet.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.
Module TONTokenWalletClassTypesModule := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .

Module Import FlexModuleForPrice := Contracts.Flex.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig.


(* Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Export SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module Import TONTonkenWalletModuleForPrice := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule .
(* Export SpecModuleForFuncNotations(* ForFuncs *).CommonNotationsModule. *)
 *)
(*   Module Import xxx := SpecModuleForFuncNotations.LedgerModuleForFuncSig.

Module Import generator := execGenerator XTypesModule StateMonadModule xxx.
 *) 
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.


(*move somewhere*)
Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.

(***************************************************************************)		
(* 
Compute default : LocalStateLRecord.

 *)
Definition LocalStateDefault := (Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil))),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)))),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil))),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil),
(Datatypes.nil, Datatypes.nil, (Datatypes.nil, Datatypes.nil)))))%xprod
: LocalStateLRecord.

Opaque LocalStateDefault.

(* Import URSUS.
Import FuncsModule.TONTonkenWalletModuleForPrice.CommonTypes.BasicTypesModule.
Import FuncsModule.TONTonkenWalletModuleForPrice.CommonTypes.
 *) (* Import URSUS_. *)
(* 
 Import FuncsModule.FlexModuleForPrice.CommonAxiomsModule.CommonNotationsModule.tvmNotationsModule.tvmFuncModule.stdFuncNotationsModule.stdUFuncModule.stdNotationsModule.stdFuncModule.stdErrorsModule.stdTypesNotationsModule.URSUS.
 Import FuncsModule.FlexModuleForPrice.CommonAxiomsModule.CommonNotationsModule.tvmNotationsModule.tvmFuncModule.stdFuncNotationsModule.stdUFuncModule.stdNotationsModule.stdFuncModule.
 Import FuncsModule.FuncNotationsModuleForFunc.SpecModuleForFuncNotations.ClassTypesNotationsModule.
 Import FuncsModule.FlexModuleForPrice.CommonAxiomsModule.CommonNotationsModule.tvmNotationsModule.tvmFuncModule.stdFuncNotationsModule.stdUFuncModule.stdNotationsModule.stdFuncModule.stdErrorsModule.stdTypesNotationsModule.URSUS.
 Import FuncsModule.FlexModuleForPrice.CommonAxiomsModule.CommonNotationsModule.tvmNotationsModule.tvmFuncModule.stdFuncNotationsModule.stdUFuncModule.stdNotationsModule.stdFuncModule.
 Import FuncsModule.FlexModuleForPrice.CommonAxiomsModule.CommonNotationsModule.tvmNotationsModule.tvmFuncModule.stdFuncNotationsModule.
 Import FuncsModule.FlexModuleForPrice.CommonAxiomsModule.CommonNotationsModule.
 Import FlexModuleForPrice.CommonAxiomsModule.CommonNotationsModule.tvmNotationsModule.tvmFuncModule.stdFuncNotationsModule.stdUFuncModule.stdNotationsModule.stdFuncModule.stdErrorsModule.stdTypesNotationsModule.URSUS.
 Import LedgerModuleForFuncSig.TypesModuleForLedger.
 Import URSUS. *)
 Existing Instance LedgerPruvendoRecord.
 




 
 Section make_deal.
 Variable this : ULValue dealerLRecord.
Context
(d_a : ULValue OrderInfoLRecord -> ULValue OrderInfoLRecord -> URValue uint false)
(s_o_t : ULValue OrderInfoLRecord ->  ULValue uint128 -> URValue boolean false )
(b_o_t : ULValue OrderInfoLRecord ->  ULValue uint128 -> URValue boolean false )
(l_t_s : ULValue uint -> ULValue OrderInfoLRecord -> URValue boolean false)
(b_c :  ULValue (optional uint) -> URValue uint128 true)
(f0  : ULValue OrderInfoLRecord -> ULValue OrderInfoLRecord -> ULValue uint -> UExpression ( boolean # (boolean # uint128) ) false )
(b0 : ULValue boolean -> ULValue boolean -> URValue boolean false)
( cc : ULValue uint -> ULValue dealerLRecord -> URValue (optional uint) true )
(f01 : ULValue uint128 -> ULValue dealerLRecord -> UExpression ( boolean # (boolean # uint128) ) false)
(f02 : ULValue uint128 -> ULValue dealerLRecord -> UExpression ( boolean # (boolean # uint128) ) false)
(f1 : ULValue boolean -> ULValue boolean -> UExpression ( boolean # (boolean # uint128) ) true )
(f2 : ULValue OrderInfoLRecord ->
ULValue OrderInfoLRecord ->
ULValue uint128 -> ULValue uint128 -> UExpression ( boolean # (boolean # uint128) ) false )
( f3 : ULValue OrderInfoLRecord ->
 ULValue (optional uint) -> UExpression ( boolean # (boolean # uint128) ) true )
(f4 : ULValue dealerLRecord ->
ULValue OrderInfoLRecord ->
ULValue OrderInfoLRecord ->
ULValue uint -> ULValue (optional uint) -> UExpression ( boolean # (boolean # uint128) ) true )
(f41 : ULValue dealerLRecord -> ULValue uint -> UExpression ( boolean # (boolean # uint128) ) false)
(f42 :  ULValue uint -> UExpression ( boolean # (boolean # uint128) ) false).
 Definition make_deal_template (* (this : ULValue dealerLRecord) *) ( sell : ULValue OrderInfoLRecord ) ( buy : ULValue OrderInfoLRecord ) : UExpression ( boolean # (boolean # uint128) ) true .
 refine {{ new 'deal_amount : uint @ "deal_amount" := (* min ( !{sell} ↑ OrderInfo.amount , !{buy} ↑ OrderInfo.amount ) *) { d_a sell buy } ; { _ } }} . 
 refine {{ new 'last_tip3_sell : boolean @ "last_tip3_sell" := (* !{deal_amount} ==  !{sell} ↑ OrderInfo.amount *) { l_t_s deal_amount sell} ; { _ } }} .
 refine {{ { f0 sell buy deal_amount : UEf } ; { _ }  }}.
 refine {{ new 'cost : optional uint @ "cost" :=  (* calc_cost_ ( !{deal_amount} , !{this} ↑ dealer.price_ ) *) { cc deal_amount this}  ; { _ } }} .
 refine {{ new 'sell_costs : uint128 @ "sell_costs" := 0 ; { _ } }} . 
 refine {{ new 'buy_costs : uint128 @ "buy_costs" :=  (* ( !{cost} ) -> get () *)  { b_c cost } ; { _ } }} . 
 refine {{ if ( !{last_tip3_sell} ) then { { _:UEf } } 
 else { { _:UEf } } ; { _ } }} . 
 refine {{ { f01  sell_costs  this }   }}.
 refine {{ { f02  sell_costs  this }   }}.
(*  refine {{ {sell_costs} += ( (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) + (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ) }} .
 refine {{ {buy_costs} += ( (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) + (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ) }} . 
 *) refine {{ new 'sell_out_of_tons : boolean @ "sell_out_of_tons" :=  (* !{sell} ↑ OrderInfo.account < !{sell_costs} *) { s_o_t sell sell_costs } ; { _ } }} . 
 refine {{ new 'buy_out_of_tons : boolean @ "buy_out_of_tons" := (* !{buy} ↑ OrderInfo.account < !{buy_costs} *) { b_o_t buy buy_costs } ; { _ } }} . 
 refine {{ if ( (* !{sell_out_of_tons} \\ !{buy_out_of_tons} *) {b0 sell_out_of_tons buy_out_of_tons} ) then { { _ :UEt } } ; { _ } }} . 
 refine {{ { f1 sell_out_of_tons buy_out_of_tons}  }}.
 refine {{ { f2 sell buy sell_costs buy_costs   } ; { _ }  }}.
 refine {{ {f4 this sell buy deal_amount cost  } }}.
(*  refine ( let sell_ptr := {{ ITONTokenWalletPtr [[ (!{sell} ↑ OrderInfo.tip3_wallet)  ]] }} in 
 {{ {sell_ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) ⇒ { Messsage_ι_value }  $] 
                            ⤳ .transfer ( !{sell} ↑ OrderInfo.tip3_wallet , !{buy} ↑ OrderInfo.tip3_wallet ,
                 !{deal_amount} , 0 , FALSE ) ; {_} }} ).  
refine {{ { f3 sell  cost  } ; { _ } }}.
refine ( let notify_addr__ptr := {{ IFlexNotifyPtr [[ !{this} ↑ dealer.notify_addr_  ]] }} in 
              {{ {notify_addr__ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ⇒ { Messsage_ι_value }  $] 
                                         ⤳ .onDealCompleted ( !{this} ↑ dealer.tip3root_  , !{this} ↑ dealer.price_ ,
										 				 !{deal_amount} ) ; {_} }} ).
refine {{ return_ [ FALSE , FALSE , !{ deal_amount } ] }} . 
 *) Defined .
 


 Definition make_deal ( sell : ULValue OrderInfoLRecord ) ( buy : ULValue OrderInfoLRecord ) : UExpression ( boolean # (boolean # uint128) ) true . 
 refine {{ new 'deal_amount : uint @ "deal_amount" := min ( !{sell} ↑ OrderInfo.amount , !{buy} ↑ OrderInfo.amount ) ; { _ } }} . 
 refine {{ new 'last_tip3_sell : boolean @ "last_tip3_sell" := !{deal_amount} ==  !{sell} ↑ OrderInfo.amount ; { _ } }} .
 refine {{ {sell} ↑ OrderInfo.amount -= !{deal_amount} ; { _ } }} . 
 refine {{ {buy} ↑ OrderInfo.amount -= !{deal_amount} ; { _ } }} . 
 refine {{ new 'cost : optional uint @ "cost" := calc_cost_ ( !{deal_amount} , !{this} ↑ dealer.price_ ) ; { _ } }} .
 refine {{ new 'sell_costs : uint128 @ "sell_costs" := 0 ; { _ } }} . 
 refine {{ new 'buy_costs : uint128 @ "buy_costs" := ( !{cost} ) -> get () ; { _ } }} . 
 refine {{ if ( !{last_tip3_sell} ) then { { _:UEf } } 
                            else { { _:UEf } } ; { _ } }} . 
 refine {{ {sell_costs} += ( (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) + (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ) }} .
 refine {{ {buy_costs} += ( (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) + (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ) }} . 
 refine {{ new 'sell_out_of_tons : boolean @ "sell_out_of_tons" :=  !{sell} ↑ OrderInfo.account < !{sell_costs} ; { _ } }} . 
 refine {{ new 'buy_out_of_tons : boolean @ "buy_out_of_tons" := !{buy} ↑ OrderInfo.account < !{buy_costs} ; { _ } }} . 
 refine {{ if ( !{sell_out_of_tons} \\ !{buy_out_of_tons} ) then { { _ :UEt } } ; { _ } }} . 
 refine {{ exit_ [ !{ sell_out_of_tons } , !{ buy_out_of_tons } , 0 ] }} . 
 refine {{ {sell} ↑ OrderInfo.account -= !{sell_costs} ; { _ } }} . 
 refine {{ {buy}  ↑ OrderInfo.account -= !{buy_costs} ; { _ } }} .

refine ( let sell_ptr := {{ ITONTokenWalletPtr [[ (!{sell} ↑ OrderInfo.tip3_wallet)  ]] }} in 
            {{ {sell_ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) ⇒ { Messsage_ι_value }  $] 
                                       ⤳ .transfer ( !{sell} ↑ OrderInfo.tip3_wallet , !{buy} ↑ OrderInfo.tip3_wallet ,
                                          !{deal_amount} , 0 , FALSE ) ; {_} }} ).  
        refine {{ tvm_transfer ( !{sell} ↑ OrderInfo.client_addr , !{cost} -> get () , TRUE , 
                    SENDER_WANTS_TO_PAY_FEES_SEPARATELY_ ) ; { _ } }} .
refine ( let notify_addr__ptr := {{ IFlexNotifyPtr [[ !{this} ↑ dealer.notify_addr_  ]] }} in 
            {{ {notify_addr__ptr} with [$ (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ⇒ { Messsage_ι_value }  $] 
                                       ⤳ .onDealCompleted ( !{this} ↑ dealer.tip3root_  , !{this} ↑ dealer.price_ ,
                                          !{deal_amount} ) ; {_} }} ).  

 refine {{ return_ [ FALSE , FALSE , !{ deal_amount } ] }} . 
Defined .


 Definition make_deal_template_correct :  forall

 (* (s_o_t : ULValue OrderInfoLRecord ->  ULValue uint128 -> URValue boolean false )
(b_o_t : ULValue OrderInfoLRecord ->  ULValue uint128 -> URValue boolean false ) *)
 (* (this : ULValue dealerLRecord) *) ( sell : ULValue OrderInfoLRecord ) ( buy : ULValue OrderInfoLRecord ),
 ( b_o_t = (fun b bc => ||!{b} ↑ OrderInfo.account < !{bc} ||) ) ->
 ( s_o_t = (fun s sc => ||!{s} ↑ OrderInfo.account < !{sc} ||) ) ->
 (d_a = ( fun s b => || min ( !{s} ↑ OrderInfo.amount , !{b} ↑ OrderInfo.amount ) || )) ->
 (l_t_s = (fun da s => || ( !{da} ==  !{s} ↑ OrderInfo.amount) || )) ->
 (cc = (fun da t => || calc_cost_ ( !{da} , !{t} ↑ dealer.price_ ) || )) ->
 (b_c = (fun c => || ( !{c} ) -> get () ||  )) ->
 (b0 = (fun sot bot => || !{sot} \\ !{bot} || )) ->
   (f0 = (fun s b da => {{ {s} ↑ OrderInfo.amount -= !{da} ; {b} ↑ OrderInfo.amount -= !{da} }} )) -> 
 (f01 = (fun  s t => {{ {s} += ( (!{t} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) + (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ) }})) ->
 (f02 = (fun  b t  => {{ {b} += ( (!{t} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) + (!{this} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ) }})) ->
 (f1 = (fun sot bot => {{ exit_ [ !{ sot } , !{ bot } , 0 ] }})) ->
 (f2 = (fun s b sc bc  => 
  {{ {s} ↑ OrderInfo.account -= !{sc} ;  
     {b} ↑ OrderInfo.account -= !{bc} }})) ->

  (f4 = (fun t s b da c => 
 ( let sell_ptr := {{ ITONTokenWalletPtr [[ (!{s} ↑ OrderInfo.tip3_wallet)  ]] }} in 
 {{ {sell_ptr} with [$ (!{t} ↑ dealer.tons_cfg_ ↑ TonsConfig.transfer_tip3) ⇒ { Messsage_ι_value }  $] 
                            ⤳ .transfer ( !{s} ↑ OrderInfo.tip3_wallet , !{b} ↑ OrderInfo.tip3_wallet ,
                 !{da} , 0 , FALSE ) ;  { f41 t da } ; { f3 s c } }} ) )) ->
 
 (f3 = (fun s c => {{ tvm_transfer ( !{s} ↑ OrderInfo.client_addr , !{c} -> get () , TRUE , 
 SENDER_WANTS_TO_PAY_FEES_SEPARATELY_ )  }} )) ->
 
 (f41 = (fun  t da  => 
 ( let notify_addr__ptr := {{ IFlexNotifyPtr [[ !{t} ↑ dealer.notify_addr_  ]] }} in 
              {{ {notify_addr__ptr} with [$ (!{t} ↑ dealer.tons_cfg_ ↑ TonsConfig.send_notify) ⇒ { Messsage_ι_value }  $] 
                                         ⤳ .onDealCompleted ( !{t} ↑ dealer.tip3root_  , !{t} ↑ dealer.price_ ,
										 				 !{da} ) ; { f42 da } }} )   )) ->
(f42 = (fun da => {{ return_ [ FALSE , FALSE , !{ da } ] }} )) ->
 make_deal (* this *) sell buy =
 make_deal_template (* this *) sell buy.
 Proof.
    intros. 
   unfold make_deal.
   eremember (( || ! {OrderInfo_account_left buy} < ! {_} || )).
   Unshelve.
   all : cycle 1.
   apply H4.
   (* unfold make_deal_template. *)
    (rewrite <- H).
   subst b0.
   subst f0 f01 f02 f1 f2 f4 f3 f41 f42 d_a b_c cc l_t_s.
(*    subst f01.
   subst f02.
      subst f1.
      subst f2.
      subst f4.
      subst f3.
      subst f41.
      subst f42.

      subst d_a.
      subst b_c.
      subst s_o_t.
      subst b_o_t.
      subst cc.
      subst l_t_s. *)
      (* unfold make_deal. *)

  reflexivity.
 Abort.

End make_deal.

Section extract_active_order.
Context 
(f_while : ULValue (optional OrderInfoWithIdx) ->
ULValue (queue OrderInfoLRecord) ->
ULValue uint128 ->
ULValue boolean ->UExpression ( ( optional OrderInfoWithIdx ) # ( ( queue OrderInfoLRecord ) # uint128 ) ) true).
Definition  extract_active_order_template ( cur_order : optional OrderInfoWithIdx ) 
( orders : queue OrderInfoLRecord  ) 
( all_amount : uint128 ) 
( sell : boolean ) : UExpression ( ( optional OrderInfoWithIdx ) # ( ( queue OrderInfoLRecord ) # uint128 ) ) true  .
vararg cur_order "cur_order".
vararg orders "orders".
vararg all_amount "all_amount".
vararg sell "sell".
refine {{ if !{ cur_order } then { { _:UEt  } } ; { _ } }} .
refine {{ exit_ [ !{ cur_order } , !{ orders } , !{ all_amount } ] }} .
refine {{ { f_while  cur_order orders all_amount sell } ; { _ } }}.
refine {{ return_ [ !{cur_order} , !{orders} , !{all_amount} ] }} . 
Defined . 
(* Definition extract_active_order_template_correct :  forall
( cur_order : optional OrderInfoWithIdx ) 
( orders : queue OrderInfoLRecord  ) 
( all_amount : uint128 ) 
( sell : boolean ),
(f_while = (fun co o aa s =>   {{ { extract_active_order_while co o aa s } }} )) ->
 
 extract_active_order cur_order orders all_amount sell =
 extract_active_order_template cur_order orders all_amount sell.
 Proof.
   intros.
   unfold extract_active_order.
   unfold extract_active_order_template.
   subst f_while.
   unfold extract_active_order_while.
   try reflexivity.
 Abort.
 *)End extract_active_order.


End PriceTemplate.


