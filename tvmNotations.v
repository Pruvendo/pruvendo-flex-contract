Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 
Require Import Coq.Logic.FunctionalExtensionality. 
Require Import Coq.Program.Combinators. 
Require Import Coq.Unicode.Utf8. 

Local Open Scope program_scope. 

Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith. 
Require Import FinProof.StateMonad21. 

Local Open Scope record. 

Require Import UMLang.SolidityNotations2. 
(* Require Import UMLang.SML_NG19.  *)

Require Import tip3ContractClass.
(* Require Import tip3ContractClass. 
Require Import tip3ContractConsts.  
Require Import tip3Variables. *)

Module tvmNotations (xt: XTypesSig) (sm: StateMonadSig) .
Module Export LedgerClass := LedgerClass xt sm.

(* Export dc. Export var.  
 *)
Import SMLNotations.

Local Open Scope solidity_scope. 
Local Open Scope sml_scope. 

Set Typeclasses Iterative Deepening. 
Set Typeclasses Depth 10. 

Arguments ControlValue {X E}.
Arguments ControlError {X E}.

About SMLExpression0_Ledgerable.
About SMLExpression_Next_Ledgerable.

Notation "'λ0'" := ( @SMLExpression0_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _) (at level 0).
Notation "'λ1'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default    _ _   _ _ _ _ λ0) (at level 0).
Notation "'λ2'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ1) (at level 0).
Notation "'λ3'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ2) (at level 0).
Notation "'λ4'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ3) (at level 0).
Notation "'λ5'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ4) (at level 0).
Notation "'λ6'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ5) (at level 0).
Notation "'λ7'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ6) (at level 0).
Notation "'λ8'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ7) (at level 0).
Notation "'λ9'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ8) (at level 0).
Notation "'λ10'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ9) (at level 0).
Notation "'λ11'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ10) (at level 0).
Notation "'λ12'" := ( @SMLExpression_Next_Ledgerable Ledger _ LocalState FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 default _ _ _ _ _ _ λ11) (at level 0).

(**************************************************************************************************)

Parameter __builtin_tvm_hashcu : 
            XCell ->  SMLExpression (S:=Ledger) false XInteger XInteger .

Notation " '__builtin_tvm_hashcu_' '(' x ')' " := ( SMLRScalar (sml_call 
  (Ledgerable := λ1)
  (* (T := XCell ->  SMLExpression (S:=Ledger) false XInteger XInteger)*) __builtin_tvm_hashcu x ))  
  (in custom SMLRValue at level 0 , x custom SMLRValue at level 0) : sml_scope.

Notation " '__builtin_tvm_hashcu_' '(' x ')' " := ( ResultExpression (sml_call 
  (Ledgerable := λ1)
  (* (T := XCell ->  SMLExpression (S:=Ledger) false XInteger XInteger) *) __builtin_tvm_hashcu x )) 
  (in custom SMLLValue at level 0 , x custom SMLRValue at level 0) : sml_scope.

(**************************************************************************************************)  
  
Parameter tvm_balance : SMLExpression (S:=Ledger) false XInteger XInteger .


Section functions.

Variables f g : SMLExpression (S:=Ledger) false True XInteger .

Notation " 'f_' " := ( (SMLRScalar (sml_call (Ledgerable := λ0)
 f ))) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'f_' " := ( 
  (ResultExpression (sml_call (Ledgerable := λ0)
  f ))) (in custom SMLLValue at level 0) : sml_scope.  

Notation " 'g_' " := ( (SMLRScalar (sml_call (Ledgerable := λ0)
 g ))) (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'g_' " := ( 
  (ResultExpression (sml_call (Ledgerable := λ0)
  g ))) (in custom SMLLValue at level 0) : sml_scope.  


Definition strict_bind_fg : SMLExpression (S:=Ledger) false True XInteger :=
{{ f_ ; g_ }}.

End functions.


Notation " 'tvm.balance' '()' " := ( 
  (SMLRScalar (sml_call (Ledgerable := λ0)
  (* (T :=  SMLExpression (S:=Ledger) false XInteger XInteger) *) tvm_balance ))) 
  (in custom SMLRValue at level 0) : sml_scope. 

Notation " 'tvm.balance' '()' " := ( 
  (ResultExpression (sml_call (Ledgerable := λ0)
  (* (T :=  SMLExpression (S:=Ledger) false XInteger XInteger) *) tvm_balance ))) 
  (in custom SMLLValue at level 0) : sml_scope.  

(**************************************************************************************************) 

Parameter prepare_persistent_data1 : 
          XInteger -> DTONTokenWallet -> SMLExpression (S:=Ledger) false (XMaybe XCell) XInteger .

Notation " 'prepare_persistent_data1_' '(' a ',' b ')' " := ( 
  (SMLRScalar (sml_call (Ledgerable := λ2)
  (* (T :=  XInteger -> DTONTokenWallet -> SMLExpression (S:=Ledger) false (XMaybe XCell) XInteger) *) prepare_persistent_data1 a b ))) 
  (in custom SMLRValue at level 0,
  a custom SMLRValue at level 0 , 
  b custom SMLRValue at level 0) : sml_scope. 

Notation " 'prepare_persistent_data1_' '(' a ',' b ')' " := ( 
  (ResultExpression (sml_call (Ledgerable := λ2)
  (* (T :=  XInteger -> DTONTokenWallet -> SMLExpression (S:=Ledger) false (XMaybe XCell) XInteger) *) prepare_persistent_data1 a b))) 
  (in custom SMLLValue at level 0,
  a custom SMLRValue at level 0 , 
  b custom SMLRValue at level 0) : sml_scope.

(**************************************************************************************************) 


Parameter prepare_persistent_data2 : 
   XInteger ->  DRootTokenContract -> SMLExpression (S:=Ledger) false (XMaybe XCell) XInteger .

Notation " 'prepare_persistent_data2_' '(' a ',' b ')' " := ( 
  (SMLRScalar (sml_call (Ledgerable := λ2)
  (* (T := XInteger ->  DRootTokenContract -> SMLExpression (S:=Ledger) false (XMaybe XCell) XInteger) *) prepare_persistent_data2 a b ))) 
  (in custom SMLRValue at level 0,
  a custom SMLRValue at level 0 , 
  b custom SMLRValue at level 0) : sml_scope. 

Notation " 'prepare_persistent_data2_' '(' a ',' b ')' " := ( 
  (ResultExpression (sml_call (Ledgerable := λ2)
  (* (T := XInteger ->  DRootTokenContract -> SMLExpression (S:=Ledger) false (XMaybe XCell) XInteger) *) prepare_persistent_data2 a b ))) 
  (in custom SMLLValue at level 0,
  a custom SMLRValue at level 0 , 
  b custom SMLRValue at level 0) : sml_scope.

(**************************************************************************************************)   

Parameter prepare_persistent_data3 : 
   XInteger ->  DAuthWallet -> SMLExpression (S:=Ledger) false (XMaybe XCell) XInteger .

Notation " 'prepare_persistent_data3_' '(' a ',' b ')' " := ( 
  (SMLRScalar (sml_call (Ledgerable := λ2)
  (* (T := XInteger ->  DAuthWallet -> SMLExpression (S:=Ledger) false (XMaybe XCell) XInteger) *) prepare_persistent_data3 a b ))) 
  (in custom SMLRValue at level 0,
  a custom SMLRValue at level 0 , 
  b custom SMLRValue at level 0) : sml_scope. 

Notation " 'prepare_persistent_data3_' '(' a ',' b ')' " := ( 
  (ResultExpression (sml_call (Ledgerable := λ2)
  (* (T := XInteger ->  DAuthWallet -> SMLExpression (S:=Ledger) false (XMaybe XCell) XInteger) *) prepare_persistent_data3 a b ))) 
  (in custom SMLLValue at level 0,
  a custom SMLRValue at level 0 , 
  b custom SMLRValue at level 0) : sml_scope.

(**************************************************************************************************) 


Parameter tvm_hash : XCell -> SMLExpression (S:=Ledger) false XInteger XInteger .

Notation " 'tvm.hash' '(' a ')' " := ( 
  (SMLRScalar (sml_call (Ledgerable := λ1)
  (* (T := XCell -> SMLExpression (S:=Ledger) false XInteger XInteger) *) tvm_hash a  ))) 
  (in custom SMLRValue at level 0,
  a custom SMLRValue at level 0 ) : sml_scope. 

Notation " 'tvm.hash' '(' a ')' " := ( 
  (ResultExpression (sml_call (Ledgerable := λ1)
  (* (T := XCell -> SMLExpression (S:=Ledger) false XInteger XInteger) *) tvm_hash a  ))) 
  (in custom SMLLValue at level 0,
  a custom SMLRValue at level 0 ) : sml_scope. 

(**************************************************************************************************) 

Parameter make_std : XInteger -> XInteger -> SMLExpression (S:=Ledger) false  (XMaybe address) XInteger.

Notation " 'address::make_std' '(' a ',' b ')' " :=  ( 
    (SMLRScalar (sml_call (Ledgerable := λ2)
    (* (T := XInteger -> XInteger -> SMLExpression (S:=Ledger) false  (XMaybe address) XInteger) *) make_std a b ))) 
    (in custom SMLRValue at level 0,
    a custom SMLRValue at level 0 , 
    b custom SMLRValue at level 0) : sml_scope.

Notation " 'address::make_std' '(' a ',' b ')' " :=  ( 
    (ResultExpression (sml_call (Ledgerable := λ2)
    (* (T := XInteger -> XInteger -> SMLExpression (S:=Ledger) false  (XMaybe address) XInteger) *) make_std a b ))) 
    (in custom SMLLValue at level 0,
    a custom SMLRValue at level 0 , 
    b custom SMLRValue at level 0) : sml_scope.      

(**************************************************************************************************) 

Parameter check_owner : SMLExpression (S:=Ledger) false True XInteger .

Notation " 'check_owner_' '()' " := ( 
    (SMLRScalar (sml_call (Ledgerable := λ0)
    (* (T := SMLExpression (S:=Ledger) false True XInteger) *) check_owner ))) 
    (in custom SMLRValue at level 0) : sml_scope.

Notation " 'check_owner_' '()' " := ( 
    (ResultExpression (sml_call (Ledgerable := λ0)
    (* (T := SMLExpression (S:=Ledger) false True XInteger) *) check_owner ))) 
    (in custom SMLLValue at level 0) : sml_scope.    

(**************************************************************************************************) 

Parameter tvm_accept : SMLExpression (S:=Ledger) false True XInteger.

Notation " 'tvm.accept' '()' " := ( 
    (SMLRScalar (sml_call (Ledgerable := λ0)
   (*  (T := SMLExpression (S:=Ledger) false True XInteger) *) tvm_accept ))) 
    (in custom SMLRValue at level 0) : sml_scope.

Notation " 'tvm.accept' '()' " := ( 
    (ResultExpression (sml_call (Ledgerable := λ0)
    (* (T := SMLExpression (S:=Ledger) false True XInteger) *) tvm_accept ))) 
    (in custom SMLLValue at level 0) : sml_scope. 

(**************************************************************************************************) 

Parameter tvm_rawreserve : XInteger ->  XInteger -> SMLExpression (S:=Ledger) false True XInteger .   

Notation " 'tvm.rawreserve' '(' a ',' b ')'  " :=  (SMLRScalar (sml_call (Ledgerable := λ2)
        (* (T := XInteger -> XInteger ->  SMLExpression (S:=Ledger) false  True XInteger) *) tvm_rawreserve a b )) 
        (in custom SMLRValue at level 0 , 
          a custom SMLRValue at level 0 ,
          b custom SMLRValue at level 0  ) : sml_scope.

Notation " 'tvm.rawreserve' '(' a ',' b ')'  " :=  (ResultExpression (sml_call (Ledgerable := λ2)
        (* (T := XInteger -> XInteger ->  SMLExpression (S:=Ledger) false  True XInteger) *) tvm_rawreserve a b )) 
        (in custom SMLLValue at level 0 , 
          a custom SMLRValue at level 0 ,
          b custom SMLRValue at level 0  ) : sml_scope.

(**************************************************************************************************)           

(*TODO*)
Parameter int_value : SMLExpression (S:=Ledger) false XInteger XInteger.

Notation " 'int_value_' '()' " := ( 
    (SMLRScalar (sml_call (Ledgerable := λ0)
    (* (T := SMLExpression (S:=Ledger) false XInteger XInteger) *) int_value ))) 
    (in custom SMLRValue at level 0) : sml_scope.

Notation " 'int_value_' '()' " := ( 
    (ResultExpression (sml_call (Ledgerable := λ0)
   (*  (T := SMLExpression (S:=Ledger) false XInteger XInteger) *) int_value ))) 
    (in custom SMLLValue at level 0) : sml_scope.

(**************************************************************************************************)       

Parameter intMax : XInteger -> XInteger -> SMLExpression (S:=Ledger) false XInteger XInteger. 

Notation " 'std::max' '(' a ',' b ')' " := 
 (SMLRScalar (sml_call (Ledgerable := λ2)
 (* (T := XInteger -> XInteger -> SMLExpression (S:=Ledger) false  XInteger XInteger)   *)
     intMax a b )) (in custom SMLRValue at level 0 , 
              a custom SMLRValue at level 0 ,
              b custom SMLRValue at level 0  ) : sml_scope. 

Notation " 'std::max' '(' a ',' b ')'  " := 
 (ResultExpression (sml_call (Ledgerable := λ2)
 (* (T := XInteger -> XInteger -> SMLExpression (S:=Ledger) false  XInteger XInteger) *)  
     intMax a b )) (in custom SMLLValue at level 0 , 
              a custom SMLRValue at level 0 ,
              b custom SMLRValue at level 0  ) : sml_scope.

(**************************************************************************************************) 

Parameter set_int_return_flag : XInteger -> SMLExpression (S:=Ledger) false True XInteger .

Notation " 'set_int_return_flag_' '(' a ')' " := (SMLRScalar (sml_call (Ledgerable := λ1)
  (* (T := XInteger -> SMLExpression (S:=Ledger) false True XInteger) *) set_int_return_flag a ))
            (in custom SMLRValue at level 0 , 
            a custom SMLRValue at level 0  ) : sml_scope.

Notation " 'set_int_return_flag_' '(' a ')' " := (ResultExpression (sml_call (Ledgerable := λ1)
  (* (T := XInteger -> SMLExpression (S:=Ledger) false True XInteger) *) set_int_return_flag a ))
            (in custom SMLLValue at level 0 , 
            a custom SMLRValue at level 0  ) : sml_scope.             
(**************************************************************************************************) 

(*TODO*)
Parameter tvm_transfer : SMLExpression (S:=Ledger) false True XInteger .

Notation " 'tvm.transfer' '()' " :=  ( 
    (SMLRScalar (sml_call (Ledgerable := λ0)
    (* (T := SMLExpression (S:=Ledger) false True XInteger) *) tvm_transfer ))) 
    (in custom SMLRValue at level 0) : sml_scope.
    
Notation " 'tvm.transfer' '()' " :=  ( 
    (ResultExpression (sml_call (Ledgerable := λ0)
    (* (T := SMLExpression (S:=Ledger) false True XInteger) *) tvm_transfer ))) 
    (in custom SMLLValue at level 0) : sml_scope.

(**************************************************************************************************) 

Parameter tvm_myaddr : SMLExpression (S:=Ledger) false address XInteger .

Notation " 'tvm.myaddr' '()' ":= (SMLRScalar ( sml_call (Ledgerable := λ0)
   (* ( T:= SMLExpression (S:=Ledger)  false address XInteger ) *) tvm_myaddr )) 
   (in custom SMLRValue at level 0 ) : sml_scope.

Notation " 'tvm.myaddr' '()' " := (ResultExpression (sml_call (Ledgerable := λ0)
    (* ( T := SMLExpression ( S:=Ledger ) false address XInteger) *) tvm_myaddr ) ) 
    (in custom SMLLValue at level 0, only parsing ) : sml_scope.  
    
(**************************************************************************************************)     

Parameter toCell: StateInit -> SMLExpression (S:=Ledger) false XCell XInteger  .

Notation " a  '->' 'make_cell' '()' " := (SMLRScalar ( sml_call  (Ledgerable := λ1)
   (* ( T:= StateInit -> SMLExpression (S:=Ledger) false XCell XInteger ) *) toCell a )) 
   (in custom SMLRValue at level 0) : sml_scope.

Notation " a  '->' 'make_cell' '()' " := (ResultExpression ( sml_call  (Ledgerable := λ1)
   (* ( T:= StateInit -> SMLExpression (S:=Ledger) false XCell XInteger ) *) toCell a )) 
   (in custom SMLLValue at level 0, 
   a custom SMLRValue at level 0 ) : sml_scope.

(*Variable s_expr: SMLExpression (S:=Ledger) false StateInit XInteger.

Notation " 's_' " := (s_expr)  (in custom SMLRValue at level 0) .
Notation " 's_' " := (s_expr)  (in custom SMLLValue at level 0) .

Check | s_ -> make_cell () |.
Check {{ s_ -> make_cell () }}. *)

(**************************************************************************************************)     

Parameter parse_continue : XSlice -> SMLExpression (S:=Ledger) false ( XSlice # XSlice ) XInteger .

Notation " 'parse_continue<abiv1::internal_msg_header>' '(' a ')' " := (SMLRScalar ( sml_call  (Ledgerable := λ1)
   (* ( T:= XSlice -> SMLExpression (S:=Ledger) false  ( XSlice # XSlice ) XInteger ) *) parse_continue a )) 
   (in custom SMLRValue at level 0) : sml_scope.

Notation " 'parse_continue<abiv1::internal_msg_header>' '(' a ')' " := (ResultExpression ( sml_call (Ledgerable := λ1) 
   (* ( T:= XSlice -> SMLExpression (S:=Ledger) false  ( XSlice # XSlice ) XInteger ) *) parse_continue a )) 
   (in custom SMLLValue at level 0, 
   a custom SMLRValue at level 0 ) : sml_scope.

(**************************************************************************************************)                         
Parameter int_sender : SMLExpression (S:=Ledger) false address XInteger .

Notation " 'int_sender_' '()' " := (SMLRScalar ( sml_call (Ledgerable := λ0)
(* ( T:= SMLExpression (S:=Ledger)  false address XInteger ) *) int_sender )) 
(in custom SMLRValue at level 0 ) : sml_scope.

Notation " 'int_sender_' '()' " := (ResultExpression ( sml_call (Ledgerable := λ0)
(* ( T:= SMLExpression (S:=Ledger)  false address XInteger ) *) int_sender )) 
(in custom SMLLValue at level 0 ) : sml_scope.

(**************************************************************************************************)

Parameter tvm_pubkey : SMLExpression (S:=Ledger) false XInteger256 XInteger .

Notation " 'tvm.pubkey' '()' " :=  (SMLRScalar ( sml_call (Ledgerable := λ0)
(* ( T:= SMLExpression (S:=Ledger)  false XInteger256 XInteger ) *) tvm_pubkey )) 
(in custom SMLRValue at level 0 ) : sml_scope.

Notation " 'tvm.pubkey' '()' " :=  (ResultExpression ( sml_call (Ledgerable := λ0)
(* ( T:= SMLExpression (S:=Ledger)  false XInteger256 XInteger ) *) tvm_pubkey )) 
(in custom SMLLValue at level 0 ) : sml_scope.

(**************************************************************************************************)

Parameter wallet_replay_protection_t_init : SMLExpression (S:=Ledger) false XInteger XInteger .

Notation " 'wallet_replay_protection_t::init' '()' " := 
  (SMLRScalar ( sml_call (Ledgerable := λ0)
  (* ( T:= SMLExpression (S:=Ledger)  false XInteger256 XInteger ) *) wallet_replay_protection_t_init )) 
  (in custom SMLRValue at level 0 ) : sml_scope.

Notation " 'wallet_replay_protection_t::init' '()'" :=  
  (ResultExpression ( sml_call (Ledgerable := λ0)
  (* ( T:= SMLExpression (S:=Ledger)  false XInteger256 XInteger ) *) wallet_replay_protection_t_init )) 
  (in custom SMLLValue at level 0 ) : sml_scope.


(**************************************************************************************************)

Parameter root_replay_protection_t_init : SMLExpression (S:=Ledger) false XInteger XInteger .

Notation " 'root_replay_protection_t::init' '()' " := 
  (SMLRScalar ( sml_call (Ledgerable := λ0)
  (* ( T:= SMLExpression (S:=Ledger)  false XInteger256 XInteger ) *) root_replay_protection_t_init )) 
  (in custom SMLRValue at level 0 ) : sml_scope.

Notation " 'wallet_replay_protection_t::init' '()'" :=  
  (ResultExpression ( sml_call (Ledgerable := λ0)
  (* ( T:= SMLExpression (S:=Ledger)  false XInteger256 XInteger ) *) root_replay_protection_t_init )) 
  (in custom SMLLValue at level 0 ) : sml_scope.

(**************************************************************************************************)

Notation "'RL'" := (SMLRValue (S:=Ledger)).


(*TODO*)
Parameter _contains: forall {X Y: Type} (x:RL X ) (y:RL Y), RL XBool
(*  :=  {{ ρ return TRUE_ }} *) .
Notation " x '->contains' y " := ( _contains x y )
                 (in custom SMLRValue at level 0, y custom SMLRValue at level 0) : sml_scope.

Parameter _erase: forall {X Y} (x:RL X )(y:RL Y ), RL True (* := 
  {{ ρ return I }} *).

Notation " x '->erase' y " := ( _erase x y ) 
                 (in custom SMLRValue at level 0, y custom SMLRValue at level 0) : sml_scope.

Parameter _insert: forall {X Y}(x:RL X )(y:RL Y), RL True  (* := 
  {{ ρ return I }} *).

Notation " x '->insert' y " := ( _insert x y ) 
                 (in custom SMLRValue at level 0, y custom SMLRValue at level 0) : sml_scope.

Parameter _size: forall {X}(x:RL X), RL XInteger (* := 
  {{ ρ return 1 }} *).

Notation " x '->size' " := (  _size x ) 
                 (in custom SMLRValue at level 0) : sml_scope.

Parameter _hasValue: forall {X }(x:RL X ), RL XBool (* := 
  {{ ρ return TRUE_ }} *).
Notation " x '->has_value' " := ( _hasValue x ) 
                 (in custom SMLRValue at level 0 ) : sml_scope.                

End tvmNotations.                 