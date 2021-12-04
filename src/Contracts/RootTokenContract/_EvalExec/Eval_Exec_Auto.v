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
Require Import UMLang.ExecGenerator.

Require Import UrsusTVM.Cpp.tvmTypes.
Require Import UrsusTVM.Cpp.tvmFunc.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonConstSig.
Require Import Project.CommonTypes.
Require Import Project.CommonNotations.

(*Fully qualified name are mandatory in multi-contract environment*)
Require Import RootTokenContract.Ledger.
Require Import RootTokenContract.Functions.FuncSig.
Require Import RootTokenContract.Functions.FuncNotations.
Require Import RootTokenContract.Functions.Funcs.

Require RootTokenContract.Interface.

(* Require Import TONTokenWallet.ClassTypes.
Require Import Contracts.TONTokenWallet.ClassTypesNotations. *)

Unset Typeclasses Iterative Deepening.
Set Typeclasses Depth 30.

Module EvalExecAuto (co : CompilerOptions)(dc : ConstsTypesSig XTypesModule StateMonadModule) .

Module Export FuncsModule := Funcs co dc.

Import FuncsInternal.

Import co.

(* Module Export FuncNotationsModuleForFunc := FuncNotations XTypesModule StateMonadModule dc. 
Import SpecModuleForFuncNotations.LedgerModuleForFuncSig. 
Module TONTokenWalletClassTypes := Contracts.TONTokenWallet.ClassTypes.ClassTypes XTypesModule StateMonadModule.
Module FuncsInternal <: SpecModuleForFuncNotations(* ForFuncs *).SpecSig. *)
 
Module Import xxx := SpecModuleForFuncNotations.LedgerModuleForFuncSig.


(* Module Import TONTokenWalletModuleForRoot := Contracts.TONTokenWallet.ClassTypesNotations.ClassTypesNotations XTypesModule StateMonadModule SpecModuleForFuncNotations.LedgerModuleForFuncSig. *)

Module Import generator := execGenerator XTypesModule StateMonadModule xxx.

Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.
Local Open Scope struct_scope.
Local Open Scope N_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Import URSUS_.

Section optional_owner.
Definition optional_owner_exec_P (l : Ledger) ( owner :  address  ): 
{l' | l' = exec_state (Uinterpreter (optional_owner owner)) l}.
  generate_proof (exec_expression l (optional_owner owner)).
Defined.

Definition optional_owner_auto_exec (l : Ledger) ( owner :  address  ): Ledger.
intros. term_of (optional_owner_exec_P l owner).
Defined.

Theorem optional_owner_exec_proof_next (l : Ledger) ( owner :  address  ) :
optional_owner_auto_exec l owner =
  exec_state (Uinterpreter (optional_owner owner)) l.
Proof.
  intros. proof_of (optional_owner_exec_P l owner).
Qed.



Definition optional_owner_eval_P (l : Ledger) ( owner :  address  ): 
{v | v = toValue (eval_state (Uinterpreter (optional_owner owner)) l)}.
  generate_proof (eval_expression l (optional_owner owner)).
Defined.
Definition optional_owner_auto_eval (l : Ledger) ( owner :  address  ):  (XMaybe address) .
intros. term_of (optional_owner_eval_P l owner).
Defined.
Theorem optional_owner_eval_proof_next (l : Ledger) ( owner :  address  ) :
optional_owner_auto_eval l owner =
  toValue (eval_state (Uinterpreter (optional_owner owner)) l).
Proof.
  intros. proof_of (optional_owner_eval_P l owner).
Qed.


End optional_owner.

Section is_internal_owner.
Definition is_internal_owner_exec_P (l : Ledger): 
{l' | l' = exec_state (Uinterpreter (is_internal_owner )) l}.
  generate_proof (exec_expression l (is_internal_owner )).
Defined.
Definition is_internal_owner_auto_exec (l : Ledger) : Ledger.
intros. term_of (is_internal_owner_exec_P l ).
Defined.
Theorem is_internal_owner_exec_proof_next (l : Ledger)  :
is_internal_owner_auto_exec l  =
  exec_state (Uinterpreter (is_internal_owner )) l.
Proof.
  intros. proof_of (is_internal_owner_exec_P l ).
Qed.



Definition is_internal_owner_eval_P (l : Ledger): 
{v | v = toValue (eval_state (Uinterpreter (is_internal_owner )) l)}.
  generate_proof (eval_expression l (is_internal_owner )).
Defined.
Definition is_internal_owner_auto_eval (l : Ledger): boolean.
intros. term_of (is_internal_owner_eval_P l ).
Defined.
Theorem is_internal_owner_eval_proof_next (l : Ledger) :
is_internal_owner_auto_eval l  =
  toValue (eval_state (Uinterpreter (is_internal_owner )) l).
Proof.
  intros. proof_of (is_internal_owner_eval_P l ).
Qed.



End is_internal_owner.

Section check_internal_owner.
Definition check_internal_owner_exec_P (l : Ledger) : 
{l' | l' = exec_state (Uinterpreter (check_internal_owner )) l}.
  generate_proof (exec_expression l (check_internal_owner )).
Defined.
Definition check_internal_owner_auto_exec (l : Ledger) : Ledger.
intros. term_of (check_internal_owner_exec_P l ).
Defined.
Theorem check_internal_owner_exec_proof_next (l : Ledger) :
check_internal_owner_auto_exec l  =
  exec_state (Uinterpreter (check_internal_owner )) l.
Proof.
  intros. proof_of (check_internal_owner_exec_P l ).
Qed.

End check_internal_owner.

Section check_external_owner.
Definition check_external_owner_exec_P (l : Ledger) ( allow_pubkey_owner_in_internal_node :  boolean  ): 
{l' | l' = exec_state (Uinterpreter (check_external_owner allow_pubkey_owner_in_internal_node)) l}.
  generate_proof (exec_expression l (check_external_owner allow_pubkey_owner_in_internal_node)).
Defined.
Definition check_external_owner_auto_exec (l : Ledger) ( allow_pubkey_owner_in_internal_node :  boolean  ): Ledger.
intros. term_of (check_external_owner_exec_P l allow_pubkey_owner_in_internal_node).
Defined.
Theorem check_external_owner_exec_proof_next (l : Ledger) ( allow_pubkey_owner_in_internal_node :  boolean  ) :
check_external_owner_auto_exec l allow_pubkey_owner_in_internal_node =
  exec_state (Uinterpreter (check_external_owner allow_pubkey_owner_in_internal_node)) l.
Proof.
  intros. proof_of (check_external_owner_exec_P l allow_pubkey_owner_in_internal_node).
Qed.



End check_external_owner.

Section check_owner.
Definition check_owner_exec_P (l : Ledger) ( allow_pubkey_owner_in_internal_node :  boolean  ): 
{l' | l' = exec_state (Uinterpreter (check_owner allow_pubkey_owner_in_internal_node)) l}.
  generate_proof (exec_expression l (check_owner allow_pubkey_owner_in_internal_node)).
Defined.
Definition check_owner_auto_exec (l : Ledger) ( allow_pubkey_owner_in_internal_node :  boolean  ): Ledger.
intros. term_of (check_owner_exec_P l allow_pubkey_owner_in_internal_node).
Defined.
Theorem check_owner_exec_proof_next (l : Ledger) ( allow_pubkey_owner_in_internal_node :  boolean  ) :
check_owner_auto_exec l allow_pubkey_owner_in_internal_node =
  exec_state (Uinterpreter (check_owner allow_pubkey_owner_in_internal_node)) l.
Proof.
  intros. proof_of (check_owner_exec_P l allow_pubkey_owner_in_internal_node).
Qed.

End check_owner.

Section constructor.
Definition constructor_exec_P (l : Ledger) ( name :  String  )
( symbol :  String  )
( decimals :  uint8  )
( root_public_key :  uint256  )
( root_owner :  address  )
( total_supply :  uint128  ) : 
{l' | l' = exec_state (Uinterpreter (constructor name symbol decimals root_public_key root_owner total_supply)) l}.
  generate_proof (exec_expression l (constructor name symbol decimals root_public_key root_owner total_supply)).
Defined.
Definition constructor_auto_exec (l : Ledger) ( name :  String  )
( symbol :  String  )
( decimals :  uint8  )
( root_public_key :  uint256  )
( root_owner :  address  )
( total_supply :  uint128  ): Ledger.
intros. term_of (constructor_exec_P l name symbol decimals root_public_key root_owner total_supply).
Defined.
Theorem constructor_exec_proof_next (l : Ledger) ( name :  String  )
( symbol :  String  )
( decimals :  uint8  )
( root_public_key :  uint256  )
( root_owner :  address  )
( total_supply :  uint128  ) :
constructor_auto_exec l name symbol decimals root_public_key root_owner total_supply =
  exec_state (Uinterpreter (constructor name symbol decimals root_public_key root_owner total_supply)) l.
Proof.
  intros. proof_of (constructor_exec_P l name symbol decimals root_public_key root_owner total_supply).
Qed.


End constructor.

Section setWalletCode.
Definition setWalletCode_exec_P (l : Ledger) ( wallet_code :  TvmCell  ): 
{l' | l' = exec_state (Uinterpreter (setWalletCode wallet_code)) l}.
  generate_proof (exec_expression l (setWalletCode wallet_code)).
Defined.
Definition setWalletCode_auto_exec (l : Ledger) ( wallet_code :  TvmCell  ): Ledger.
intros. term_of (setWalletCode_exec_P l wallet_code).
Defined.
Theorem setWalletCode_exec_proof_next (l : Ledger) ( wallet_code :  TvmCell  ) :
setWalletCode_auto_exec l wallet_code =
  exec_state (Uinterpreter (setWalletCode wallet_code)) l.
Proof.
  intros. proof_of (setWalletCode_exec_P l wallet_code).
Qed.


Definition setWalletCode_eval_P (l : Ledger) ( wallet_code :  TvmCell  ): 
{v | v =  (eval_state (Uinterpreter (setWalletCode wallet_code)) l)}.
  generate_proof (eval_expression l (setWalletCode wallet_code)).
Defined.

Definition setWalletCode_auto_eval (l : Ledger) ( wallet_code :  TvmCell  ): (ControlResult boolean true).
intros. term_of (setWalletCode_eval_P l wallet_code).
Defined.

Theorem setWalletCode_eval_proof_next (l : Ledger) ( wallet_code :  TvmCell  ) :
setWalletCode_auto_eval l wallet_code =
   (eval_state (Uinterpreter (setWalletCode wallet_code)) l).
Proof.
  intros. proof_of (setWalletCode_eval_P l wallet_code).
Qed.

End setWalletCode.


Section prepare_wallet_data.
Definition prepare_wallet_data_exec_P (l : Ledger) 
( name :  XString  )
( symbol :  XString  )
( decimals :  XUInteger8  )
( root_public_key :  XUInteger256  )
( wallet_public_key :  XUInteger256  )
( root_address :  address  )
( owner_address : XMaybe address  )
( code :  XCell  )
( workchain_id :  int  )
: 
{l' | l' = exec_state (Uinterpreter (prepare_wallet_data name symbol decimals 
                                    root_public_key wallet_public_key root_address
                                    owner_address code workchain_id)) l}.
  generate_proof (exec_expression l (prepare_wallet_data name symbol decimals 
                                        root_public_key wallet_public_key root_address
                                        owner_address code workchain_id)).
Defined.

Definition prepare_wallet_data_auto_exec (l : Ledger)
( name :  XString  )
( symbol :  XString  )
( decimals :  XUInteger8  )
( root_public_key :  XUInteger256  )
( wallet_public_key :  XUInteger256  )
( root_address :  address  )
( owner_address : XMaybe address  )
( code :  XCell  )
( workchain_id :  int  )
: Ledger.
intros. term_of (prepare_wallet_data_exec_P l name symbol decimals 
                    root_public_key wallet_public_key root_address
                    owner_address code workchain_id).
Defined.
Theorem prepare_wallet_data_exec_proof_next (l : Ledger) 
( name :  XString  )
( symbol :  XString  )
( decimals :  XUInteger8  )
( root_public_key :  XUInteger256  )
( wallet_public_key :  XUInteger256  )
( root_address :  address  )
( owner_address : XMaybe address  )
( code :  XCell  )
( workchain_id :  int  )
:
prepare_wallet_data_auto_exec l name symbol decimals 
root_public_key wallet_public_key root_address
owner_address code workchain_id =
  exec_state (Uinterpreter (prepare_wallet_data name symbol decimals 
  root_public_key wallet_public_key root_address
  owner_address code workchain_id)) l.
Proof.
  intros. proof_of (prepare_wallet_data_exec_P l name symbol decimals 
  root_public_key wallet_public_key root_address
  owner_address code workchain_id).
Qed.



Definition prepare_wallet_data_eval_P (l : Ledger) 
( name :  XString  )
( symbol :  XString  )
( decimals :  XUInteger8  )
( root_public_key :  XUInteger256  )
( wallet_public_key :  XUInteger256  )
( root_address :  address  )
( owner_address : XMaybe address  )
( code :  XCell  )
( workchain_id :  int  ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_wallet_data name symbol decimals 
root_public_key wallet_public_key root_address
owner_address code workchain_id)) l)}.
  generate_proof (eval_expression l (prepare_wallet_data name symbol decimals 
  root_public_key wallet_public_key root_address
  owner_address code workchain_id)).
Defined.
Definition prepare_wallet_data_auto_eval (l : Ledger) 
( name :  XString  )
( symbol :  XString  )
( decimals :  XUInteger8  )
( root_public_key :  XUInteger256  )
( wallet_public_key :  XUInteger256  )
( root_address :  address  )
( owner_address : XMaybe address  )
( code :  XCell  )
( workchain_id :  int  ): TONTokenWalletClassTypes.DTONTokenWalletLRecord.
intros. term_of (prepare_wallet_data_eval_P l name symbol decimals 
root_public_key wallet_public_key root_address
owner_address code workchain_id).
Defined.
Theorem prepare_wallet_data_eval_proof_next (l : Ledger) 
( name :  XString  )
( symbol :  XString  )
( decimals :  XUInteger8  )
( root_public_key :  XUInteger256  )
( wallet_public_key :  XUInteger256  )
( root_address :  address  )
( owner_address : XMaybe address  )
( code :  XCell  )
( workchain_id :  int  ) :
prepare_wallet_data_auto_eval l name symbol decimals 
root_public_key wallet_public_key root_address
owner_address code workchain_id =
  toValue (eval_state (Uinterpreter (prepare_wallet_data name symbol decimals 
  root_public_key wallet_public_key root_address
  owner_address code workchain_id)) l).
Proof.
  intros. proof_of (prepare_wallet_data_eval_P l name symbol decimals 
  root_public_key wallet_public_key root_address
  owner_address code workchain_id).
Qed.



End prepare_wallet_data.


Section prepare_wallet_state_init_and_addr.
Definition prepare_wallet_state_init_and_addr_exec_P (l : Ledger) ( wallet_data :  TONTokenWalletClassTypes.DTONTokenWalletLRecord  ): 
{l' | l' = exec_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l}.
  generate_proof (exec_expression l (prepare_wallet_state_init_and_addr wallet_data)).
Defined.
Definition prepare_wallet_state_init_and_addr_auto_exec (l : Ledger) ( wallet_data :  TONTokenWalletClassTypes.DTONTokenWalletLRecord  ): Ledger.
intros. term_of (prepare_wallet_state_init_and_addr_exec_P l wallet_data).
Defined.
Theorem prepare_wallet_state_init_and_addr_exec_proof_next (l : Ledger) ( wallet_data :  TONTokenWalletClassTypes.DTONTokenWalletLRecord  ) :
prepare_wallet_state_init_and_addr_auto_exec l wallet_data =
  exec_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l.
Proof.
  intros. proof_of (prepare_wallet_state_init_and_addr_exec_P l wallet_data).
Qed.



Definition prepare_wallet_state_init_and_addr_eval_P (l : Ledger) ( wallet_data :  TONTokenWalletClassTypes.DTONTokenWalletLRecord  ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l)}.
  generate_proof (eval_expression l (prepare_wallet_state_init_and_addr wallet_data)).
Defined.
Definition prepare_wallet_state_init_and_addr_auto_eval (l : Ledger) ( wallet_data :  TONTokenWalletClassTypes.DTONTokenWalletLRecord  ): ( StateInitLRecord # uint256 ).
intros. term_of (prepare_wallet_state_init_and_addr_eval_P l wallet_data).
Defined.
Theorem prepare_wallet_state_init_and_addr_eval_proof_next (l : Ledger) ( wallet_data :  TONTokenWalletClassTypes.DTONTokenWalletLRecord  ) :
prepare_wallet_state_init_and_addr_auto_eval l wallet_data =
  toValue (eval_state (Uinterpreter (prepare_wallet_state_init_and_addr wallet_data)) l).
Proof.
  intros. proof_of (prepare_wallet_state_init_and_addr_eval_P l wallet_data).
Qed.



End prepare_wallet_state_init_and_addr.


Section calc_wallet_init.
Definition calc_wallet_init_exec_P (l : Ledger) ( pubkey :  XUInteger256  ) ( owner_addr :  address  ): 
{l' | l' = exec_state (Uinterpreter (calc_wallet_init pubkey owner_addr)) l}.
  generate_proof (exec_expression l (calc_wallet_init pubkey owner_addr)).
Defined.
Definition calc_wallet_init_auto_exec (l : Ledger) ( pubkey :  XUInteger256  ) ( owner_addr :  address  ): Ledger.
intros. term_of (calc_wallet_init_exec_P l pubkey owner_addr).
Defined.
Theorem calc_wallet_init_exec_proof_next (l : Ledger) ( pubkey :  XUInteger256  ) ( owner_addr :  address  ) :
calc_wallet_init_auto_exec l pubkey owner_addr =
  exec_state (Uinterpreter (calc_wallet_init pubkey owner_addr)) l.
Proof.
  intros. proof_of (calc_wallet_init_exec_P l pubkey owner_addr).
Qed.



Definition calc_wallet_init_eval_P (l : Ledger) ( pubkey :  XUInteger256  ) ( owner_addr :  address  ): 
{v | v = toValue (eval_state (Uinterpreter (calc_wallet_init pubkey owner_addr)) l)}.
  generate_proof (eval_expression l (calc_wallet_init pubkey owner_addr)).
Defined.
Definition calc_wallet_init_auto_eval (l : Ledger) ( pubkey :  XUInteger256  ) ( owner_addr :  address  ):  StateInitLRecord # address.
intros. term_of (calc_wallet_init_eval_P l pubkey owner_addr).
Defined.
Theorem calc_wallet_init_eval_proof_next (l : Ledger) ( pubkey :  XUInteger256  ) ( owner_addr :  address  ) :
calc_wallet_init_auto_eval l pubkey owner_addr =
  toValue (eval_state (Uinterpreter (calc_wallet_init pubkey owner_addr)) l).
Proof.
  intros. proof_of (calc_wallet_init_eval_P l pubkey owner_addr).
Qed.



End calc_wallet_init.

Section deployWallet.
Definition deployWallet_exec_P (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( tokens :  XUInteger128  )
( grams :  XUInteger128  )
: 
{l' | l' = exec_state (Uinterpreter (deployWallet pubkey internal_owner tokens grams)) l}.
  generate_proof (exec_expression l (deployWallet  pubkey internal_owner tokens grams)).
Defined.
Definition deployWallet_auto_exec (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( tokens :  XUInteger128  )
( grams :  XUInteger128  ): Ledger.
intros. term_of (deployWallet_exec_P l pubkey internal_owner tokens grams).
Defined.
Theorem deployWallet_exec_proof_next (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( tokens :  XUInteger128  )
( grams :  XUInteger128  ) :
deployWallet_auto_exec l pubkey internal_owner tokens grams =
  exec_state (Uinterpreter (deployWallet pubkey internal_owner tokens grams)) l.
Proof.
  intros. proof_of (deployWallet_exec_P l pubkey internal_owner tokens grams).
Qed.



Definition deployWallet_eval_P (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( tokens :  XUInteger128  )
( grams :  XUInteger128  ): 
{v | v =  (eval_state (Uinterpreter (deployWallet pubkey internal_owner tokens grams)) l)}.
  generate_proof (eval_expression l (deployWallet pubkey internal_owner tokens grams)).
Defined.
Definition deployWallet_auto_eval (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( tokens :  XUInteger128  )
( grams :  XUInteger128  ): (ControlResult address true).
intros. term_of (deployWallet_eval_P l pubkey internal_owner tokens grams).
Defined.
Theorem deployWallet_eval_proof_next (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( tokens :  XUInteger128  )
( grams :  XUInteger128  ) :
deployWallet_auto_eval l pubkey internal_owner tokens grams =
   (eval_state (Uinterpreter (deployWallet pubkey internal_owner tokens grams)) l).
Proof.
  intros. proof_of (deployWallet_eval_P l pubkey internal_owner tokens grams).
Qed.




End deployWallet.

Section deployEmptyWallet.

Definition deployEmptyWallet_exec_P (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( grams :  XUInteger128  ): 
{l' | l' = exec_state (Uinterpreter (deployEmptyWallet pubkey internal_owner  grams)) l}.
  generate_proof (exec_expression l (deployEmptyWallet pubkey internal_owner  grams)).
Defined.
Definition deployEmptyWallet_auto_exec (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( grams :  XUInteger128  ): Ledger.
intros. term_of (deployEmptyWallet_exec_P l pubkey internal_owner  grams).
Defined.
Theorem deployEmptyWallet_exec_proof_next (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( grams :  XUInteger128  ) :
deployEmptyWallet_auto_exec l pubkey internal_owner  grams =
  exec_state (Uinterpreter (deployEmptyWallet pubkey internal_owner  grams)) l.
Proof.
  intros. proof_of (deployEmptyWallet_exec_P l pubkey internal_owner  grams).
Qed.



Definition deployEmptyWallet_eval_P (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( grams :  XUInteger128  ): 
{v | v =  (eval_state (Uinterpreter (deployEmptyWallet pubkey internal_owner  grams)) l)}.
  generate_proof (eval_expression l (deployEmptyWallet pubkey internal_owner  grams)).
Defined.
Definition deployEmptyWallet_auto_eval (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( grams :  XUInteger128  ): (ControlResult address true).
intros. term_of (deployEmptyWallet_eval_P l pubkey internal_owner  grams).
Defined.
Theorem deployEmptyWallet_eval_proof_next (l : Ledger) ( pubkey :  XUInteger256  )
( internal_owner :  address  )
( grams :  XUInteger128  ) :
deployEmptyWallet_auto_eval l pubkey internal_owner  grams =
   (eval_state (Uinterpreter (deployEmptyWallet pubkey internal_owner  grams)) l).
Proof.
  intros. proof_of (deployEmptyWallet_eval_P l pubkey internal_owner  grams).
Qed.




End deployEmptyWallet.


Section grant.
Definition grant_exec_P (l : Ledger) ( dest :  address  )
( tokens :  XUInteger128  )
( grams :  XUInteger128  )
: 
{l' | l' = exec_state (Uinterpreter (grant dest tokens grams)) l}.
  generate_proof (exec_expression l (grant dest tokens grams)).
Defined.
Definition grant_auto_exec (l : Ledger) ( dest :  address  )
( tokens :  XUInteger128  )
( grams :  XUInteger128  ): Ledger.
intros. term_of (grant_exec_P l dest tokens grams).
Defined.
Theorem grant_exec_proof_next (l : Ledger) ( dest :  address  )
( tokens :  XUInteger128  )
( grams :  XUInteger128  ) :
grant_auto_exec l dest tokens grams =
  exec_state (Uinterpreter (grant dest tokens grams)) l.
Proof.
  intros. proof_of (grant_exec_P l dest tokens grams).
Qed.


End grant.

Section mint.

Definition mint_exec_P (l : Ledger) ( tokens :  XUInteger128  ): 
{l' | l' = exec_state (Uinterpreter (mint tokens)) l}.
  generate_proof (exec_expression l (mint tokens)).
Defined.
Definition mint_auto_exec (l : Ledger) ( tokens :  XUInteger128  ): Ledger.
intros. term_of (mint_exec_P l tokens).
Defined.
Theorem mint_exec_proof_next (l : Ledger) ( tokens :  XUInteger128  ) :
mint_auto_exec l tokens =
  exec_state (Uinterpreter (mint tokens)) l.
Proof.
  intros. proof_of (mint_exec_P l tokens).
Qed.


Definition mint_eval_P (l : Ledger) ( tokens :  XUInteger128  ): 
{v | v =  (eval_state (Uinterpreter (mint tokens)) l)}.
  generate_proof (eval_expression l (mint tokens)).
Defined.
Definition mint_auto_eval (l : Ledger) ( tokens :  XUInteger128  ): (ControlResult boolean true).
intros. term_of (mint_eval_P l tokens).
Defined.
Theorem mint_eval_proof_next (l : Ledger) ( tokens :  XUInteger128  ) :
  mint_auto_eval l tokens =
   (eval_state (Uinterpreter (mint tokens)) l).
Proof.
  intros. proof_of (mint_eval_P l tokens).
Qed.

End mint.

Section requestTotalGranted.
Definition requestTotalGranted_exec_P (l : Ledger): 
{l' | l' = exec_state (Uinterpreter (requestTotalGranted )) l}.
  generate_proof (exec_expression l (requestTotalGranted )).
Defined.
Definition requestTotalGranted_auto_exec (l : Ledger) : Ledger.
intros. term_of (requestTotalGranted_exec_P l ).
Defined.
Theorem requestTotalGranted_exec_proof_next (l : Ledger):
  requestTotalGranted_auto_exec l  =
  exec_state (Uinterpreter (requestTotalGranted )) l.
Proof.
  intros. proof_of (requestTotalGranted_exec_P l ).
Qed.



Definition requestTotalGranted_eval_P (l : Ledger): 
{v | v = toValue (eval_state (Uinterpreter (requestTotalGranted )) l)}.
  generate_proof (eval_expression l (requestTotalGranted )).
Defined.
Definition requestTotalGranted_auto_eval (l : Ledger): XUInteger128.
intros. term_of (requestTotalGranted_eval_P l ).
Defined.
Theorem requestTotalGranted_eval_proof_next (l : Ledger) :
requestTotalGranted_auto_eval l  =
  toValue (eval_state (Uinterpreter (requestTotalGranted )) l).
Proof.
  intros. proof_of (requestTotalGranted_eval_P l ).
Qed.



End requestTotalGranted.

Section _on_bounced.

Definition _on_bounced_exec_P (l : Ledger) ( msg :  XCell  )
( msg_body :  XSlice  )
: 
{l' | l' = exec_state (Uinterpreter (_on_bounced msg msg_body)) l}.
  generate_proof (exec_expression l (_on_bounced msg msg_body)).
Defined.

Definition _on_bounced_auto_exec (l : Ledger) ( msg :  XCell  )
( msg_body :  XSlice  ): Ledger.
intros. term_of (_on_bounced_exec_P l msg msg_body).
Defined.

Theorem _on_bounced_exec_proof_next (l : Ledger) ( msg :  XCell  )
( msg_body :  XSlice  ) :
  _on_bounced_auto_exec l msg msg_body =
  exec_state (Uinterpreter (_on_bounced msg msg_body)) l.
Proof.
  intros. proof_of (_on_bounced_exec_P l msg msg_body).
Qed.



Definition _on_bounced_eval_P (l : Ledger) ( msg :  XCell  )
( msg_body :  XSlice  ): 
{v | v =  (eval_state (Uinterpreter (_on_bounced msg msg_body)) l)}.
  generate_proof (eval_expression l (_on_bounced msg msg_body)).
Defined.

Definition _on_bounced_auto_eval (l : Ledger) ( msg :  XCell  )
( msg_body :  XSlice  ): (ControlResult XUInteger true).
intros. term_of (_on_bounced_eval_P l msg msg_body).
Defined.

Theorem _on_bounced_eval_proof_next (l : Ledger) ( msg :  XCell  )
( msg_body :  XSlice  ) :
_on_bounced_auto_eval l msg msg_body =
   (eval_state (Uinterpreter (_on_bounced msg msg_body)) l).
Proof.
  intros. proof_of (_on_bounced_eval_P l msg msg_body).
Qed.

End _on_bounced.


Section prepare_root_state_init_and_addr.
Definition prepare_root_state_init_and_addr_exec_P (l : Ledger) ( root_code :  XCell  )
( root_data :  DRootTokenContractLRecord  )
: 
{l' | l' = exec_state (Uinterpreter (prepare_root_state_init_and_addr root_code root_data)) l}.
  generate_proof (exec_expression l (prepare_root_state_init_and_addr root_code root_data)).
Defined.

Definition prepare_root_state_init_and_addr_auto_exec (l : Ledger) ( root_code :  XCell  )
( root_data :  DRootTokenContractLRecord  ): Ledger.
intros. term_of (prepare_root_state_init_and_addr_exec_P l  root_code root_data).
Defined.
Theorem prepare_root_state_init_and_addr_exec_proof_next (l : Ledger) ( root_code :  XCell  )
( root_data :  DRootTokenContractLRecord  ) :
  prepare_root_state_init_and_addr_auto_exec l root_code root_data =
  exec_state (Uinterpreter (prepare_root_state_init_and_addr root_code root_data)) l.
Proof.
  intros. proof_of (prepare_root_state_init_and_addr_exec_P l root_code root_data).
Qed.



Definition prepare_root_state_init_and_addr_eval_P (l : Ledger) ( root_code :  XCell  )
( root_data :  DRootTokenContractLRecord  ): 
{v | v = toValue (eval_state (Uinterpreter (prepare_root_state_init_and_addr root_code root_data)) l)}.
  generate_proof (eval_expression l (prepare_root_state_init_and_addr root_code root_data)).
Defined.
Definition prepare_root_state_init_and_addr_auto_eval (l : Ledger) ( root_code :  XCell  )
( root_data :  DRootTokenContractLRecord  ): StateInitLRecord * XUInteger256.
intros. term_of (prepare_root_state_init_and_addr_eval_P l root_code root_data).
Defined.
Theorem prepare_root_state_init_and_addr_eval_proof_next (l : Ledger) ( root_code :  XCell  )
( root_data :  DRootTokenContractLRecord  ) :
prepare_root_state_init_and_addr_auto_eval l root_code root_data =
  toValue (eval_state (Uinterpreter (prepare_root_state_init_and_addr root_code root_data)) l).
Proof.
  intros. proof_of (prepare_root_state_init_and_addr_eval_P l root_code root_data).
Qed.



End prepare_root_state_init_and_addr.
