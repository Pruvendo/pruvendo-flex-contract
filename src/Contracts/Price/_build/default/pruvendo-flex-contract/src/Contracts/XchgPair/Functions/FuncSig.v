Require Import FinProof.Common. 

Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusStdLib.Cpp.stdTypes.

Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Project.CommonNotations.

Require Import XchgPair.ClassTypes.
Require Import XchgPair.ClassTypesNotations.
Require Import XchgPair.Ledger.

Module Spec (xt: XTypesSig) (sm: StateMonadSig).

Module LedgerModuleForFuncSig := Ledger xt sm .
Module Export ClassTypesNotationsModule := ClassTypesNotations xt sm LedgerModuleForFuncSig.

Module Type SpecSig.

Local Open Scope ursus_scope.
Local Open Scope ucpp_scope.

Parameter onDeploy :  uint128 -> uint128 -> raw_address -> UExpression boolean true . 
Parameter getFlexAddr : UExpression raw_address false . 
Parameter getTip3MajorRoot : UExpression raw_address false . 
Parameter getTip3MinorRoot : UExpression raw_address false . 
Parameter getMinAmount : UExpression uint128 false . 
Parameter getNotifyAddr : UExpression raw_address false . 
Parameter _fallback : TvmCell -> TvmSlice -> UExpression uint false . 

Parameter prepare_xchg_pair_state_init_and_addr: ContractLRecord -> TvmCell -> UExpression ( StateInitLRecord # uint256 ) false . 

End SpecSig.

End Spec.  