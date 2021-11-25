Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.RootTokenContract.ClassTypes.
Require Import Contracts.RootTokenContract.Ledger.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

Definition WrapperRet_ι_err_code _right {b} (x: URValue DRootTokenContractLRecord b): URValue XUInteger32 b :=
    || {x} ^^ {WrapperRet_ι_err_code} || : _ .
    
Definition WrapperRet_ι_err_code_left (x: ULValue DRootTokenContractLRecord): ULValue XUInteger32 :=
    {{ {x} ^^ {WrapperRet_ι_err_code} }} : _.
    
Notation " a '↑' 'xxx' " := ( WrapperRet_ι_err_code _right a ) (in custom URValue at level 0) : ursus_scope.
Notation " a '↑' 'xxx' " := ( WrapperRet_ι_err_code _left a ) (in custom ULValue at level 0) : ursus_scope.


End ClassTypesNotations.

