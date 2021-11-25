Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.RootTokenContract.ClassTypes.
Require Import Contracts.RootTokenContract.Ledger.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := Contracts.RootTokenContract.ClassTypes.ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

End ClassTypesNotations.


