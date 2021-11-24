Require Import UMLang.BasicModuleTypes.
Require Import UMLang.UrsusLib.

Require Import UrsusTVM.Cpp.tvmFunc.

Require Import Project.CommonNotations.
Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger.


Module ClassTypesNotations (xt: XTypesSig) (sm: StateMonadSig) (cs : ClassSigTVM xt sm).
Module Export CommonNotationsModule := CommonNotations xt sm cs.
Module Export ClassTypesModule := Contracts.Flex.ClassTypes.ClassTypes xt sm.

Import UrsusNotations.
Local Open Scope ursus_scope.

End ClassTypesNotations.

