Require Import UMLang.BasicModuleTypes.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger .


Module StateProofs (xt: XTypesSig) (sm: StateMonadSig).
Module Import ClassTypesModule := Contracts.Flex.ClassTypes xt . 
Module Import LedgerModule := FlexClass xt sm .

Check Ledger.
Print LedgerStateLRecord.


End StateProofs .