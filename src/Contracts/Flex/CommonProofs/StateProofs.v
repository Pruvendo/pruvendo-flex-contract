Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger .


Module StateProofs (xt: XTypesSig) (sm: StateMonadSig).
Module Import ClassTypesModule := FlexClassTypes xt . 
Module Import LedgerModule := FlexClass xt sm .

Check Ledger.
Print LedgerStateLRecord.


End StateProofs .