Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.FlexClient.ClassTypes.
Require Import Contracts.FlexClient.Ledger .


Module StateProofs (xt: XTypesSig) (sm: StateMonadSig).
Module Import ClassTypesModule := ClassTypes xt . 
Module Import LedgerModule := FlexClientClass xt sm .

Check Ledger.
Print LedgerStateLRecord.


End StateProofs .