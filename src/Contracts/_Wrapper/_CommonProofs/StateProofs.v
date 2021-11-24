Require Import UMLang.BasicModuleTypes.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Contracts.Price.ClassTypes.
Require Import Contracts.Price.Ledger .


Module StateProofs (xt: XTypesSig) (sm: StateMonadSig).
Module Import ClassTypesModule := PriceClassTypes xt . 
Module Import LedgerModule := PriceClass xt sm .

Check Ledger.
Print LedgerStateLRecord.


End StateProofs .