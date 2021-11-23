Require Import UMLang.BasicModuleTypes.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.Cpp.tvmNotations.

Require Import Contracts.PriceXchg.ClassTypes.
Require Import Contracts.PriceXchg.Ledger .


Module StateProofs (xt: XTypesSig) (sm: StateMonadSig).
Module Import ClassTypesModule := PriceXchgClassTypes xt . 
Module Import LedgerModule := PriceXchgClass xt sm .

Check Ledger.
Print LedgerStateLRecord.


End StateProofs .