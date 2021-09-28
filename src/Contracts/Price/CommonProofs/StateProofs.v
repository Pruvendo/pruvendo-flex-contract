Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.SelfDeployer.ClassTypes.
Require Import Contracts.SelfDeployer.Ledger .


Module StateProofs (xt: XTypesSig) (sm: StateMonadSig).
Module Import ClassTypesModule := trainContractClassTypes xt . 
Module Import LedgerModule := SelfDeployerClass xt sm .

Check Ledger.
Print LedgerStateLRecord.


End StateProofs .