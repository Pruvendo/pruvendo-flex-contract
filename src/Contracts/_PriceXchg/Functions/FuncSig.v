Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.PriceXchg.ClassTypes.
Require Import Contracts.PriceXchg.Ledger .

Module trainContractSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export ClassTypesModule := ClassTypes xt sm . 
Module Export LedgerModule := PriceXchgClass xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModule. 


Module Type PriceXchgSpecSig.




End PriceXchgSpecSig.


End PriceXchgSpec.  