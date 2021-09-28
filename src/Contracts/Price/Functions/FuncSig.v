Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.SelfDeployer.ClassTypes.
Require Import Contracts.SelfDeployer.Ledger .

Module trainContractSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export ClassTypesModule := trainContractClassTypes xt . 
Module Export LedgerModule := SelfDeployerClass xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModule. 


Module Type trainContractSpecSig.

Axiom constructor : XInteger -> UExpression PhantomType  true.
Axiom deploy : XInteger -> UExpression XAddress  false.



End trainContractSpecSig.


End trainContractSpec.  