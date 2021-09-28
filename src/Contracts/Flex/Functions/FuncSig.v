Require Import UMLang.SolidityNotations2.
Require Import UMLang.SML_NG28.
Require Import UrsusTVM.tvmNotations.

Require Import Contracts.Flex.ClassTypes.
Require Import Contracts.Flex.Ledger .

Module FlexSpec (xt: XTypesSig) (sm: StateMonadSig).
Module Export ClassTypesModule := FlexClassTypes xt . 
Module Export LedgerModule := FlexClass xt sm .
Module Export tvmNotationsModule := tvmNotations xt sm LedgerModule. 


Module Type FlexSpecSig.

Axiom constructor : XInteger -> UExpression PhantomType  true.
Axiom deploy : XInteger -> UExpression XAddress  false.



End FlexSpecSig.


End FlexSpec.  