Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.ProofEnvironment2.
Require Import Ledger.
Require Import FuncSig.
Require Import Project.CommonConstSig.
Require Import FuncNotations.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.

Require Import Funcs.

Module trainTemplates (dc : trainConstsTypesSig XTypesModule StateMonadModule).

Module Import trainContractFuncs := trainFuncs dc.
Import trainFuncsInternal.

Check constructor.


End trainTemplates.