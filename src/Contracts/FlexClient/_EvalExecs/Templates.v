Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.ProofEnvironment2.
Require Import Contracts.Flex.Ledger.
Require Import Contracts.Flex.Functions.FuncSig.
Require Import Project.CommonConstSig.
Require Import Contracts.Flex.Functions.FuncNotations.
Require Import UrsusTVM.tvmNotations.
Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
(* From elpi Require Import elpi. *)

Require Import Contracts.Flex.Functions.Funcs.

Module FlexTemplates (dc : ConstsTypesSig XTypesModule StateMonadModule).

Module Import FlexContractFuncs := FlexFuncs dc.
Import FlexFuncsInternal.

(* Check constructor. *)


End FlexTemplates.