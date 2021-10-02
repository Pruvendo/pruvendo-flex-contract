Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.ProofEnvironment2.
Require Import Contracts.FlexClient.Ledger.
Require Import Contracts.FlexClient.Functions.FuncSig.
Require Import Project.CommonConstSig.
Require Import Contracts.FlexClient.Functions.FuncNotations.
Require Import UrsusTVM.tvmNotations.
Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
(* From elpi Require Import elpi. *)

Require Import Contracts.FlexClient.Functions.Funcs.

Module FlexClientTemplates (dc : ConstsTypesSig XTypesModule StateMonadModule).

Module Import FlexClientFuncs := FlexClientFuncs dc.
Import FlexClientFuncsInternal.

Check constructor.


End FlexClientTemplates.