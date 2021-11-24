Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.ProofEnvironment2.
Require Import Contracts.PriceXchg.Ledger.
Require Import Contracts.PriceXchg.Functions.FuncSig.
Require Import Project.CommonConstSig.
Require Import Contracts.PriceXchg.Functions.FuncNotations.
Require Import UrsusTVM.Cpp.tvmNotations.
Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
(* From elpi Require Import elpi. *)

Require Import Contracts.PriceXchg.Functions.Funcs.

Module PriceXchgTemplates (dc : PriceXchgConstsTypesSig XTypesModule StateMonadModule).

Module Import PriceXchgFuncs := PriceXchgFuncs dc.
Import PriceXchgFuncsInternal.

Check constructor.


End PriceXchgTemplates.