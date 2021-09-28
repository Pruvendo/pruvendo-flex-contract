Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String. 

Require Import UMLang.ProofEnvironment2.
Require Import Ledger.
Require Import FuncSig.
Require Import Project.CommonConstSig.
Require Import FuncNotations.
Require Import UrsusTVM.tvmNotations.
Require Import FinProof.Common. 
Require Import FinProof.ProgrammingWith.
From elpi Require Import elpi.

Elpi Command AddLocalState.

Elpi Accumulate lp:{{

main [Name , Term, LocalStateFieldT] :-
  trm TrmInternal = Term,
  trm LocalStateField = LocalStateFieldT,
  str NameStr = Name,
  N is NameStr ^ "_j",
  coq.env.add-axiom N  (app [LocalStateField , TrmInternal]) _ , 
  coq.locate  N GR, 
  coq.TC.declare-instance GR 0,
  coq.say TrmInternal.
main _ :- coq.error "usage: AddLocalState <name> <term> <LocalStateField>".

}}.

Elpi Typecheck.
Elpi Export AddLocalState.

Elpi Command TestDefinitions. 
Elpi Accumulate lp:{{

pred get_name i:string , o:term.
get_name NameS NameG :-
    coq.locate NameS GR ,
    NameG = global GR . 

pred constructors_names i:string , o:list constructor.
constructors_names IndName Names :-
  std.assert! (coq.locate IndName (indt GR)) "not an inductive type",
  coq.env.indt GR _ _ _ _ Names _.

pred coqlist->list i:term, o: list term.
coqlist->list {{ [ ]%xlist }} [ ].
coqlist->list {{ (lp:X::lp:XS)%xlist }} [X | M] :- coqlist->list XS M.
coqlist->list X _ :- coq.say "error",
                    coq.say X.

main [ A ] :-
  coq.say  A. 
}}. 

Elpi Typecheck.
 
(* Module trainContractSpecModuleForFuncs := trainContractSpec XTypesModule StateMonadModule. *)

Module trainFuncs (dc : trainConstsTypesSig XTypesModule StateMonadModule) .

Module Export trainFuncNotationsModule := trainFuncNotations XTypesModule StateMonadModule dc. 
Import trainContractSpecModule(* ForFuncs *).tvmNotationsModule.

Module trainFuncsInternal <: trainContractSpecModule(* ForFuncs *).trainContractSpecSig.
 
Import UrsusNotations.
Local Open Scope ursus_scope.
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope xlist_scope.

Local Notation UE := (UExpression _ _).
Local Notation UEf := (UExpression _ false).
Local Notation UEt := (UExpression _ true).

Notation " 'public' x " := ( x )(at level 12, left associativity, only parsing) : ursus_scope .
 
Arguments urgenerate_field {_} {_} {_} _ & .

Notation " |{ e }| " := e (in custom URValue at level 0, 
                           e custom ULValue ,  only parsing ) : ursus_scope.

Definition onlyOwner {X b}`{XDefault X} (e:UExpression X b) : UExpression X true .
   refine {{ require_ ( (tvm.pubkey() != 0) && (tvm.pubkey() == msg.pubkey()), 1 ) ; { _ } }} .
   refine {{ tvm.accept(); {e} }}.
Defined .

Existing Instance xbool_default.

Definition constructor (_depth: XInteger) : public UExpression PhantomType true.
refine {{_depth: XInteger @ "_depth" ; {_} }}.
refine {{ require_ ( ((tvm.pubkey() != 0) && (tvm.pubkey() == msg.pubkey())) \\
                      (msg.sender() == m_parent), 1 ) ; { _ } }} .
refine {{ tvm.accept(); {_} }}.
refine {{ m_depth := !{_depth} }}.
Defined.

Elpi AddLocalState _l1 (XHMap XAddress XBool) (LocalStateField).
Elpi AddLocalState _l2 (MessagesAndEventsStateLRecord) (LocalStateField).

Definition deploy (_value: XInteger) : public UExpression XAddress false.
refine {{_value: XInteger @ "_value" ; {_} }}.
refine {{new code @ "code" := tvm.code(); {_}  }}.
refine {{new addr @ "addr" := 0; {_}  }}.
(* addr = new SelfDeployer{
            value: 2 ton,
            code: code,
            varInit: {
                m_value: _value,
                m_parent: address(this)
            }
        }(m_depth + 1); *)
(*refine {{ if (!{_value}==0)then { {_:UEf} }else{ {_:UEf} } ; {_} }}. *)
refine {{ m_chilred [[ !{addr} ]] := TRUE ; { _ } }}.
refine {{ return_ !{addr} }}.
Defined.

Definition aaa : URValue XInteger  false := || m_value ||.


Elpi TestDefinitions Definition constructor' (_depth: XInteger) : public UExpression PhantomType true :=
{{
    _depth: XInteger @ "_depth" ; 
    new 'xxx : XAddress @ "xxx" := {} ;
    require_ ( ((tvm.pubkey() != 0) && (tvm.pubkey() == msg.pubkey())) \\
                      (msg.sender() == m_parent), 1 ) ;
    tvm.accept();
    
    m_depth := !{_depth} 
}}.


End trainFuncsInternal.
End trainFuncs.








