Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From MetaCoq.Template Require Import
     BasicAst Ast Loader utils.
From MetaCoq.Template.TemplateMonad Require Import
     Common Extractable.

Local Open Scope bs_scope.
Import MCMonadNotation.

Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
   (only parsing).

MetaCoq Run
    (tmBind (tmReturn 1) (fun x => tmMsg (string_of_nat x))).

MetaCoq Run
    (tmPrint <% 1 + 1 : nat %>).

Fail MetaCoq Run (tmFail "success").

MetaCoq Run
    (tmBind (tmEval cbv <% 1 + 1 %>)
            (fun t => tmPrint t)).

MetaCoq Run
    (tmBind (tmDefinition "two"%bs None <% 1 + 1 %>)
            (fun kn => tmPrint (Ast.tConst kn nil))).

MetaCoq Run
    (tmBind (tmAxiom "assume" <% nat %>)
            (fun kn => tmPrint (Ast.tConst kn nil))).


MetaCoq Run
    (tmBind (tmFreshName "blah")
            (fun i => tmBind (tmMsg i)
                          (fun _ => tmAxiom i <% bool %>))).
Print blah.
Fail Print blah0.
MetaCoq Run
    (tmBind (tmFreshName "blah0")
            (fun i => tmBind (tmMsg i)
                          (fun _ => tmAxiom i <% bool %>))).
Print blah0.

MetaCoq Test Quote nat.
MetaCoq Run
    (tmBind (tmQuoteInductive (MPfile ["Datatypes"; "Init"; "Coq"], "nat"))
            (fun mi => tmMsg (string_of_nat (length mi.(ind_bodies))))).

Definition nAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.

MetaCoq Run
    (tmInductive true {| mind_entry_record := None
                  ; mind_entry_finite := Finite
                  ; mind_entry_params := nil
                  ; mind_entry_inds :=
                      {| mind_entry_typename := "thing"
                       ; mind_entry_arity := <% Set %>
                       ; mind_entry_consnames := "thing1" :: "thing2" :: nil
                       ; mind_entry_lc := tProd nAnon <% bool %> (tRel 1) ::
                                          tProd nAnon <% string %> (tRel 1) :: nil
                       |} :: nil
                  ; mind_entry_universes := Monomorphic_entry ContextSet.empty
                  ; mind_entry_template := false
                  ; mind_entry_variance := None
                  ; mind_entry_private := None |}).
Print thing.

MetaCoq Run
    (tmBind tmCurrentModPath
            (fun s => tmMsg (string_of_modpath s))).

MetaCoq Test Quote plus.
MetaCoq Run (tmQuoteInductive (MPfile ["Datatypes"; "Init"; "Coq"], "nat")).

MetaCoq Run (tmQuoteConstant (MPfile ["Nat"; "Init"; "Coq"], "add") true).
