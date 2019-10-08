Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From MetaCoq.Template Require Import
     Ast Loader.
From MetaCoq.Template.TemplateMonad Require Import
     Common Extractable.

Local Open Scope string_scope.

Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
   (only parsing).

MetaCoq Run
    (tmBind (tmReturn 1) (fun x => tmMsg (utils.string_of_nat x))).

MetaCoq Run
    (tmPrint <% 1 + 1 : nat %>).

Fail MetaCoq Run (tmFail "success").

MetaCoq Run
    (tmBind (tmEval cbv <% 1 + 1 %>)
            (fun t => tmPrint t)).

MetaCoq Run
    (tmBind (tmDefinition "two" None <% 1 + 1 %>)
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


MetaCoq Run
    (tmBind (tmQuoteInductive "Coq.Init.Datatypes.nat")
            (fun mi => tmMsg (utils.string_of_nat (length mi.(ind_bodies))))).

Definition empty_constraints : ConstraintSet.t_.
  econstructor.
  Unshelve.
  2:{ exact nil. }
  constructor.
Defined.

MetaCoq Run
    (tmInductive {| mind_entry_record := None
                  ; mind_entry_finite := Finite
                  ; mind_entry_params := nil
                  ; mind_entry_inds :=
                      {| mind_entry_typename := "thing"
                       ; mind_entry_arity := <% Set %>
                       ; mind_entry_template := false
                       ; mind_entry_consnames := "thing1" :: "thing2" :: nil
                       ; mind_entry_lc := tProd nAnon <% bool %> (tRel 1) ::
                                          tProd nAnon <% string %> (tRel 1) :: nil
                       |} :: nil
                  ; mind_entry_universes := Monomorphic_ctx (LevelSet.empty, empty_constraints)
                  ; mind_entry_private := None |}).
Print thing.

MetaCoq Run
    (tmBind tmCurrentModPath
            tmMsg).


Fail MetaCoq Run (tmQuoteInductive "nat").
MetaCoq Run (tmQuoteInductive "Coq.Init.Datatypes.nat").

Fail MetaCoq Run (tmQuoteConstant "plus" true).
MetaCoq Run (tmQuoteConstant "Coq.Init.Nat.add" true).
