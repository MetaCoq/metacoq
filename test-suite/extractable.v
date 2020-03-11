Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
From MetaCoq.Template Require Import
     Ast Loader utils.
From MetaCoq.Template.TemplateMonad Require Import
     Common Extractable.

Local Open Scope string_scope.

Notation "<% x %>" := (ltac:(let p y := exact y in quote_term x p))
   (only parsing).

Run TemplateProgram
    (tmBind (tmReturn 1) (fun x => tmMsg (string_of_nat x))).

Run TemplateProgram
    (tmPrint <% 1 + 1 : nat %>).

Fail Run TemplateProgram (tmFail "success").

Run TemplateProgram
    (tmBind (tmEval cbv <% 1 + 1 %>)
            (fun t => tmPrint t)).

Run TemplateProgram
    (tmBind (tmDefinition "two" None <% 1 + 1 %>)
            (fun kn => tmPrint (Ast.tConst kn nil))).

Run TemplateProgram
    (tmBind (tmAxiom "assume" <% nat %>)
            (fun kn => tmPrint (Ast.tConst kn nil))).


Run TemplateProgram
    (tmBind (tmFreshName "blah")
            (fun i => tmBind (tmMsg i)
                          (fun _ => tmAxiom i <% bool %>))).
Print blah.
Fail Print blah0.
Run TemplateProgram
    (tmBind (tmFreshName "blah0")
            (fun i => tmBind (tmMsg i)
                          (fun _ => tmAxiom i <% bool %>))).
Print blah0.


Run TemplateProgram
    (tmBind (tmQuoteInductive "Coq.Init.Datatypes.nat")
            (fun mi => tmMsg (string_of_nat (length mi.(ind_bodies))))).

Definition empty_constraints : ConstraintSet.t_.
  econstructor.
  Unshelve.
  2:{ exact nil. }
  constructor.
Defined.

Run TemplateProgram
    (tmInductive {| mind_entry_record := None
                  ; mind_entry_finite := Finite
                  ; mind_entry_params := nil
                  ; mind_entry_inds :=
                      {| mind_entry_typename := "thing"
                       ; mind_entry_arity := <% Set %>
                       ; mind_entry_consnames := "thing1" :: "thing2" :: nil
                       ; mind_entry_lc := tProd nAnon <% bool %> (tRel 1) ::
                                          tProd nAnon <% string %> (tRel 1) :: nil
                       |} :: nil
                  ; mind_entry_universes := Monomorphic_entry (LevelSet.empty, empty_constraints)
                  ; mind_entry_template := false
                  ; mind_entry_cumulative := false
                  ; mind_entry_private := None |}).
Print thing.

Run TemplateProgram
    (tmBind tmCurrentModPath
            tmMsg).


Fail Run TemplateProgram (tmQuoteInductive "nat").
Run TemplateProgram (tmQuoteInductive "Coq.Init.Datatypes.nat").

Fail Run TemplateProgram (tmQuoteConstant "plus" true).
Run TemplateProgram (tmQuoteConstant "Coq.Init.Nat.add" true).
