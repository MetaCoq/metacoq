Require Template.Ast.
Require Import PCUIC.TemplateToPCUIC.
Require Import TemplateExtraction.Extract.
Require Import String.
Local Open Scope string_scope.

Existing Instance PCUICChecker.default_fuel.

Definition extract `{F:utils.Fuel} (p:Template.Ast.program) : option E.program :=
  let '(genv, t) := p in
  let gc := (genv, uGraph.init_graph) in
  let genv' := trans_global gc in
  let genv'' := extract_global genv' in
  let t' := extract genv' nil (trans t) in
  match genv'', t' with
  | PCUICChecker.Checked genv', PCUICChecker.Checked t' =>
    Some (genv', t')
  | _, _ => None
  end.

Definition extract_term `{F:utils.Fuel} (p:Template.Ast.program) : option E.term :=
  match extract p with
  | Some (env, t) => Some t
  | None => None
  end.

Quote Recursively Definition id := (fun (A : Type) (a : A) => a).
Eval cbv in extract id.

Quote Recursively Definition idtype := (fun (A : Prop) => A).
Eval cbv in extract idtype.

Quote Recursively Definition types := (nat, bool, list, List.length, sig, fun A B => prod A B, gt).
Definition types_env := fst types.

Quote Definition len := Eval compute in (fun (A : Set) (l : list A) => List.length l).

Eval cbv in extract_term (types_env, len).

Program Definition exn : { x : nat | x > 0 } := 1.
Quote Recursively Definition exn_ast := exn.
Eval cbv in extract exn_ast.
