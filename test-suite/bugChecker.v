(* -*- coq-prog-args : ("-debug" "-type-in-type") -*-  *)

From Template Require Import Template Typing Checker Ast.
Require Import List String. Import ListNotations.
Set Printing Universes.

Definition T := Type.
Definition T' := T.
Definition foo' := (T : T').

Quote Recursively Definition p := foo'.
Eval lazy in (let '(Σ, t) := decompose_program p ([], init_graph) in
let t := (tSort (Universe.super (Level.Level "Top.10"))) in
let u := (tSort (Universe.make (Level.Level "Top.10"))) in
let Γ := [] in
leq_term (snd Σ) t u).
isconv (fst Σ) fuel (Cumul (snd Σ)) Γ t [] u []).


    (*      convert_leq Σ [] (tSort (Universe.super (Level.Level "Top.10"))) *)
    (*                  (tSort (Universe.make (Level.Level "Top.10")))). *)

    (* infer Σ [] t). *)

    (* let '(Σ, t) := decompose_program p ([], init_graph) in *)
    (* check_wf_env Σ ;; infer_term Σ t. *)
