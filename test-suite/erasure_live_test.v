From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import SafeTemplateErasure.
From Coq Require Import String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import utils monad_utils.

Definition test (p : Ast.program) : string :=
  match erase_and_print_template_program p with
  | inl s => s
  | inr s => s
  end.

Quote Recursively Definition zero := 0.
Eval lazy in test zero.

Quote Recursively Definition exproof := I.
Eval lazy in test exproof.

Quote Recursively Definition exintro := (@exist _ _ 0 (@eq_refl _ 0) : {x : nat | x = 0}).
Eval lazy in test exintro.

Quote Recursively Definition idnat := ((fun (X : Set) (x : X) => x) nat).
Eval lazy in test idnat.

(** Check that optimization of singleton pattern-matchings work *)
Quote Recursively Definition singlelim := ((fun (X : Set) (x : X) (e : x = x) =>
                  match e in eq _ x' return bool with
                  | eq_refl => true
                  end)).

Time Eval lazy in test singlelim.