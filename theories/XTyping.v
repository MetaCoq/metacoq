From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import Ast XAst Typing XLiftSubst.

Record context_decl := { decl_name : name ;
                         decl_body : option xterm ;
                         decl_type : xterm }.

Definition vass x A := {| decl_name := x; decl_body := None; decl_type := A |}.
Definition vdef x t A :=
  {| decl_name := x; decl_body := Some t; decl_type := A |}.

Definition context := (list context_decl).

Definition snoc (Γ : context) (d : context_decl) := d :: Γ.

Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

Fixpoint eq_term (t u : xterm) {struct t} :=
  match t, u with
  | xRel n, xRel n' => eq_nat n n'
  | xSort s, xSort s' => eq_sort s s'
  | xApp f A B u, xApp f' A' B' u' => eq_term f f' && eq_term A A' && eq_term B B' && eq_term u u'
  | xLambda A B b t, xLambda A' B' b' t' => eq_term b b' && eq_term t t'
  | xProd _ b t, xProd _ b' t' => eq_term b b' && eq_term t t'
  | _, _ => false
  end.

Fixpoint leq_term (t u : xterm) {struct t} :=
  match t, u with
  | xRel n, xRel n' => eq_nat n n'
  | xSort s, xSort s' => leq_sort s s'
  | xApp f A B u, xApp f' A' B' u' => eq_term f f' && eq_term A A' && eq_term B B' && eq_term u u'
  | xLambda A B b t, xLambda A' B' b' t' => eq_term b b' && eq_term t t'
  | xProd _ b t, xProd _ b' t' => eq_term b b' && leq_term t t'
  | _, _ => false (* Case, Proj, Fix, CoFix *)
  end.

Reserved Notation " Σ ;;; Γ |-- t : T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |-- t <= u " (at level 50, Γ, t, u at next level).

Record squash (A : Set) : Prop := { _ : A }.

Inductive typing (Σ : global_context) (Γ : context) : xterm -> xterm -> Set :=
| type_Rel n : forall (isdecl : n < List.length Γ),
    Σ ;;; Γ |-- (xRel n) : lift0 (S n) (safe_nth Γ (exist _ n isdecl)).(decl_type)

| type_Sort s :
    Σ ;;; Γ |-- (xSort s) : xSort (succ_sort s)

| type_Prod n t b s1 s2 :
    Σ ;;; Γ |-- t : xSort s1 ->
    Σ ;;; Γ ,, vass n t |-- b : xSort s2 ->
    Σ ;;; Γ |-- (xProd n t b) : xSort (max_sort s1 s2)

| type_Lambda n n' t b s1 s2 bty :
    Σ ;;; Γ |-- t : xSort s1 ->
    Σ ;;; Γ ,, vass n t |-- bty : xSort s2 ->
    Σ ;;; Γ ,, vass n t |-- b : bty ->
    Σ ;;; Γ |-- (xLambda n t bty b) : xProd n' t bty

| type_App n s1 s2 t A B u :
    Σ ;;; Γ |-- A : xSort s1 ->
    Σ ;;; Γ ,, vass n A |-- B : s2 ->
    Σ ;;; Γ |-- t : xProd n A B ->
    Σ ;;; Γ |-- u : A ->
    Σ ;;; Γ |-- (xApp t A B u) : B{ 0 := u }

| type_Conv t A B s :
    Σ ;;; Γ |-- t : A ->
    Σ ;;; Γ |-- B : xSort s ->
    Σ ;;; Γ |-- A <= B ->
    Σ ;;; Γ |-- t : B

where " Σ ;;; Γ |-- t : T " := (@typing Σ Γ t T) : type_scope

with cumul (Σ : global_context) (Γ : context) : xterm -> xterm -> Prop :=
| cumul_refl t u :
    leq_term t u = true -> cumul Σ Γ t u
(* | cumul_reflection i j p A B : *)
(*     Σ ;;; Γ |-- p : eq i (tSort (sType j)) A B -> cumul Σ Γ A B *)

where " Σ ;;; Γ |-- t <= u " := (@cumul Σ Γ t u) : type_scope.

Definition conv Σ Γ T U :=
  Σ ;;; Γ |-- T <= U /\ Σ ;;; Γ |-- U <= T.

Notation " Σ ;;; Γ |-- t = u " := (@conv Σ Γ t u) (at level 50, Γ, t, u at next level) : type_scope.