(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From Template Require Import utils univ AstUtils.
From Template Require UnivSubst.
From TemplateExtraction Require Import Ast Induction LiftSubst.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

(** * Universe substitution

  *WIP*

  Substitution of universe levels for universe level variables, used to
  implement universe polymorphism. *)

Fixpoint subst_instance_constr (u : universe_instance) (c : term) :=
  match c with
  | tBox | tRel _ | tVar _ | tMeta _ => c
  | tConst c u' => tConst c (UnivSubst.subst_instance_instance u u')
  | tConstruct ind k u' => tConstruct ind k (UnivSubst.subst_instance_instance u u')
  | tEvar ev args => tEvar ev (List.map (subst_instance_constr u) args)
  | tLambda na M => tLambda na (subst_instance_constr u M)
  | tApp f v => tApp (subst_instance_constr u f) (subst_instance_constr u v)
  | tLetIn na b b' => tLetIn na (subst_instance_constr u b)
                                (subst_instance_constr u b')
  | tCase ind c brs =>
    let brs' := List.map (on_snd (subst_instance_constr u)) brs in
    tCase ind (subst_instance_constr u c) brs'
  | tProj p c => tProj p (subst_instance_constr u c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (subst_instance_constr u)) mfix in
    tCoFix mfix' idx
  end.

Definition subst_instance_context (u : universe_instance) (c : context) : context :=
  map_context (subst_instance_constr u) c.