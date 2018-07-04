(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
Require Import Template.config Template.utils Template.kernel.univ.
From Extraction Require Import Ast Induction LiftSubst UnivSubst.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.


(** * Typing derivations

  *WIP*

  Inductive relations for reduction, conversion and typing of CIC terms.

 *)

(** ** Environment lookup *)

Definition global_decl_ident d :=
  match d with
  | ConstantDecl id _ => id
  | InductiveDecl id _ => id
  end.

Definition is_constant_decl d :=
  match d with
  | InductiveDecl _ _ => false
  | _ => true
  end.

Definition is_minductive_decl d :=
  match d with
  | InductiveDecl _ _ => true
  | _ => false
  end.

Definition is_inductive_decl_for i d :=
  match d with
  | InductiveDecl _ cb => i < List.length cb.(ind_bodies)
  | _ => False
  end.

Definition ident_eq (x y : ident) :=
  if string_dec x y then true else false.

Lemma ident_eq_spec x y : reflect (x = y) (ident_eq x y).
Proof.
  unfold ident_eq. destruct string_dec; constructor; auto.
Qed.

Fixpoint lookup_env (Σ : global_declarations) (id : ident) : option global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if ident_eq id (global_decl_ident hd) then Some hd
    else lookup_env tl id
  end.

Definition declared_constant (Σ : global_declarations) (id : ident) decl : Prop :=
  lookup_env Σ id = Some (ConstantDecl id decl).

Definition declared_minductive Σ mind decl :=
  lookup_env Σ mind = Some (InductiveDecl mind decl).

Definition declared_inductive Σ ind univs decl :=
  exists decl', declared_minductive Σ (inductive_mind ind) decl' /\
                univs = decl'.(ind_universes) /\
                List.nth_error decl'.(ind_bodies) (inductive_ind ind) = Some decl.

Definition declared_constructor Σ cstr univs decl : Prop :=
  let '(ind, k) := cstr in
  exists decl', declared_inductive Σ ind univs decl' /\
                List.nth_error decl'.(ind_ctors) k = Some decl.

Definition declared_projection Σ (proj : projection) decl : Prop :=
  let '(ind, ppars, arg) := proj in
  exists univs decl', declared_inductive Σ ind univs decl' /\
                List.nth_error decl'.(ind_projs) arg = Some decl.

Program
Definition type_of_constant_decl (d : global_decl | is_constant_decl d = true) : term :=
  match d with
  | InductiveDecl _ _ => !
  | ConstantDecl _ decl => decl.(cst_type)
  end.

Program
Definition body_of_constant_decl (d : global_decl | is_constant_decl d = true) : option term :=
  match d with
  | InductiveDecl _ _ => !
  | ConstantDecl _ decl => decl.(cst_body)
  end.

Program
Definition types_of_minductive_decl (d : global_decl | is_minductive_decl d = true) :
  list one_inductive_body :=
  match d with
  | InductiveDecl _ tys => tys.(ind_bodies)
  | ConstantDecl _ _ => !
  end.

Definition inds ind u (l : list one_inductive_body) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tInd (mkInd ind n) u :: aux n
      end
  in aux (List.length l).

Program
Definition type_of_constructor (Σ : global_declarations) (c : inductive * nat) (univs : universe_context) (u : list Level.t) (decl : ident * term * nat)
           (H : declared_constructor Σ c univs decl) :=
  let mind := inductive_mind (fst c) in
  let '(id, trm, args) := decl in
  match lookup_env Σ mind with
  | Some (InductiveDecl _ decl') =>
    substl (inds mind u decl'.(ind_bodies)) (subst_instance_constr u trm)
  | _ => !
  end.

Next Obligation.
  destruct H as [decl [H H']].
  destruct H as [decl' [H'' H''']].
  eapply H0.
  simpl. rewrite H''. reflexivity.
Defined.

(** ** Reduction *)

(** *** Helper functions for reduction *)

Definition fix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), substl (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a =>
    match a with
    | tConstruct _ _ _ => true
    | tApp (tConstruct _ _ _) _ => true
    | _ => false
    end
  | None => false
  end.

Definition tDummy := tRel 0.

Definition iota_red npar c args brs :=
  (mkApps (snd (List.nth c brs (0, tDummy))) (List.skipn npar args)).

Notation "#| Γ |" := (List.length Γ) (at level 0, Γ at level 99, format "#| Γ |").
