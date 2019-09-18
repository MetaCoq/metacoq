(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils.
From MetaCoq.Erasure Require Import EAst EAstUtils EInduction ELiftSubst.
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

Definition declared_inductive Σ mdecl ind decl :=
  declared_minductive Σ (inductive_mind ind) mdecl /\
  List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

Definition declared_constructor Σ mdecl idecl cstr cdecl : Prop :=
  declared_inductive Σ mdecl (fst cstr) idecl /\
  List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

Definition declared_projection Σ mdecl idecl (proj : projection) pdecl : Prop :=
  declared_inductive Σ mdecl (fst (fst proj)) idecl /\
  List.nth_error idecl.(ind_projs) (snd proj) = Some pdecl.

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
  | Some d => Some (d.(rarg), subst0 (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cofix_subst (l : mfixpoint term) :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n => tCoFix l n :: aux n
      end
  in aux (List.length l).

Definition unfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), subst0 (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition is_constructor n ts :=
  match List.nth_error ts n with
  | Some a =>
    let (f, a) := decompose_app a in
    match f with
    | tConstruct _ _ => true
    | _ => false
    end
  | None => false
  end.

Definition is_constructor_or_box n ts :=
  match List.nth_error ts n with
  | Some tBox => true
  | Some a =>
    let (f, a) := decompose_app a in
    match f with
    | tConstruct _ _ => true
    | _ => false
    end
  | None => false
  end.

Lemma fix_subst_length mfix : #|fix_subst mfix| = #|mfix|.
Proof.
  unfold fix_subst. generalize (tFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Lemma cofix_subst_length mfix : #|cofix_subst mfix| = #|mfix|.
Proof.
  unfold cofix_subst. generalize (tCoFix mfix). intros.
  induction mfix; simpl; auto.
Qed.

Definition tDummy := tVar "".

Definition iota_red npar c args brs :=
  (mkApps (snd (List.nth c brs (0, tDummy))) (List.skipn npar args)).
