(* Distributed under the terms of the MIT license. *)
From Coq Require Import Program.
From MetaCoq.Template Require Import config utils Reflect.
From MetaCoq.Erasure Require Import EAst EAstUtils ELiftSubst EReflect ECSubst.
Require Import ssreflect.

(** * Typing derivations

  Inductive relations for reduction, conversion and typing of CIC terms.

 *)
(** ** Environment lookup *)

Fixpoint lookup_env (Σ : global_declarations) id : option global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if kername_eq_dec id hd.1 is left _ then Some hd.2
    else lookup_env tl id
  end.

Definition declared_constant (Σ : global_declarations) id decl : Prop :=
  lookup_env Σ id = Some (ConstantDecl decl).

Definition declared_minductive Σ mind decl :=
  lookup_env Σ mind = Some (InductiveDecl decl).

Definition declared_inductive Σ ind mdecl decl :=
  declared_minductive Σ (inductive_mind ind) mdecl /\
  List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

Definition declared_constructor Σ cstr mdecl idecl cdecl : Prop :=
  declared_inductive Σ (fst cstr) mdecl idecl /\
  List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

Definition declared_projection Σ (proj : projection) mdecl idecl pdecl : Prop :=
  declared_inductive Σ (fst (fst proj)) mdecl idecl /\
  List.nth_error idecl.(ind_projs) (snd proj) = Some pdecl.

Lemma elookup_env_cons_fresh {kn d Σ kn'} : 
  kn <> kn' ->
  ETyping.lookup_env ((kn, d) :: Σ) kn' = ETyping.lookup_env Σ kn'.
Proof.
  simpl. destruct kername_eq_dec. subst => //. auto. 
Qed.

(** Knowledge of propositionality status oof an inductive type *)

Definition is_propositional_ind Σ ind :=
  match lookup_env Σ (inductive_mind ind) with
  | Some (InductiveDecl mdecl) =>
    match nth_error mdecl.(ind_bodies) (inductive_ind ind) with 
    | Some idecl => Some (idecl.(ind_propositional))
    | None => None
    end
  | _ => None
  end.

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

Definition is_constructor_app_or_box t :=
  match t with
  | tBox => true
  | a =>
    let (f, a) := decompose_app a in
    match f with
    | tConstruct _ _ => true
    | _ => false
    end
  end.

Definition is_nth_constructor_app_or_box n ts :=
  match List.nth_error ts n with
  | Some a => is_constructor_app_or_box a
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

Definition tDummy := tVar ""%string.

Definition iota_red npar args (br : nat * term) :=
  substl (List.skipn npar args) br.2.
