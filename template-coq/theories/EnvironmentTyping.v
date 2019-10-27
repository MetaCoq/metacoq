From Coq Require Import Ascii String Bool OrderedType Lia List Program Arith.
From MetaCoq.Template Require Import utils BasicAst AstUtils.
From MetaCoq.Template Require Import Universes Environment.
Import List.ListNotations.
Require Import ssreflect.

Set Asymmetric Patterns.

Module Lookup (T : Term) (E : EnvironmentSig T).

  Import T E.

  (** ** Environment lookup *)

  Definition global_decl_ident d :=
    match d with
    | ConstantDecl id _ => id
    | InductiveDecl id _ => id
    end.

  Fixpoint lookup_env (Σ : global_env) (id : ident) : option global_decl :=
    match Σ with
    | nil => None
    | hd :: tl =>
      if ident_eq id (global_decl_ident hd) then Some hd
      else lookup_env tl id
    end.

  Definition declared_constant (Σ : global_env) (id : ident) decl : Prop :=
    lookup_env Σ id = Some (ConstantDecl id decl).

  Definition declared_minductive Σ mind decl :=
    lookup_env Σ mind = Some (InductiveDecl mind decl).

  Definition declared_inductive Σ mdecl ind decl :=
    declared_minductive Σ (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_constructor Σ mdecl idecl cstr cdecl : Prop :=
    declared_inductive Σ mdecl (fst cstr) idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_projection Σ mdecl idecl (proj : projection) pdecl
  : Prop :=
    declared_inductive Σ mdecl (fst (fst proj)) idecl /\
    List.nth_error idecl.(ind_projs) (snd proj) = Some pdecl /\
    mdecl.(ind_npars) = snd (fst proj).

  (* TODO fix lookup env *)
  Lemma lookup_env_cst_inv {Σ c k cst} :
    lookup_env Σ c = Some (ConstantDecl k cst) -> c = k.
  Proof.
    induction Σ. simpl. discriminate.
    simpl. destruct AstUtils.ident_eq eqn:Heq. intros [= ->]. simpl in Heq.
    now destruct (AstUtils.ident_eq_spec c k). auto.
  Qed.

End Lookup.

Module Type Typing (T : Term).

  Module E := Environment T.

  Import T E.

  Parameter (typing : global_env_ext -> context -> term -> term).

End Typing.