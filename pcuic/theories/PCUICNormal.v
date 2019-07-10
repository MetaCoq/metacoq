(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template
Require Import config Universes monad_utils utils BasicAst AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping.
Require Import String.
Require Import ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Module RedFlags.

  Record t := mk {
    beta   : bool ;
    iota   : bool ;
    zeta   : bool ;
    delta  : bool ;
    fix_   : bool ;
    cofix_ : bool
  }.

  Definition default := mk true true true true true true.

End RedFlags.

Section Normal.

  Context (flags : RedFlags.t).
  Context (Σ : global_env).

  Inductive normal (Γ : context) : term -> Prop :=
  | nf_ne t : neutral Γ t -> normal Γ t
  | nf_sort s : normal Γ (tSort s)
  | nf_prod na A B : normal Γ A -> normal (Γ ,, vass na A) B ->
                     normal Γ (tProd na A B)
  | nf_lam na A B : normal Γ A -> normal (Γ ,, vass na A) B ->
                    normal Γ (tLambda na A B)
  | nf_cstrapp i n u v : All (normal Γ) v -> normal Γ (mkApps (tConstruct i n u) v)
  | nf_indapp i u v : All (normal Γ) v -> normal Γ (mkApps (tInd i u) v)
  | nf_fix mfix idx : All (compose (normal Γ) dbody) mfix ->
                      normal Γ (tFix mfix idx)
  | nf_cofix mfix idx : All (compose (normal Γ) dbody) mfix ->
                        normal Γ (tCoFix mfix idx)

  with neutral (Γ : context) : term -> Prop :=
  | ne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      neutral Γ (tRel i)
  | ne_var v : neutral Γ (tVar v)
  | ne_evar n l : neutral Γ (tEvar n l)
  | ne_const c u decl :
      lookup_env Σ c = Some (ConstantDecl c decl) -> decl.(cst_body) = None ->
      neutral Γ (tConst c u)
  | ne_app f v : neutral Γ f -> normal Γ v -> neutral Γ (tApp f v)
  | ne_case i p c brs : neutral Γ c -> Forall (compose (normal Γ) snd) brs ->
                        neutral Γ (tCase i p c brs)
  | ne_proj p c : neutral Γ c -> neutral Γ (tProj p c).

  (* Relative to reduction flags *)
  Inductive whnf (Γ : context) : term -> Prop :=
  | whnf_ne t : whne Γ t -> whnf Γ t
  | whnf_sort s : whnf Γ (tSort s)
  | whnf_prod na A B : whnf Γ (tProd na A B)
  | whnf_lam na A B : whnf Γ (tLambda na A B)
  | whnf_cstrapp i n u v : whnf Γ (mkApps (tConstruct i n u) v)
  | whnf_indapp i u v : whnf Γ (mkApps (tInd i u) v)
  | whnf_fix mfix idx : whnf Γ (tFix mfix idx)
  | whnf_cofix mfix idx : whnf Γ (tCoFix mfix idx)

  with whne (Γ : context) : term -> Prop :=
  | whne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      whne Γ (tRel i)

  | whne_rel_nozeta i :
      RedFlags.zeta flags = false ->
      whne Γ (tRel i)

  | whne_var v :
      whne Γ (tVar v)

  | whne_evar n l :
      whne Γ (tEvar n l)

  | whne_letin_nozeta na B b t :
      RedFlags.zeta flags = false ->
      whne Γ (tLetIn na B b t)

  | whne_const c u decl :
      lookup_env Σ c = Some (ConstantDecl c decl) ->
      decl.(cst_body) = None ->
      whne Γ (tConst c u)

  | whne_const_nodelta c u :
      RedFlags.delta flags = false ->
      whne Γ (tConst c u)

  | whne_app f v :
      whne Γ f ->
      whne Γ (tApp f v)

  | whne_case i p c brs :
      whne Γ c ->
      whne Γ (tCase i p c brs)

  | whne_case_noiota i p c brs :
      RedFlags.iota flags = false ->
      whne Γ (tCase i p c brs)

  | whne_proj p c :
      whne Γ c ->
      whne Γ (tProj p c)

  | whne_proj_noiota p c :
      RedFlags.iota flags = false ->
      whne Γ (tProj p c).

  Lemma whne_mkApps :
    forall Γ t args,
      whne Γ t ->
      whne Γ (mkApps t args).
  Proof.
    intros Γ t args h.
    induction args in t, h |- *.
    - assumption.
    - simpl. eapply IHargs. econstructor. assumption.
  Qed.

  Lemma whne_mkApps_inv :
    forall Γ t l,
      whne Γ (mkApps t l) ->
      whne Γ t.
  Proof.
    intros Γ t l h.
    induction l in t, h |- *.
    - assumption.
    - simpl in h. apply IHl in h. inversion h. assumption.
  Qed.

End Normal.