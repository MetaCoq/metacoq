(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template
Require Import config Universes monad_utils utils BasicAst AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICInduction.
Require Import String.
Require Import ssreflect.
Local Open Scope string_scope.
Set Asymmetric Patterns.

(* Require Import Equations.Type.DepElim. *)

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
  | nf_fix mfix idx : All (compose (normal (Γ ,,, PCUICLiftSubst.fix_context mfix)) dbody) mfix ->
                      All (compose (normal Γ) dtype) mfix ->
                      normal Γ (tFix mfix idx)
  | nf_cofix mfix idx : All (compose (normal (Γ ,,, PCUICLiftSubst.fix_context mfix)) dbody) mfix ->
                      All (compose (normal Γ) dtype) mfix ->
                        normal Γ (tCoFix mfix idx)

  with neutral (Γ : context) : term -> Prop :=
  | ne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      neutral Γ (tRel i)
  | ne_var v : neutral Γ (tVar v)
  | ne_evar n l : All (normal Γ) l -> neutral Γ (tEvar n l)
  | ne_const c u decl :
      lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None ->
      neutral Γ (tConst c u)
  | ne_app f v : neutral Γ f -> normal Γ v -> neutral Γ (tApp f v)
  | ne_case i p c brs : neutral Γ c -> normal Γ p -> All (compose (normal Γ) snd) brs ->
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
      lookup_env Σ c = Some (ConstantDecl decl) ->
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


Hint Constructors normal neutral.

Derive Signature for normal.
Derive Signature for neutral.
Derive Signature for All.

Local Ltac inv H := inversion H; subst; clear H.

Lemma normal_nf Σ Γ t t' : normal Σ Γ t \/ neutral Σ Γ t -> red1 Σ Γ t t' -> False.
Proof.
  intros. induction X using red1_ind_all; destruct H.
  all: repeat match goal with
         | [ H : normal _ _ (?f ?a) |- _ ] => depelim H
         | [ H : neutral _ _ (?f ?a)|- _ ] => depelim H
         end.
  all: try congruence.
  Ltac help := try repeat match goal with
                  | [ H0 : _ = mkApps _ _ |- _ ] => 
                    eapply (f_equal decompose_app) in H0;
                      rewrite !decompose_app_mkApps in H0; cbn in *; firstorder congruence
                  | [ H1 : tApp _ _ = mkApps _ ?args |- _ ] =>
                    destruct args using rev_ind; cbn in *; [ inv H1 |
                                                             rewrite <- mkApps_nested in H1; cbn in *; inv H1
                                                    ]
                  | [ H0 : mkApps _ _ = _ |- _ ] => symmetry in H0
                         end.
  all: help.
  all: try tauto.
  all: try now (clear - H; depind H; help; eauto).
  - destruct args using rev_ind; cbn in ; [ inv x |
                                             rewrite <- mkApps_nested in x; cbn in *; inv x ].
    destruct narg; inv H2.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply IHX. left.
    eapply nf_cstrapp. now eapply All_app in H as [H _].
  - eapply IHX. left.
    eapply nf_indapp. now eapply All_app in H as [H _].
  - eapply IHX. left.
    eapply All_app in H as [_ H]. now inv H.
  - eapply IHX. left.
    eapply All_app in H as [_ H]. now inv H.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X. 2:exact H.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X. 2:exact H0.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X. 2:exact H.
    eapply OnOn2_contra; try eassumption.
    firstorder.
Qed.

Lemma normal_mk_Apps_inv:
  forall (Σ : global_env) (Γ : context) (t : term) (v : list term), ~ isApp t -> normal Σ Γ (mkApps t v) -> normal Σ Γ t /\ Forall (normal Σ Γ) v.
Proof.
  intros Σ Γ t v H H1.
  induction v using rev_ind.
  - split. eapply H1. econstructor. 
  - rewrite <- mkApps_nested in H1. cbn in H1. depelim H1. depelim H0.
    + split.
      * firstorder.
      * eapply app_Forall. firstorder. firstorder.
    + change (tApp (mkApps t v) x0) with (mkApps (mkApps t v) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      split. eapply nf_cstrapp with (v := []). econstructor.
      now eapply All_Forall. 
    + change (tApp (mkApps t v) x0) with (mkApps (mkApps t v) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      split. eapply nf_indapp with (v := []). econstructor.
      now eapply All_Forall.
Qed.

Lemma normal_mkApps Σ Γ t v :
  neutral Σ Γ t -> Forall (normal Σ Γ) v -> normal Σ Γ (mkApps t v).
Proof.
  intros. induction H0 in t, H |- *; cbn in *.
  - eauto.
  - eapply IHForall. eauto.
Qed.  

Hint Resolve normal_mkApps All_Forall.

Definition normal_neutral_dec Σ Γ t : ({normal Σ Γ t} + {~ (normal Σ  Γ t)}) * ({neutral Σ Γ t} + {~ (neutral Σ Γ t)}).
Proof.
  induction t using term_forall_mkApps_ind in Γ |- *; split; eauto.
  all: try now (right; intros H; depelim H).
  - destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
    + right. intros H. depelim H. depelim H. congruence. help. help.
    + eauto.
    + right. intros H. depelim H. depelim H. congruence. help. help.
  - destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
    + right. intros H. depelim H. congruence.
    + eauto.
    + right. intros H. depelim H. congruence.
  - todo "evar".
  - todo "evar".
  - destruct (IHt1 Γ) as [[] _];
      [destruct (IHt2 (Γ,, vass n t1)) as [[] _]|]; eauto.
    + right. intros H. depelim H. depelim H. eauto. help. help.
    + right. intros H. depelim H. depelim H. eauto. help. help.
  - destruct (IHt1 Γ) as [[] _];
      [destruct (IHt2 (Γ,, vass n t1)) as [[] _]|]; eauto.
    + right. intros H. depelim H. depelim H. eauto. help. help.
    + right. intros H. depelim H. depelim H. eauto. help. help.
  - right. intros H. depelim H. depelim H. help. help.
  - destruct (IHt Γ) as [[] _].
    + destruct dec_All with (P := (normal Σ Γ)) (L := v).
      -- eapply All_impl. eassumption. intros ? ?. apply H1.
      -- destruct t. all:eauto using normal_mkApps, All_Forall.
         all: try now (left; depelim n; help; eauto).
         ++ todo "move to neutral".
         ++ todo "move to neutral".
         ++ destruct v as [ | ? v].
            ** eauto.
            ** right. intros ?. eapply normal_nf. left; exact H1.
               cbn. todo "fact on red1".
         ++ todo "check narg".
         ++ todo "check narg".
      -- right. intros ?. eapply f. eapply Forall_All.
         now eapply normal_mk_Apps_inv.
    + right. intros ?. eapply n. now eapply normal_mk_Apps_inv.
  - destruct v using rev_ind.
    + cbn. eapply IHt.
    + rewrite <- mkApps_nested. cbn.
      eapply All_app in H0 as []. eapply IHv in a. inv a0. clear H3.
      rename H2 into IHt2.
      revert a.
      generalize (mkApps t v) as t1. intros t1 IHt1.
      destruct (IHt1) as [];
      [destruct (IHt2 Γ) as [[] _]|]; eauto.
      * right. intros HH. depelim HH. eauto.
      * right. intros HH. depelim HH. eauto.
  - destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. depelim H. congruence. help. help.
      * destruct (string_dec s k). subst. left. eauto.
        right. intros H. depelim H. depelim H. congruence. help. help.
    +   right. intros H. depelim H. depelim H. congruence. help. help.
    +   right. intros H. depelim H. depelim H. congruence. help. help.
  - destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. congruence.
      * destruct (string_dec s k). subst. left. eauto.
        right. intros H. depelim H. congruence.
    +   right. intros H. depelim H. congruence.
    +   right. intros H. depelim H. congruence.
  - left. eapply nf_indapp with (v := []). econstructor.
  - left. eapply nf_cstrapp with (v := []). econstructor.
  - todo "case".
  - todo "case".
  - destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. depelim H. eauto. help. help.
  - destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. eauto.
  - hnf in X.

    destruct dec_All with (P := (normal Σ Γ ∘ dtype)) (L := m).
    eapply All_impl. eassumption. cbn. intros. eapply H.

    destruct dec_All with (P := normal Σ  (Γ ,,, PCUICLiftSubst.fix_context m) ∘ dbody) (L := m).
    eapply All_impl. exact X. cbn. intros. eapply H.

    + left. eapply nf_fix. eauto. eauto.
    + right. intros H. depelim H. depelim H. help. help. eauto.
    + right. intros H. depelim H. depelim H. help. help. eauto.
  - hnf in X.

    destruct dec_All with (P := (normal Σ Γ ∘ dtype)) (L := m).
    eapply All_impl. eassumption. cbn. intros. eapply H.

    destruct dec_All with (P := normal Σ (Γ ,,, PCUICLiftSubst.fix_context m) ∘ dbody) (L := m).
    eapply All_impl. exact X. cbn. intros. eapply H.

    + left. eapply nf_cofix. eauto. eauto.
    + right. intros H. depelim H. depelim H. help. help. eauto.
    + right. intros H. depelim H. depelim H. help. help. eauto.
      Unshelve. repeat econstructor.
Defined.

Definition normal_dec Σ Γ t := fst (normal_neutral_dec Σ Γ t).
Definition neutral_dec Σ Γ t := snd (normal_neutral_dec Σ Γ t).
