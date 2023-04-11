From MetaCoq.Erasure.Typed Require Import Utils.
From MetaCoq.Erasure.Typed Require Import Erasure.
From MetaCoq.Erasure.Typed Require Import ExAst.
From Equations Require Import Equations.
From MetaCoq.Erasure Require Import EDeps.
From MetaCoq.Erasure Require Import ESubstitution.
From MetaCoq.Erasure Require Import Extract.
From MetaCoq.Erasure Require Import ErasureFunction.
From MetaCoq.PCUIC Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICSR.
From MetaCoq.PCUIC Require Import PCUICTyping.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import Kernames.
From Coq Require Import List.

Import ListNotations.
Import PCUICEnvironment.

Module P := PCUICEnvironment.
Module E := EAst.

Notation "Σ 'p⊢' s ▷ t" := (PCUICWcbvEval.eval Σ s t) (at level 50, s, t at next level) : type_scope.

Local Ltac invert_wf :=
  match goal with
  | [H : wf _ |- _] => inversion H;subst;clear H;cbn in *
  | [H : on_global_env _ _ _ |- _] => inversion H;subst;clear H;cbn in *
  | [H : on_global_decls _ _ _ _ (_ :: _) |- _] => inversion H;subst;clear H;cbn in *
  end.


Lemma map_map_In {X Y Z} xs (f : forall (x : X), In x xs -> Y) (g : Y -> Z) :
  map g (map_In xs f) = map_In xs (fun x isin => g (f x isin)).
Proof.
  induction xs in xs, f |- *; [easy|].
  cbn.
  f_equal.
  apply IHxs.
Qed.

Lemma map_In_ext {X Y : Type} {xs : list X} {f : forall x, In x xs -> Y} g :
  (forall x isin, f x isin = g x isin) ->
  map_In xs f = map_In xs g.
Proof.
  induction xs in xs, f, g |- *; intros all_eq; [easy|].
  cbn.
  f_equal.
  - apply all_eq.
  - apply IHxs.
    intros; apply all_eq.
Qed.

Section ECorrect.

  Existing Instance config.extraction_checker_flags.
  Existing Instance PCUICSN.extraction_normalizing.
  Context {X_type : PCUICWfEnv.abstract_env_impl} {X : projT1 (projT2 X_type)}.
  Context {normalising_in:
    forall Σ : global_env_ext, wf_ext Σ -> PCUICWfEnv.abstract_env_ext_rel X Σ -> PCUICSN.NormalizationIn Σ}.

Lemma erase_ind_body_correct Σ wfΣ kn mib oib wf :
  erases_one_inductive_body oib (trans_oib (@erase_ind_body X_type X _ _ Σ wfΣ kn mib oib wf)).
Proof.
  unfold erases_one_inductive_body, trans_oib, erase_ind_body; simpl.
  apply and_assoc.
  split; [|intuition auto].
  split.
  - unfold trans_ctors.
    rewrite map_map_In.
    unshelve erewrite (map_In_ext (fun x _ => (mkConstructor (cstr_name x) (cstr_arity x)))) by (now intros; destruct decompose_arr).
    induction ind_ctors; [now constructor|].
    constructor; [easy|].
    apply IHl.
  - induction P.ind_projs; [now constructor|].
    cbn.
    constructor; [easy|].
    apply IHl.
  - destruct wf as [(i & [])].
    unfold isPropositionalArity.
    rewrite ind_arity_eq.
    now rewrite !destArity_it_mkProd_or_LetIn.
Qed.

Lemma erase_ind_correct Σ wfΣ kn mib wf :
  erases_mutual_inductive_body mib (trans_mib (@erase_ind X_type X _ _ Σ wfΣ kn mib wf)).
Proof.
  unfold trans_mib, erase_ind.
  cbn.
  split; [|easy].
  cbn.
  generalize (Erasure.erase_ind_obligation_1 Σ kn mib wf).
  intros wfobl.
  induction P.ind_bodies; [constructor|].
  cbn in *.
  constructor; auto.
  apply erase_ind_body_correct.
Qed.

End ECorrect.

Opaque erase_type flag_of_type ErasureFunction.wf_reduction.
Lemma erase_global_decls_deps_recursive_correct decls univs retro wfΣ include ignore_deps :
  let Σ := mk_global_env univs decls retro in
  (forall k, ignore_deps k = false) ->
  (forall k, KernameSet.In k include -> P.lookup_env Σ k <> None) ->
  includes_deps Σ (trans_env (erase_global_decls_deps_recursive decls univs retro wfΣ include ignore_deps)) include.
Proof.
  cbn.
  cut (is_true (KernameSet.subset include include)); [|now apply KernameSet.subset_spec].
  generalize include at 1 3 5 as include'.
  intros include' sub no_ignores all_in.
  induction decls as [|(kn, decl) Σ0 IH] in univs, decls, retro, wfΣ, all_in, include, include', sub |- *.
  { intros kn isin. cbn.
    now apply all_in in isin. }
  simpl in *.
  match goal with
  | |- context[erase_global_decl _ ?wfΣarg _ _ ?wfdeclarg] =>
      set (wfΣext := wfΣarg) in *; clearbody wfΣext;
        set (wfdecl := wfdeclarg) in *; clearbody wfdecl
  end.
  match goal with
  | |- context[erase_global_decls_deps_recursive _ _ _ ?wfΣarg] =>
    set (wfΣprev := wfΣarg) in *; clearbody wfΣprev
  end.

  destruct wfΣ as [wfΣ].
  rewrite no_ignores;cbn.
  destruct KernameSet.mem eqn:mem; cycle 1.
  - intros kn' isin.
    change {| P.universes := univs; P.declarations := (kn, decl) :: Σ0; P.retroknowledge := retro |} with
      (add_global_decl {| P.universes := univs; P.declarations := Σ0; P.retroknowledge := retro|} (kn, decl)).
    apply global_erases_with_deps_weaken; auto.
    eapply IH; eauto.
    intros k kisin.
    specialize (all_in _ kisin).
    unfold eq_kername in *.
    apply KernameSet.subset_spec in sub.
    apply sub in kisin.
    apply KernameSet.mem_spec in kisin.
    destruct (Kername.reflect_kername) as [k_eq H].
    destruct (H k kn);congruence.
  - cbn in *.
    intros k isin.
    destruct (Kername.eq_dec k kn) as [->|]; cycle 1.
    { change {| P.universes := univs; P.declarations := (kn, decl) :: Σ0; P.retroknowledge := retro |} with
      (add_global_decl {| P.universes := univs; P.declarations := Σ0; P.retroknowledge := retro |} (kn, decl)).
      apply global_erases_with_deps_cons; auto.
      eapply (IH _ _ wfΣprev _ (KernameSet.singleton k)).
      - apply KernameSet.subset_spec.
        intros ? ?.
        eapply KernameSet.singleton_spec in H; subst a.
        apply KernameSet.union_spec.
        right.
        apply KernameSet.subset_spec in sub.
        now apply sub.
      - specialize (all_in _ isin).
        intros isink <-%KernameSet.singleton_spec.
        apply KernameSet.mem_spec in isin.
        unfold eq_kername in *.
        destruct (Kername.reflect_kername) as [k_eq H].
        destruct (H isink kn);congruence.

      - now apply KernameSet.singleton_spec. }

    cbn.
    destruct decl; [left|right].
    all: unfold declared_constant, declared_minductive,
         P.declared_constant, P.declared_minductive; cbn.
    all: unfold eq_kername in *.
    all: try rewrite eq_kername_refl.
    + eexists; split; [left;reflexivity|].
      unfold erase_constant_decl.
      destruct flag_of_type; cbn in *.
      destruct conv_ar; cbn in *.
      destruct wfΣprev as [wfΣprev].
      * destruct c eqn:Hc; cbn in *.
        destruct cst_body0 eqn:Hcb; cbn in *; cycle 1.
        { eexists; split;cbn; unfold EGlobalEnv.declared_constant;cbn.
          now rewrite eq_kername_refl. cbn.
          intuition congruence. }

        eexists. split;cbn; unfold EGlobalEnv.declared_constant;cbn.
        now rewrite eq_kername_refl.
        split; last first.
        { intros ? H.
          noconf H.
          constructor. }

        destruct wfdecl as [wfdecl].
        destruct c0 as [ctx univ [r]].
        destruct r.
        apply @type_reduction with (B := mkNormalArity ctx univ) in wfdecl; eauto.
        cbn in *.
        constructor.
        eapply (Is_type_extends (({| P.universes := univs; P.declarations := Σ0; P.retroknowledge := retro |}, _))).
        constructor.
        2: now eauto.
        2:{ eapply extends_decls_extends_subrel, strictly_extends_decls_extends_decls.
           unfold strictly_extends_decls; trea. eexists. cbn; auto. eexists [_].
           cbn. reflexivity. reflexivity. } eauto.
        eexists.
        split; [eassumption|].
        left.
        apply isArity_mkNormalArity.
      * eexists; split;cbn; unfold EGlobalEnv.declared_constant;cbn.
          now rewrite eq_kername_refl.
        unfold trans_cst; cbn.
        destruct c; cbn in *.
        destruct cst_body0; cbn in *; cycle 1.
        { intuition congruence. }

        match goal with
        | |- context[erase _ _ _ _ ?p] =>
          set (twt := p) in *; clearbody twt
        end.
        destruct wfdecl as [wfdecl].
        split.
        -- apply @type_reduction with (B := cst_type0) in wfdecl as wfdecl1; eauto.
           2: repeat invert_wf;split;auto;split;auto.
           eapply (erases_extends (_, _)).
           2: now eauto.
           1: repeat invert_wf;split;auto;split;auto.
           1: repeat invert_wf;split;auto.
           2: { eexists. reflexivity. eexists [_]; reflexivity. reflexivity. }
           1: constructor;auto.
           now apply erases_erase.
        -- intros.
           noconf H.
           destruct wfΣext.
           assert (unfold_add_gd : forall univs decls (decl : kername × global_decl),
                      add_global_decl (mk_global_env univs decls retro) decl = {| P.universes := univs; P.declarations := decl :: decls; P.retroknowledge := retro |}) by reflexivity.
           rewrite <- unfold_add_gd.
           repeat invert_wf.
           apply erases_deps_cons;eauto;cbn in *.
           constructor;eauto.
           eapply (@erase_global_erases_deps (_, _)); eauto.
           { now apply erases_erase. }
           eapply IH.
           ++ apply KernameSet.subset_spec.
              intros ? isin'.
              apply KernameSet.union_spec; left.
              now apply KernameSet.union_spec; right.
           ++ intros ? isin'.
              eapply term_global_deps_spec in isin' as [(? & ?)]; eauto.
              ** cbn in *. congruence.
              ** now apply erases_erase.
    + eexists _, _; split; [left; reflexivity|]; split.
      unfold EGlobalEnv.declared_minductive;cbn.
      now rewrite eq_kername_refl.
      cbn in *.
      apply erase_ind_correct.
Qed.
