(* Distributed under the terms of the MIT license.   *)
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICConversion PCUICGeneration.
Require Import ssreflect ssrbool.
Require Import String.
From MetaCoq Require Import LibHypsNaming.
Local Open Scope string_scope.
Set Asymmetric Patterns.
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Set Equations With UIP.

Section Inversion.

  Context `{checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Ltac insum :=
    match goal with
    | |- ∑ x : _, _ =>
      eexists
    end.

  Ltac intimes :=
    match goal with
    | |- _ × _ =>
      split
    end.

  Ltac outsum :=
    match goal with
    | ih : ∑ x : _, _ |- _ =>
      destruct ih as [? ?]
    end.

  Ltac outtimes :=
    match goal with
    | ih : _ × _ |- _ =>
      destruct ih as [? ?]
    end.

  Ltac invtac h :=
    dependent induction h ; [
      repeat insum ;
      repeat intimes ;
      [ first [ eassumption | reflexivity ] .. | eapply cumul_refl' ]
    | repeat outsum ;
      repeat outtimes ;
      repeat insum ;
      repeat intimes ;
      [ first [ eassumption | reflexivity ] ..
      | eapply cumul_trans ; eassumption ]
    ].

  Derive Signature for typing.

  Lemma inversion_Rel :
    forall {Γ n T},
      Σ ;;; Γ |- tRel n : T ->
      ∑ decl,
        wf_local Σ Γ ×
        (nth_error Γ n = Some decl) ×
        Σ ;;; Γ |- lift0 (S n) (decl_type decl) <= T.
  Proof.
    intros Γ n T h. invtac h.
  Qed.

  Lemma inversion_Var :
    forall {Γ i T},
      Σ ;;; Γ |- tVar i : T -> False.
  Proof.
    intros Γ i T h. dependent induction h. assumption.
  Qed.

  Lemma inversion_Evar :
    forall {Γ n l T},
      Σ ;;; Γ |- tEvar n l : T -> False.
  Proof.
    intros Γ n l T h. dependent induction h. assumption.
  Qed.

  Lemma inversion_Sort :
    forall {Γ s T},
      Σ ;;; Γ |- tSort s : T ->
      ∑ l,
        wf_local Σ Γ ×
        LevelSet.In l (global_ext_levels Σ) ×
        (s = Universe.make l) ×
        Σ ;;; Γ |- tSort (Universe.super l) <= T.
  Proof.
    intros Γ s T h. invtac h.
  Qed.

  Lemma inversion_Prod :
    forall {Γ na A B T},
      Σ ;;; Γ |- tProd na A B : T ->
      ∑ s1 s2,
        Σ ;;; Γ |- A : tSort s1 ×
        Σ ;;; Γ ,, vass na A |- B : tSort s2 ×
        Σ ;;; Γ |- tSort (Universe.sort_of_product s1 s2) <= T.
  Proof.
    intros Γ na A B T h. invtac h.
  Qed.

  Lemma inversion_Lambda :
    forall {Γ na A t T},
      Σ ;;; Γ |- tLambda na A t : T ->
      ∑ s B,
        Σ ;;; Γ |- A : tSort s ×
        Σ ;;; Γ ,, vass na A |- t : B ×
        Σ ;;; Γ |- tProd na A B <= T.
  Proof.
    intros Γ na A t T h. invtac h.
  Qed.

  Lemma inversion_LetIn :
    forall {Γ na b B t T},
      Σ ;;; Γ |- tLetIn na b B t : T ->
      ∑ s1 A,
        Σ ;;; Γ |- B : tSort s1 ×
        Σ ;;; Γ |- b : B ×
        Σ ;;; Γ ,, vdef na b B |- t : A ×
        Σ ;;; Γ |- tLetIn na b B A <= T.
  Proof.
    intros Γ na b B t T h. invtac h.
  Qed.

  Lemma inversion_App :
    forall {Γ u v T},
      Σ ;;; Γ |- tApp u v : T ->
      ∑ na A B,
        Σ ;;; Γ |- u : tProd na A B ×
        Σ ;;; Γ |- v : A ×
        Σ ;;; Γ |- B{ 0 := v } <= T.
  Proof.
    intros Γ u v T h. invtac h.
  Qed.

  Lemma inversion_Const :
    forall {Γ c u T},
      Σ ;;; Γ |- tConst c u : T ->
      ∑ decl,
        wf_local Σ Γ ×
        declared_constant Σ c decl ×
        (consistent_instance_ext Σ decl.(cst_universes) u) ×
        Σ ;;; Γ |- subst_instance_constr u (cst_type decl) <= T.
  Proof.
    intros Γ c u T h. invtac h.
  Qed.

  Lemma inversion_Ind :
    forall {Γ ind u T},
      Σ ;;; Γ |- tInd ind u : T ->
      ∑ mdecl idecl,
        wf_local Σ Γ ×
        declared_inductive Σ mdecl ind idecl ×
        consistent_instance_ext Σ (ind_universes mdecl) u ×
        Σ ;;; Γ |- subst_instance_constr u idecl.(ind_type) <= T.
  Proof.
    intros Γ ind u T h. invtac h.
  Qed.

  Lemma inversion_Construct :
    forall {Γ ind i u T},
      Σ ;;; Γ |- tConstruct ind i u : T ->
      ∑ mdecl idecl cdecl,
        wf_local Σ Γ ×
        declared_constructor (fst Σ) mdecl idecl (ind, i) cdecl ×
        consistent_instance_ext Σ (ind_universes mdecl) u ×
        Σ;;; Γ |- type_of_constructor mdecl cdecl (ind, i) u <= T.
  Proof.
    intros Γ ind i u T h. invtac h.
  Qed.

  Lemma inversion_Case :
    forall {Γ ind npar p c brs T},
      Σ ;;; Γ |- tCase (ind, npar) p c brs : T ->
      ∑ u args mdecl idecl pty indctx pctx ps btys,
        declared_inductive Σ mdecl ind idecl ×
        ind_npars mdecl = npar ×
        let pars := firstn npar args in
        Σ ;;; Γ |- p : pty ×
        types_of_case ind mdecl idecl pars u p pty =
        Some (indctx, pctx, ps, btys) ×
        check_correct_arity (global_ext_constraints Σ)
        idecl ind u indctx pars pctx ×
        existsb (leb_sort_family (universe_family ps)) (ind_kelim idecl) ×
        Σ ;;; Γ |- c : mkApps (tInd ind u) args ×
        All2 (fun x y =>
          (fst x = fst y) *
          (Σ ;;; Γ |- snd x : snd y) *
          (Σ ;;; Γ |- snd y : tSort ps)
        ) brs btys ×
        Σ ;;; Γ |- mkApps p (skipn npar args ++ [c]) <= T.
  Proof.
    intros Γ ind npar p c brs T h. invtac h.
  Qed.

  Lemma inversion_Proj :
    forall {Γ p c T},
      Σ ;;; Γ |- tProj p c : T ->
      ∑ u mdecl idecl pdecl args,
        declared_projection Σ mdecl idecl p pdecl ×
        Σ ;;; Γ |- c : mkApps (tInd (fst (fst p)) u) args ×
        #|args| = ind_npars mdecl ×
        let ty := snd pdecl in
        Σ ;;; Γ |- (subst0 (c :: List.rev args)) (subst_instance_constr u ty)
                <= T.
  Proof.
    intros Γ p c T h. invtac h.
  Qed.

  Lemma inversion_Fix :
    forall {Γ mfix n T},
      Σ ;;; Γ |- tFix mfix n : T ->
      ∑ decl,
        let types := fix_context mfix in
        fix_guard mfix ×
        nth_error mfix n = Some decl ×
        wf_local Σ (Γ ,,, types) ×
        All (fun d =>
          Σ ;;; Γ ,,, types |- dbody d : (lift0 #|types|) (dtype d) ×
          isLambda (dbody d) = true
        ) mfix ×
        Σ ;;; Γ |- dtype decl <= T.
  Proof.
    intros Γ mfix n T h. invtac h.
  Qed.

  Lemma inversion_CoFix :
    forall {Γ mfix idx T},
      Σ ;;; Γ |- tCoFix mfix idx : T ->
      ∑ decl,
        allow_cofix ×
        let types := fix_context mfix in
        nth_error mfix idx = Some decl ×
        wf_local Σ (Γ ,,, types) ×
        All (fun d =>
          Σ ;;; Γ ,,, types |- d.(dbody) : lift0 #|types| d.(dtype)
        ) mfix ×
        Σ ;;; Γ |- decl.(dtype) <= T.
  Proof.
    intros Γ mfix idx T h. invtac h.
  Qed.

  Lemma inversion_it_mkLambda_or_LetIn :
    forall {Γ Δ t T},
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ t : T ->
      ∑ A,
        Σ ;;; Γ ,,, Δ |- t : A ×
        Σ ;;; Γ |- it_mkProd_or_LetIn Δ A <= T.
  Proof.
    intros Γ Δ t T h.
    induction Δ as [| [na [b|] A] Δ ih ] in Γ, t, h |- *.
    - eexists. split ; eauto.
    - simpl. apply ih in h. cbn in h.
      destruct h as [B [h c]].
      apply inversion_LetIn in h as hh.
      destruct hh as [s1 [A' [? [? [? ?]]]]].
      exists A'. split ; eauto.
      cbn. eapply cumul_trans ; try eassumption.
      eapply cumul_it_mkProd_or_LetIn.
      assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [B [h c]].
      apply inversion_Lambda in h as hh.
      pose proof hh as [s1 [B' [? [? ?]]]].
      exists B'. split ; eauto.
      cbn. eapply cumul_trans ; try eassumption.
      eapply cumul_it_mkProd_or_LetIn.
      assumption.
  Qed.

End Inversion.

Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
  destArity ctx (it_mkProd_or_LetIn ctx' t) =
  destArity (ctx ,,, ctx') t.
Proof.
  induction ctx' in ctx, t |- *; simpl; auto.
  rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
Qed.
