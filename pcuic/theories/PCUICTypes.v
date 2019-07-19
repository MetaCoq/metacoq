(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Equations Require Import Equations.
Require Import Equations.Tactics.
From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia CRelationClasses.
From MetaCoq Require Import LibHypsNaming.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICParallelReduction PCUICEquality
     PCUICValidity PCUICParallelReductionConfluence PCUICConfluence
     PCUICContextConversion
     PCUICConversion PCUICInversion PCUICPrincipality.

Require Import ssreflect ssrbool.
Require Import String.
Set Asymmetric Patterns.
Set SimplIsCbn.

Inductive is_type {cf : checker_flags} (Σ : global_env_ext) (Γ : context) : term -> Type :=
| is_type_Rel i d :
    nth_error Γ i = Some d ->
    is_type Σ Γ d.(decl_type) ->
    is_type Σ Γ (tRel i)

| is_type_Sort s : is_type Σ Γ (tSort s)

| is_type_Prod na dom codom :
    is_type Σ Γ dom -> is_type Σ (Γ ,, vass na dom) codom ->
    is_type Σ Γ (tProd na dom codom)

| is_type_LetIn na b B t :
    is_type Σ Γ B -> is_type Σ (Γ ,, vdef na b B) t ->
    is_type Σ Γ (tLetIn na b B t)

| is_type_App f u na dom codom :
    Σ ;;; Γ |- f : tProd na dom codom ->
    Σ ;;; Γ |- u : dom ->
    is_type Σ Γ (codom {0 := u}) ->
    is_type Σ Γ (tApp f u)

| is_type_Const c u decl :
    declared_constant Σ c decl ->
    is_type Σ Γ (subst_instance_constr u decl.(cst_type)) ->
    is_type Σ Γ (tConst c u)

| is_type_Ind i u : is_type Σ Γ (tInd i u)

| is_type_Case indp p c brs :
    is_type Σ Γ p ->
    is_type Σ Γ (tCase indp p c brs)

| is_type_Proj p c u mdecl idecl pdecl args :
    declared_projection Σ.1 mdecl idecl p pdecl ->
    Σ;;; Γ |- c : mkApps (tInd p.1.1 u) args ->
    is_type Σ Γ (subst_instance_constr u pdecl.2) ->
    is_type Σ Γ (tProj p c)

| is_type_Fix mfix n decl :
    nth_error mfix n = Some decl ->
    is_type Σ Γ decl.(dtype) ->
    is_type Σ Γ (tFix mfix n)

| is_type_Cumul T T' :
    is_type Σ Γ T ->
    isWfArity_or_Type Σ Γ T' ->
    Σ ;;; Γ |- T <= T' ->
    is_type Σ Γ T'

| is_type_Cumul_inv T T' :
    is_type Σ Γ T' ->
    isWfArity_or_Type Σ Γ T ->
    Σ ;;; Γ |- T <= T' ->
    is_type Σ Γ T.

(* cofixpoints always produce a value in the coinductive type:
   they cannot be types *)

Lemma inversion_type_Sort {cf : checker_flags} (Σ : global_env_ext) (Γ : context) T s :
  Σ ;;; Γ |- T : tSort s -> ∑ ctx ty, (Σ ;;; Γ |- T : ty) * (Σ ;;; Γ |- ty <= it_mkProd_or_LetIn ctx (tSort s)).
Proof.
  intros.
  exists [], (tSort s).
  split; auto.
Qed.

Lemma isType_red {cf : checker_flags} (Σ : global_env_ext) (Γ : context) T T' :
  isWfArity_or_Type Σ Γ T ->
  red Σ Γ T T' -> is_type Σ Γ T' -> is_type Σ Γ T.
Proof.
  intros.
Admitted.

Lemma smash_context_app Γ Γ' Γ'' :
  smash_context Γ (Γ' ++ Γ'') =
  smash_context (smash_context Γ Γ') Γ''.
Proof.
  induction Γ' in Γ, Γ'' |- *; simpl; auto.
  destruct a as [na [b|] ty].
  now rewrite -IHΓ'.
  now rewrite -IHΓ'.
Qed.

(* Lemma smash_context_subst Γ s Γ' n : *)
(*   closedn_ctx #|Γ| Γ' -> *)
(*                    smash_context Γ (subst_context s (#|Γ| + n) Γ') = *)
(*                    subst_context s (#|Γ| + n) (smash_context Γ Γ'). *)
(* Proof. *)
(*   induction Γ' in Γ, s, n |- *; cbn -[subst_context]. simpl. *)
(*   admit. *)
(*   intros Hs. *)
(*   destruct a as [na [b|] ty]; cbn -[subst_context]. *)
(*   - rewrite subst_context_snoc. simpl. *)
(*     specialize (IHΓ' (subst_context [b] 0 Γ) s). *)
(*     rewrite subst_context_length in IHΓ'. *)
(*     rewrite mapi_rec_app /= forallb_app /= /id /closed_decl /= in Hs. *)
(*     move/andP: Hs => [] closedctx. move => /andP [/andP[Hb Hty] _]. *)
(*     rewrite -IHΓ'; auto. *)
(*     assert (subst s (#|Γ'| + (#|Γ| + n)) b = b). *)
(*     eapply subst_closedn. *)
(*     eapply closed_upwards; eauto. now rewrite List.rev_length. *)
(*     now rewrite H. *)
(*   - rewrite subst_context_snoc. simpl. *)
(*     rewrite mapi_rec_app /= forallb_app /= /id /closed_decl /= in Hs. *)
(*     move/andP: Hs => [] closedctx. move => /andP [Hty _]. *)
(*     specialize (IHΓ' (Γ ++ [subst_decl s (#|Γ'| + (#|Γ| + n)) *)
(*                                        {| decl_name := na; decl_body := None; decl_type := ty |}])). *)
(*     rewrite app_length /= in IHΓ'. *)
(*     specialize (IHΓ' s n); auto. *)
(*     rewrite Nat.add_1_r in IHΓ'. *)
(* Admitted. (* Wrong! *) *)

Lemma cumul_it_mkProd_or_LetIn_r_inv {cf : checker_flags} (Σ : global_env_ext) Γ T ctx' s' :
  wf Σ ->
  Σ ;;; Γ |- T <= it_mkProd_or_LetIn ctx' (tSort s') ->
  ∑ ctx s, (red Σ Γ T (it_mkProd_or_LetIn ctx (tSort s)))
           * conv_context Σ ctx (smash_context [] ctx')
           * leq_term Σ (tSort s) (tSort s').
Proof.
  intros wfΣ.
  revert Γ T s'.
  generalize (@eq_refl _ #|ctx'|).
  move: {2}#|ctx'| => n; move: ctx'.
  induction n.
  - case=> //=; rewrite /=. move=> _ Γ T s'.
    move/cumul_Sort_r_inv => [s [? ?]].
    exists [], s. simpl. intuition auto with pcuic. now constructor.
  - destruct ctx' using rev_ind => //= /=. clear IHctx'.
    rewrite app_length /= Nat.add_1_r => [=] Hn Γ T s'. subst n.
    rewrite it_mkProd_or_LetIn_app /=.
    case: x => [na [b|] ty] => /= H.
    * eapply cumul_LetIn_r_inv in H as [T' [redT' cum]] => //.
      rewrite /subst1 subst_it_mkProd_or_LetIn /= in cum.
      specialize (IHn (subst_context [b] 0 l) ltac:(now rewrite subst_context_length) _ _ _ cum) as
          [ctx' [s'' [[redT'' convctx] leq]]]; auto.
      exists ctx', s''. intuition auto.
      eapply transitivity; eauto.
      eapply conv_context_trans; eauto.
      rewrite smash_context_app. simpl.
      (* rewrite smash_context_subst. *)
      admit.
    * eapply cumul_Prod_r_inv in H as [na' [dom' [codom' [[reddom eqcodom] ?]]]] => //.
      destruct (IHn l eq_refl (Γ ,, vass na ty) _ _ c) as [ctx' [s'' [[redT' convctx'] leqs]]].
      exists (ctx' ++ [vass na' dom']), s''.
      rewrite it_mkProd_or_LetIn_app. simpl.
      intuition auto. transitivity (tProd na' dom' codom') => //.
      eapply red_prod_r.
      admit.
      admit.
Admitted.

Lemma is_type_sound {cf : checker_flags} (Σ : global_env_ext) (Γ : context) T :
  wf Σ ->
  isType Σ Γ T -> is_type Σ Γ T.
Proof.
  intros wfΣ [s Hs].
  eapply inversion_type_Sort in Hs as [ctx [U [HU Us]]].
  revert s ctx Us. induction HU; intros s' Us; try solve [econstructor; eauto].
  - econstructor; eauto.
    destruct decl as [na d ty]; try discriminate.
    simpl in Us. simpl in Us0.
    (* eapply cumul_Sort_r_inv in Us as [s [reds ?]]. simpl. *)
    (* eapply is_type_Cumul with (tSort s). constructor; auto. admit. *)
    admit.
Admitted.

(*   - now eapply cumul_Prod_Sort_inv in Us. *)

(*   - constructor. eapply IHHU1; eauto. *)
(*     eapply IHHU3 with s'. admit. *)

(*   - eapply is_type_App; eauto. *)
(*     eapply is_type_Cumul_inv; eauto. constructor. admit. *)

(*   - econstructor. eauto. *)
(*     eapply is_type_Cumul_inv; eauto. constructor. admit. *)

(*   - admit. (* Impossible *) *)
(*   - eapply on_declared_inductive in isdecl as [onm oni] => //. *)
(*     destruct oni. *)
(*     assert (pty = it_mkProd_or_LetIn pctx (tSort ps)). *)
(*     move: e0; rewrite /types_of_case. *)
(*     case ip: instantiate_params => [ity|] //. *)
(*     case da: destArity => [[ctx isort]|] //. *)
(*     case dp: destArity => [[pctx' psort]|] //. *)
(*     case moo: map_option_out => [brtys|] // [] ? ? ? ?; subst. *)
(*     generalize (destArity_spec [] pty). now rewrite dp. *)
(*     subst pty. *)
(*     eapply is_type_Case. eapply IHHU1 with ps. *)
(*     assert (tSort ps <= tSort s'). *)




(*     Lemma types_of_case_pty *)


(*     red in c0. *)
(*     admit. *)

(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(*   - eapply IHHU. *)
(*     eapply transitivity; eauto. *)
(* Admitted. *)