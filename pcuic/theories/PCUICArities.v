(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List BinPos Compare_dec Arith Lia
     Classes.CRelationClasses ProofIrrelevance ssreflect.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICUnivSubstitution
     PCUICCumulativity PCUICPosition PCUICEquality PCUICNameless
     PCUICNormal PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion
     PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICClosed PCUICSubstitution
     PCUICWeakening PCUICGeneration PCUICUtils PCUICCtxShape PCUICContexts.

From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.

Derive Signature for typing_spine.

Notation isWAT :=
  (lift_typing
    (fun (Σ0 : PCUICEnvironment.global_env_ext) (Γ : context) (_ T : term)
  => isWfArity_or_Type Σ0 Γ T)).

Lemma isArity_it_mkProd_or_LetIn Γ t : isArity t -> isArity (it_mkProd_or_LetIn Γ t).
Proof.
  intros isA. induction Γ using rev_ind; simpl; auto.
  rewrite it_mkProd_or_LetIn_app. simpl; auto.
  destruct x as [? [?|] ?]; simpl; auto.
Qed.

Lemma invert_cumul_arity_l {cf:checker_flags} Σ (Γ : context) (C : term) T :
  wf Σ.1 ->
  Σ;;; Γ |- C <= T ->
  match destArity [] C with
  | Some (ctx, s) =>
    ∑ T' ctx' s', red Σ.1 Γ T T' * (destArity [] T' = Some (ctx', s')) * 
       conv_context Σ (Γ ,,, smash_context [] ctx) (Γ ,,, ctx') * leq_universe
       (global_ext_constraints Σ) s s'
  | None => unit
  end.
Proof.
intros wfΣ CT.
generalize (destArity_spec [] C). destruct destArity as [[ctx p]|].
simpl. intros ->. 2:intros _; exact tt.
revert Γ T CT.
generalize (@le_n #|ctx|).
generalize (#|ctx|) at 2. intros n; revert ctx.
induction n; intros ctx Hlen Γ T HT.
- destruct ctx; simpl in Hlen; try lia.
  eapply invert_cumul_sort_l in HT as [u' [redT leqT]].
  exists (tSort u'), [], u'; intuition auto.
  reflexivity.
- destruct ctx using rev_ind.
  * eapply invert_cumul_sort_l in HT as [u' [redT leqT]].
    exists (tSort u'), [], u'; intuition auto.  
    reflexivity.
  * rewrite it_mkProd_or_LetIn_app in HT; simpl in HT.
    destruct x as [na [b|] ty]; unfold mkProd_or_LetIn in HT; simpl in *.
    + eapply invert_cumul_letin_l in HT; auto.
      unfold subst1 in HT; rewrite subst_it_mkProd_or_LetIn in HT.
      rewrite app_length /= Nat.add_1_r in Hlen.
      simpl in HT. specialize (IHn (subst_context [b] 0 ctx) ltac:(rewrite
      subst_context_length; lia) Γ T HT).
      destruct IHn as [T' [ctx' [s' [[[redT destT] convctx] leq]]]].
      clear IHctx.
      exists T', ctx', s'. intuition auto.
      rewrite smash_context_app. simpl.
      now rewrite -smash_context_subst_empty.
    + eapply invert_cumul_prod_l in HT; auto. 
      rewrite -> app_length in Hlen.
      rewrite Nat.add_1_r in Hlen.
      destruct HT as [na' [A' [B' [[redT convT] HT]]]].
      specialize (IHn ctx ltac:(lia) (Γ ,, vass na' A') B').
      forward IHn. eapply cumul_conv_ctx; eauto.
      constructor; pcuic. clear IHctx.
      destruct IHn as [T' [ctx' [s' [[[redT' destT] convctx] leq]]]].
      exists (tProd na' A' T'), (ctx' ++ [vass na' A'])%list, s'. intuition auto. 2:simpl.
      -- transitivity (tProd na' A' B'); auto.
        eapply red_prod. reflexivity. apply redT'.
      -- now rewrite destArity_app destT.
      -- rewrite smash_context_app /= .
         rewrite !app_context_assoc.
         assert (#|smash_context [] ctx| = #|ctx'|).
         { apply context_relation_length in convctx.
          autorewrite with len in convctx |- *.
          simpl in convctx. simpl. lia. }
        eapply context_relation_app_inv; auto.
        apply context_relation_app in convctx; auto.
        constructor; pcuic.
        eapply context_relation_app in convctx as [_ convctx].
        unshelve eapply (context_relation_impl _ convctx).
        simpl; firstorder. destruct X. constructor.
        eapply conv_conv_ctx; eauto.
        eapply context_relation_app_inv. constructor; pcuic.
        constructor; pcuic. constructor; pcuic. now symmetry.
        apply context_relation_refl. intros.
        destruct x as [na'' [b'|] ty']; constructor; reflexivity.
        constructor; pcuic. 
        eapply conv_conv_ctx; eauto.
        eapply context_relation_app_inv. constructor; pcuic.
        constructor; pcuic. constructor; pcuic. now symmetry.
        apply context_relation_refl. intros.
        destruct x as [na'' [b'|] ty']; constructor; reflexivity.
        constructor; pcuic.
        eapply conv_conv_ctx; eauto.
        eapply context_relation_app_inv. constructor; pcuic.
        constructor; pcuic. constructor; pcuic. now symmetry.
        apply context_relation_refl. intros.
        destruct x as [? [?|] ?]; constructor; reflexivity.
        eapply conv_conv_ctx; eauto.
        eapply context_relation_app_inv. constructor; pcuic.
        constructor; pcuic. constructor; pcuic. now symmetry.
        apply context_relation_refl. intros.
        destruct x as [? [?|] ?]; constructor; reflexivity.
        auto.
Qed.


Lemma destArity_spec_Some ctx T ctx' s :
  destArity ctx T = Some (ctx', s)
  -> it_mkProd_or_LetIn ctx T = it_mkProd_or_LetIn ctx' (tSort s).
Proof.
  pose proof (PCUICClosed.destArity_spec ctx T) as H.
  intro e; now rewrite e in H.
Qed.

Lemma isWAT_tProd {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na A B}
  : isWfArity_or_Type Σ Γ (tProd na A B)
    <~> (isType Σ Γ A × isWfArity_or_Type Σ (Γ,, vass na A) B).
Proof.
  split; intro HH.
  - destruct HH as [[ctx [s [H1 H2]]]|[s H]].
    + cbn in H1. apply destArity_app_Some in H1.
      destruct H1 as [ctx' [H1 HH]]; subst ctx.
      rewrite app_context_assoc in H2. split.
      * apply wf_local_app in H2. inversion H2; subst. assumption.
      * left. exists ctx', s. split; tas.
    + apply inversion_Prod in H; tas. destruct H as [s1 [s2 [HA [HB Hs]]]].
      split.
      * eexists; tea.
      * right. eexists; tea.
  - destruct HH as [HA [[ctx [s [H1 H2]]]|HB]].
    + left. exists ([vass na A] ,,, ctx), s. split.
      cbn. now rewrite destArity_app H1.
      now rewrite app_context_assoc.
    + right. destruct HA as [sA HA], HB as [sB HB].
      eexists. econstructor; eassumption.
Defined.

Lemma isWAT_subst {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ Δ} (HΓ : wf_local Σ (Γ ,,, Δ)) {A} s :
    subslet Σ Γ s Δ ->
    isWfArity_or_Type Σ (Γ ,,, Δ) A -> 
    isWfArity_or_Type Σ Γ (subst0 s A).
Proof.
  intros sub WAT.
  destruct WAT.
  - left.
    destruct i as [ctx [s' [wfa wfl]]].
    exists (subst_context s 0 ctx), s'.
    generalize (subst_destArity [] A s 0).
    rewrite wfa /= => ->.
    split; auto.
    now eapply substitution_wf_local.
  - right.
    destruct i as [s' Hs].
    exists s'. eapply (substitution _ _ Δ s [] _ _ HΣ' sub Hs).
Qed.

Lemma isWAT_subst_gen {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ) {Γ Δ Δ'} {A} s :
  subslet Σ Γ s Δ ->
  isWfArity_or_Type Σ (Γ ,,, Δ ,,, Δ') A -> 
  isWfArity_or_Type Σ (Γ ,,, subst_context s 0 Δ') (subst s #|Δ'| A).
Proof.
  intros sub WAT.
  destruct WAT.
  - left.
    destruct i as [ctx [s' [wfa wfl]]].
    exists (subst_context s #|Δ'|ctx), s'.
    generalize (subst_destArity [] A s #|Δ'|).
    rewrite wfa /=.
    split; auto.
    epose proof (subst_context_app _ 0 _ _).
    rewrite Nat.add_0_r in H0. rewrite <- app_context_assoc, <- H0.
    eapply substitution_wf_local; eauto.
    now rewrite app_context_assoc.
  - right.
    destruct i as [s' Hs].
    exists s'. eapply (substitution _ _ Δ s _ _ _ HΣ' sub Hs).
Qed.

Lemma typing_spine_letin_inv {cf:checker_flags} {Σ Γ na b B T args S} : 
  wf Σ.1 ->
  typing_spine Σ Γ (tLetIn na b B T) args S ->
  typing_spine Σ Γ (T {0 := b}) args S.
Proof.
  intros wfΣ Hsp.
  depelim Hsp.
  constructor. auto.
  now eapply invert_cumul_letin_l in c.
  econstructor; eauto.
  now eapply invert_cumul_letin_l in c.
Qed.

Lemma typing_spine_letin {cf:checker_flags} {Σ Γ na b B T args S} : 
  wf Σ.1 ->
  typing_spine Σ Γ (T {0 := b}) args S ->
  typing_spine Σ Γ (tLetIn na b B T) args S.
Proof.
  intros wfΣ Hsp.
  depelim Hsp.
  constructor. auto.
  etransitivity. eapply red_cumul. eapply red1_red, red_zeta. auto.
  econstructor; eauto.
  etransitivity. eapply red_cumul. eapply red1_red, red_zeta. auto.
Qed.

Lemma typing_spine_weaken_concl {cf:checker_flags} {Σ Γ T args S S'} : 
  wf Σ.1 ->
  typing_spine Σ Γ T args S ->
  Σ ;;; Γ |- S <= S' ->
  isWfArity_or_Type Σ Γ S' ->
  typing_spine Σ Γ T args S'.
Proof.
  intros wfΣ.  
  induction 1 in S' => cum.
  constructor; auto. now transitivity ty'.
  intros isWAT.
  econstructor; eauto.
Qed.

Lemma typing_spine_prod {cf:checker_flags} {Σ Γ na b B T args S} : 
  wf Σ.1 ->
  typing_spine Σ Γ (T {0 := b}) args S ->
  isWfArity_or_Type Σ Γ (tProd na B T) ->
  Σ ;;; Γ |- b : B ->
  typing_spine Σ Γ (tProd na B T) (b :: args) S.
Proof.
  intros wfΣ Hsp.
  depelim Hsp.
  econstructor; eauto. reflexivity.
  constructor; auto with pcuic.
  intros Har. eapply isWAT_tProd in Har as [? ?]; eauto using typing_wf_local.
  intros Hb.
  econstructor. 3:eauto. 2:reflexivity.
  destruct i1 as [[ctx [s [Hs ?]]]|?].
  - left. exists ([vass na B] ,,, ctx), s; simpl; intuition auto.
    rewrite destArity_app Hs /= ?app_context_nil_l //.
    now rewrite app_context_assoc.
  - right. destruct i1 as [s Hs], i0 as [s' Hs'].
    eexists. eapply type_Prod; eauto.
  - econstructor; eauto.
Qed.

Lemma typing_spine_WAT_concl {cf:checker_flags} {Σ Γ T args S} : 
  typing_spine Σ Γ T args S ->
  isWfArity_or_Type Σ Γ S.
Proof.
  induction 1; auto.
Qed.


Lemma type_mkProd_or_LetIn {cf:checker_flags} Σ Γ d u t s : 
  wf Σ.1 ->
  Σ ;;; Γ |- decl_type d : tSort u ->
  Σ ;;; Γ ,, d |- t : tSort s ->
  match decl_body d return Type with 
  | Some b => Σ ;;; Γ |- mkProd_or_LetIn d t : tSort s
  | None => Σ ;;; Γ |- mkProd_or_LetIn d t : tSort (Universe.sort_of_product u s)
  end.
Proof.
  intros wfΣ. destruct d as [na [b|] dty] => [Hd Ht|Hd Ht]; rewrite /mkProd_or_LetIn /=.
  - have wf := typing_wf_local Ht.
    depelim wf. clear l.
    eapply type_Cumul. econstructor; eauto.
    left. red. exists [], s; intuition auto.
    transitivity (tSort s).
    eapply red_cumul. eapply red1_red. constructor. reflexivity.
  - have wf := typing_wf_local Ht.
    depelim wf; clear l.
    eapply type_Cumul. eapply type_Prod; eauto.
    left. red. exists [], (Universe.sort_of_product u s); intuition auto.
    reflexivity.
Qed.

Lemma type_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Γ' u t s : 
  wf Σ.1 ->
  type_local_ctx (lift_typing typing) Σ Γ Γ' u ->
  Σ ;;; Γ ,,, Γ' |- t : tSort s ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Γ' t : tSort (Universe.sort_of_product u s).
Proof.
  revert Γ u s t.
  induction Γ'; simpl; auto; move=> Γ u s t wfΣ equ Ht.
  - eapply type_Cumul; eauto.
    left. eexists [], _; intuition eauto.
    eapply typing_wf_local; eauto.
    constructor. constructor.
    eapply leq_universe_product.
  - specialize (IHΓ' Γ  u (Universe.sort_of_product u s)); auto.
    unfold app_context in Ht.
    eapply type_Cumul.
    eapply IHΓ'; auto.
    destruct a as [na [b|] ty]; intuition auto.
    destruct a as [na [b|] ty]; intuition auto.
    { apply typing_wf_local in Ht as XX. inversion XX; subst.
      eapply (type_mkProd_or_LetIn _ _ {| decl_body := Some b |}); auto.
      + simpl. exact X0.π2.
      + eapply type_Cumul; eauto.
        left. eexists [], _. intuition eauto.
        constructor. constructor. eapply leq_universe_product. }
    eapply (type_mkProd_or_LetIn _ _ {| decl_body := None |}) => /=; eauto.
    left. eexists [], _; intuition eauto using typing_wf_local.
    eapply typing_wf_local in Ht.
    depelim Ht; eapply All_local_env_app in Ht; intuition auto.
    now rewrite sort_of_product_twice.
Qed.

Lemma isWAT_wf_local {cf:checker_flags} {Σ Γ T} : isWfArity_or_Type Σ Γ T -> wf_local Σ Γ.
Proof.
  move=> [[ctx [s [_ Hs]]]|[s Hs]]. 
  - eapply All_local_env_app in Hs.
    intuition eauto with pcuic.
  - now eapply typing_wf_local.
Qed.  


  (* 
Lemma typing_spine_prod {cf:checker_flags} Σ Γ na b B T args S : 
  wf Σ.1 ->
  typing_spine Σ Γ (tProd na b B T) args S ->
  typing_spine Σ Γ (T {0 := b}) args S.
Proof.
  intros wfΣ Hsp.
  depelim Hsp.
  constructor. auto.
  now eapply invert_cumul_letin_l in c.
  econstructor; eauto.
  now eapply invert_cumul_letin_l in c.
Qed. *)

Lemma app_context_push Γ Δ Δ' d : (Γ ,,, Δ ,,, Δ') ,, d = (Γ ,,, Δ ,,, (Δ' ,, d)).
Proof.
  reflexivity.
Qed.

Hint Extern 4 (_ ;;; _ |- _ <= _) => reflexivity : pcuic.
Ltac pcuic := eauto 5 with pcuic.


Lemma subslet_app_closed {cf:checker_flags} Σ Γ s s' Δ Δ' : 
  subslet Σ Γ s Δ ->
  subslet Σ Γ s' Δ' ->
  closed_ctx Δ ->
  subslet Σ Γ (s ++ s') (Δ' ,,, Δ).
Proof.
  induction 1 in s', Δ'; simpl; auto; move=> sub';
  rewrite closedn_ctx_snoc => /andP [clctx clt];
  try constructor; auto.
  - pose proof (subslet_length X). rewrite Nat.add_0_r in clt.
    rewrite /closed_decl /= -H in clt.
    rewrite subst_app_simpl /= (subst_closedn s') //.
  - pose proof (subslet_length X). rewrite Nat.add_0_r in clt.
    rewrite /closed_decl /= -H in clt. move/andP: clt => [clt clT].
    replace (subst0 s t) with (subst0 (s ++ s') t).
    + constructor; auto.
      rewrite !subst_app_simpl /= !(subst_closedn s') //.
    + rewrite !subst_app_simpl /= !(subst_closedn s') //.
Qed.

Hint Constructors subslet : core pcuic.

Lemma subslet_app_inv {cf:checker_flags} Σ Γ Δ Δ' s : 
  subslet Σ Γ s (Δ ,,, Δ') ->
  subslet Σ Γ (skipn #|Δ'| s) Δ * 
  subslet Σ Γ (firstn #|Δ'| s) (subst_context (skipn #|Δ'| s) 0 Δ').
Proof.
  intros sub. split.
  - induction Δ' in Δ, s, sub |- *; simpl; first by rewrite skipn_0.
    depelim sub; rewrite skipn_S; auto.
  - induction Δ' in Δ, s, sub |- *; simpl; first by constructor.
    destruct s; depelim sub.
    * rewrite subst_context_snoc. constructor; eauto.
      rewrite skipn_S Nat.add_0_r /=.
      assert(#|Δ'| = #|firstn #|Δ'| s|).
      { pose proof (subslet_length sub).
        rewrite app_context_length in H.
        rewrite firstn_length_le; lia. }
      rewrite {3}H.
      rewrite -subst_app_simpl.
      now rewrite firstn_skipn.
    * rewrite subst_context_snoc.
      rewrite skipn_S Nat.add_0_r /=.
      rewrite /subst_decl /map_decl /=.
      specialize (IHΔ' _ _ sub).
      epose proof (cons_let_def _ _ _ _ _ (subst (skipn #|Δ'| s0) #|Δ'| t0) 
      (subst (skipn #|Δ'| s0) #|Δ'| T) IHΔ').
      assert(#|Δ'| = #|firstn #|Δ'| s0|).
      { pose proof (subslet_length sub).
        rewrite app_context_length in H.
        rewrite firstn_length_le; lia. }      
      rewrite {3 6}H in X.
      rewrite - !subst_app_simpl in X.
      rewrite !firstn_skipn in X.
      specialize (X t1).
      rewrite {3}H in X.
      now rewrite - !subst_app_simpl firstn_skipn in X.
Qed.

Lemma make_context_subst_skipn {Γ args s s'} :
  make_context_subst Γ args s = Some s' ->
  skipn #|Γ| s' = s.
Proof.
  induction Γ in args, s, s' |- *.
  - destruct args; simpl; auto.
    + now intros [= ->].
    + now discriminate.
  - destruct a as [na [b|] ty]; simpl.
    + intros H.
      specialize (IHΓ _ _ _ H).
      now eapply skipn_n_Sn.
    + destruct args; try discriminate.
      intros Hsub.
      specialize (IHΓ _ _ _ Hsub).
      now eapply skipn_n_Sn.
Qed.

Lemma subslet_inds_gen {cf:checker_flags} Σ ind mdecl idecl :
  wf Σ ->
  declared_inductive Σ mdecl ind idecl ->
  let u := PCUICLookup.abstract_instance (ind_universes mdecl) in
  subslet (Σ, ind_universes mdecl) [] (inds (inductive_mind ind) u (ind_bodies mdecl))
    (arities_context (ind_bodies mdecl)).
Proof.
  intros wfΣ isdecl u.
  unfold inds.
  pose proof (proj1 isdecl) as declm'. 
  apply PCUICWeakeningEnv.on_declared_minductive in declm' as [oind oc]; auto.
  clear oc.
  assert (Alli (fun i x =>
   (Σ, ind_universes mdecl) ;;; [] |- tInd {| inductive_mind := inductive_mind ind; inductive_ind := i |} u : (ind_type x)) 0 (ind_bodies mdecl)).
  { apply forall_nth_error_Alli. intros.
    eapply type_Cumul.
    econstructor; eauto. split; eauto with pcuic.
    eapply consistent_instance_ext_abstract_instance; eauto.
    eapply declared_inductive_wf_global_ext; eauto with pcuic.
    eapply Alli_nth_error in oind; eauto. simpl in oind.
    destruct oind. red in onArity. right. apply onArity.
    rewrite (subst_instance_ind_type_id Σ _ {| inductive_mind := inductive_mind ind; inductive_ind := i |}); eauto.
    destruct isdecl. split; eauto. reflexivity. }
  clear oind.
  revert X. clear onNpars onGuard.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4 5.
  induction l using rev_ind; simpl; first constructor.
  rewrite /subst_instance_context /= /map_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=. 
  rewrite /= app_length /= Nat.add_1_r.
  constructor.
  - rewrite -rev_map_spec. apply IHl; try lia.
    eapply Alli_app in X; intuition auto.
  - eapply Alli_app in X as [oind Hx].
    depelim Hx. clear Hx.
    rewrite Nat.add_0_r in t.
    rewrite subst_closedn; auto. 
    + eapply typecheck_closed in t as [? ?]; auto.
Qed.

Lemma subslet_inds {cf:checker_flags} Σ ind u mdecl idecl :
  wf Σ.1 ->
  declared_inductive Σ.1 mdecl ind idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  subslet Σ [] (inds (inductive_mind ind) u (ind_bodies mdecl))
    (subst_instance_context u (arities_context (ind_bodies mdecl))).
Proof.
  intros wfΣ isdecl univs.
  unfold inds.
  destruct isdecl as [declm _].
  pose proof declm as declm'.
  apply PCUICWeakeningEnv.on_declared_minductive in declm' as [oind oc]; auto.
  clear oc.
  assert (Alli (fun i x => Σ ;;; [] |- tInd {| inductive_mind := inductive_mind ind; inductive_ind := i |} u : subst_instance_constr u (ind_type x)) 0 (ind_bodies mdecl)). 
  { apply forall_nth_error_Alli.
    econstructor; eauto. split; eauto. }
  clear oind.
  revert X. clear onNpars onGuard.
  generalize (le_n #|ind_bodies mdecl|).
  generalize (ind_bodies mdecl) at 1 3 4 5.
  induction l using rev_ind; simpl; first constructor.
  rewrite /subst_instance_context /= /map_context.
  simpl. rewrite /arities_context rev_map_spec /=.
  rewrite map_app /= rev_app_distr /=. 
  rewrite {1}/map_decl /= app_length /= Nat.add_1_r.
  constructor.
  - rewrite -rev_map_spec. apply IHl; try lia.
    eapply Alli_app in X; intuition auto.
  - eapply Alli_app in X as [oind Hx].
    depelim Hx. clear Hx.
    rewrite Nat.add_0_r in t.
    rewrite subst_closedn; auto. 
    + eapply typecheck_closed in t as [? ?]; auto.
Qed.

Lemma weaken_subslet {cf:checker_flags} Σ s Δ Γ :
  wf Σ.1 ->
  wf_local Σ Γ -> 
  subslet Σ [] s Δ -> subslet Σ Γ s Δ.
Proof.
  intros wfΣ wfΔ.
  induction 1; constructor; auto.
  + eapply (weaken_ctx (Γ:=[]) Γ); eauto.
  + eapply (weaken_ctx (Γ:=[]) Γ); eauto.
Qed.



Set Default Goal Selector "1".

Lemma substitution_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Δ T s : 
  wf Σ.1 ->
  subslet Σ Γ s Δ ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  isType Σ Γ (subst0 s T).
Proof.
  intros wfΣ sub [s' Hs].
  exists s'.
  revert Γ s sub Hs. 
  generalize (le_n #|Δ|).
  generalize #|Δ| at 2.
  induction n in Δ, T |- *.
  - destruct Δ; simpl; intros; try (elimtype False; lia).
    depelim sub.
    rewrite subst_empty; auto.
  - destruct Δ using rev_ind; try clear IHΔ.
    + intros Hn Γ s sub; now depelim sub; rewrite subst_empty.
    + rewrite app_length Nat.add_1_r /= => Hn Γ s sub.
    pose proof (subslet_length sub). rewrite app_length /= Nat.add_1_r in H.
    have Hl : #|l| = #|firstn #|l| s|.
    { rewrite firstn_length_le; lia. }
    destruct x as [na [b|] ty] => /=;
    rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    
    intros Hs.
    eapply inversion_LetIn in Hs as [? [? [? [? [? ?]]]]]; auto.
    eapply substitution_let in t1; auto.
    eapply invert_cumul_letin_l in c; auto.
    pose proof (subslet_app_inv _ _ _ _ _ sub) as [subl subr].
    depelim subl. depelim subl. rewrite subst_empty in H0. rewrite H0 in subr.
    specialize (IHn (subst_context [b] 0 l) (subst [b] #|l| T) ltac:(rewrite subst_context_length; lia)).
    specialize (IHn _ _ subr).
    rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in t1.
    rewrite !subst_empty in t3.
    forward IHn.
    eapply type_Cumul. eapply t1. left; exists [], s'; intuition eauto using typing_wf_local.
    eapply c. rewrite {2}Hl in IHn.
    now rewrite -subst_app_simpl -H0 firstn_skipn in IHn.
    
    intros Hs.
    eapply inversion_Prod in Hs as [? [? [? [? ?]]]]; auto.
    pose proof (subslet_app_inv _ _ _ _ _ sub) as [subl subr].
    depelim subl; depelim subl. rewrite subst_empty in t2. rewrite H0 in subr.
    epose proof (substitution0 _ _ na _ _ _ _ wfΣ t0 t2).
    specialize (IHn (subst_context [t1] 0 l) (subst [t1] #|l| T)).
    forward IHn. rewrite subst_context_length; lia.
    specialize (IHn _ _ subr).
    rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in X.
    forward IHn.
    eapply type_Cumul. simpl in X. eapply X.
    left; exists [], s'; intuition eauto using typing_wf_local.
    eapply cumul_Sort_inv in c.
    do 2 constructor.
    transitivity (Universe.sort_of_product x x0).
    eapply leq_universe_product. auto.
    rewrite {2}Hl in IHn.
    now rewrite -subst_app_simpl -H0 firstn_skipn in IHn.
Qed.

Lemma isWAT_it_mkProd_or_LetIn_app {cf:checker_flags} Σ Γ Δ T s : 
  wf Σ.1 ->
  subslet Σ Γ s Δ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
  isWfArity_or_Type Σ Γ (subst0 s T).
Proof.
  intros wfΣ sub iswat.
  destruct iswat as [[ctx [s' [Hs wf]]]|].
  left.
  rewrite destArity_it_mkProd_or_LetIn in Hs.
  rewrite app_context_nil_l in Hs.
  rewrite destArity_app in Hs.
  destruct (destArity [] T) as [[ctx' T']|] eqn:Heq; try discriminate.
  simpl in Hs. noconf Hs.
  rewrite app_context_assoc in wf.
  eapply substitution_wf_local in wf; eauto.
  exists (subst_context s 0 ctx'), s'; intuition auto.
  generalize (subst_destArity [] T s 0). rewrite Heq.
  unfold subst_context, fold_context. simpl. now intros ->.
  right.
  now eapply substitution_it_mkProd_or_LetIn.
Qed.

Lemma isWAT_tLetIn_red {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na t A B}
  : isWfArity_or_Type Σ Γ (tLetIn na t A B) -> isWfArity_or_Type Σ Γ (B {0:=t}).
Proof.
  intro HH.
  destruct HH as [[ctx [s [H1 H2]]]|[s H]].
  + cbn in H1. apply destArity_app_Some in H1.
    destruct H1 as [ctx' [H1 HH]]; subst ctx.
    rewrite app_context_assoc in H2.
    left. 
    generalize (subst_destArity [] B [t] 0). rewrite H1.
    simpl. move=> H. do 2 eexists; intuition eauto.
    unfold snoc in H2.
    eapply substitution_wf_local. eauto. 2:eauto.
    eapply All_local_env_app in H2 as [wf _].
    inv wf. red in X1. 
    epose proof (cons_let_def _ _ _ [] _ _ _ (emptyslet _ _)).
    rewrite !subst_empty in X2. eapply (X2 X1).
  + right. exists s. 
    apply inversion_LetIn in H; tas. destruct H as [s1 [A' [HA [Ht [HB H]]]]].
    eapply type_Cumul with (A' {0 := t}). eapply substitution_let in HB; eauto.
    * left. apply cumul_Sort_r_inv in H.
      destruct H as [s' [H H']]. exists [], s; intuition auto.
    * eapply cumul_Sort_r_inv in H.
      destruct H as [s' [H H']].
      eapply cumul_trans with (tSort s'); eauto.
      eapply red_cumul.
      apply invert_red_letin in H as [H|H] => //.
      destruct H as [na' [d' [ty' [b' [[[reds ?] ?] ?]]]]].
      discriminate.
      now repeat constructor.
Qed.

Lemma isWAT_tLetIn_dom {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na t A B}
  : isWfArity_or_Type Σ Γ (tLetIn na t A B) -> Σ ;;; Γ |- t : A.
Proof.
  intro HH.
  destruct HH as [[ctx [s [H1 H2]]]|[s H]].
  + cbn in H1. apply destArity_app_Some in H1.
    destruct H1 as [ctx' [H1 HH]]; subst ctx.
    rewrite app_context_assoc in H2.
    eapply All_local_env_app in H2 as [wf _].
    now inv wf.
  + apply inversion_LetIn in H; tas. now destruct H as [s1 [A' [HA [Ht [HB H]]]]].
Qed.

Lemma on_minductive_wf_params {cf : checker_flags} (Σ : global_env × universes_decl)
    mdecl (u : Instance.t) ind :
   wf Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (subst_instance_context u (ind_params mdecl)).
Proof.
  intros; eapply (wf_local_instantiate _ (InductiveDecl mdecl)); eauto.
  eapply on_declared_minductive in H; auto.
  now apply onParams in H.
Qed.

Lemma it_mkProd_or_LetIn_wf_local {cf:checker_flags} Σ Γ Δ T U : 
  wf Σ.1 ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ T : U -> wf_local Σ (Γ ,,, Δ).
Proof.
  move=> wfΣ; move: Γ T U.
  induction Δ using rev_ind => Γ T U.
  + simpl. intros. now eapply typing_wf_local in X.
  + rewrite it_mkProd_or_LetIn_app.
    destruct x as [na [b|] ty]; cbn; move=> H.
    * apply inversion_LetIn in H as (s1 & A & H0 & H1 & H2 & H3); auto.
      eapply All_local_env_app_inv; split; pcuic. now apply typing_wf_local in H0.
      eapply All_local_env_app_inv. split. repeat constructor. now exists s1.
      auto. apply IHΔ in H2.
      eapply All_local_env_app in H2. intuition auto.
      eapply All_local_env_impl; eauto. simpl. intros.
      now rewrite app_context_assoc.
    * apply inversion_Prod in H as (s1 & A & H0 & H1 & H2); auto.
      eapply All_local_env_app_inv; split; pcuic. now apply typing_wf_local in H0.
      eapply All_local_env_app_inv. split. repeat constructor. now exists s1.
      apply IHΔ in H1.
      eapply All_local_env_app in H1. intuition auto.
      eapply All_local_env_impl; eauto. simpl. intros.
      now rewrite app_context_assoc.
Qed.

Lemma isWAT_it_mkProd_or_LetIn_wf_local {cf:checker_flags} Σ Γ Δ T : 
  wf Σ.1 ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) -> wf_local Σ (Γ ,,, Δ).
Proof.
  move=> wfΣ [[ctx [s [Hs Hwf]]]|[s Hs]].
  - rewrite destArity_it_mkProd_or_LetIn app_context_nil_l in Hs.
    eapply destArity_app_Some in Hs as [ctx' [? eq]]. subst ctx.
    rewrite app_context_assoc in Hwf.
    now eapply All_local_env_app in Hwf as [Hwf _].
  - now eapply it_mkProd_or_LetIn_wf_local in Hs.
Qed.

Lemma isWAT_weaken {cf:checker_flags} Σ Γ T :
  wf Σ.1 -> wf_local Σ Γ ->
  isWfArity_or_Type Σ [] T ->
  isWfArity_or_Type Σ Γ T.
Proof.
  move=> wfΣ wfΓ [[ctx [s eq]]|[s hs]].
  - left; exists ctx, s. intuition pcuic.
    rewrite app_context_nil_l in b.
    eapply weaken_wf_local=> //.
  - right. exists s.
    unshelve epose proof (subject_closed wfΣ hs); eauto.
    eapply (weakening _ _ Γ) in hs => //.
    rewrite lift_closed in hs => //.
    now rewrite app_context_nil_l in hs.
    now rewrite app_context_nil_l.
Qed.

Lemma subst_telescope_subst_instance_constr u s k Γ :
  subst_telescope (map (subst_instance_constr u) s) k 
    (subst_instance_context u Γ) =
  subst_instance_context u (subst_telescope s k Γ).
Proof.
  rewrite /subst_telescope /subst_instance_context /map_context.
  rewrite map_mapi mapi_map. apply mapi_ext.
  intros. rewrite !compose_map_decl; apply map_decl_ext => ?.
  now rewrite -subst_subst_instance_constr.
Qed.

Section CheckerFlags.
  Context `{cf : config.checker_flags}.

  Lemma isType_subst_instance_decl {Σ Γ T c decl u} :
    wf Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isType (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isType Σ (subst_instance_context u Γ) (subst_instance_constr u T).
  Proof.
    destruct Σ as [Σ φ]. intros X X0 [s Hs] X1.
    exists (subst_instance_univ u s).
    eapply (typing_subst_instance_decl _ _ _ (tSort _)); eauto.
  Qed.
  
  Lemma isWfArity_subst_instance_decl {Σ Γ T c decl u} :
    wf Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isWfArity typing (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isWfArity typing Σ (subst_instance_context u Γ) (subst_instance_constr u T).
  Proof.
    destruct Σ as [Σ φ]. intros X X0 [ctx [s [eq wf]]] X1.
    exists (subst_instance_context u ctx), (subst_instance_univ u s).
    rewrite (subst_instance_destArity []) eq. intuition auto.
    rewrite -subst_instance_context_app.  
    eapply wf_local_subst_instance_decl; eauto.  
  Qed.
  
  Lemma isWAT_subst_instance_decl {Σ Γ T c decl u} :
    wf Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isWfArity_or_Type (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isWfArity_or_Type Σ (subst_instance_context u Γ) (subst_instance_constr u T).
  Proof.
    destruct Σ as [Σ φ]. intros X X0 X1 X2.
    destruct X1.
    - left. now eapply isWfArity_subst_instance_decl.
    - right. now eapply isType_subst_instance_decl.
  Qed.

End CheckerFlags.