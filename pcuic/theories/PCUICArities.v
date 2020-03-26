(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses ProofIrrelevance ssreflect.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping
     PCUICCumulativity PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion PCUICValidity
     PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICClosed PCUICPrincipality PCUICSubstitution
     PCUICWeakening PCUICGeneration PCUICUtils PCUICCtxShape PCUICContexts
     PCUICUniverses.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.

Derive Signature for typing_spine.

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
      specialize (IHn ctx ltac:(lia) (Γ ,, vass na ty) B' HT). clear IHctx.
      destruct IHn as [T' [ctx' [s' [[[redT' destT] convctx] leq]]]].
      exists (tProd na' A' T'), (ctx' ++ [vass na' A'])%list, s'. intuition auto. 2:simpl.
      -- transitivity (tProd na' A' B'); auto.
        eapply red_prod. reflexivity.
        todo"red context conv"%string.
      -- now rewrite destArity_app destT.
      -- rewrite smash_context_app /= .
         rewrite !app_context_assoc. simpl.
         eapply conv_context_trans with (Γ ,, vass na ty ,,, ctx'); auto.
         todo "conv context"%string.
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
    now apply wf_local_app in HΓ.
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
    depelim wf; simpl in H; noconf H. clear l.
    eapply type_Cumul. econstructor; eauto.
    left. red. exists [], s; intuition auto.
    transitivity (tSort s).
    eapply red_cumul. eapply red1_red. constructor. reflexivity.
  - have wf := typing_wf_local Ht.
    depelim wf; simpl in H; noconf H.
    clear l.
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
    constructor. constructor.
    apply eq_universe_leq_universe.
    apply sort_of_product_twice.
Qed.

Local Open Scope string_scope.



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

 
(** We can easily invert in case there are only assumptions: not so 
    easy to formulate with LetIn's which have non-local effects.
    Luckily, most kernel functions just expand lets when needed. *)
(*
  Lemma inversion_it_mkProd_or_LetIn {cf:checker_flags} Σ {wfΣ : wf Σ.1}:
 forall {Γ Δ t s},
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ t : tSort s ->
  Σ ;;; Γ ,,, Δ |- t : tSort s.
Proof.
intros Γ Δ t s h. revert Γ t s h.
induction Δ; intros.
- apply h.
- destruct a as [na [b|] ty]; simpl in *;
  rewrite /mkProd_or_LetIn /= in h.
  specialize (IHΔ _ _ _ h).
  eapply inversion_LetIn in IHΔ as [s' [? [? [? [? ?]]]]]; auto.
  eapply type_Cumul. eapply t2.
  left. eexists _, _; intuition eauto using typing_wf_local.
  eapply invert_cumul_letin_l in c; auto.
  eapply invert_cumul_sort_r in c as [u' [redu' cumu']].
  transitivity (tSort u'). 2:do 2 constructor; auto. all:auto.
  eapply red_cumul.
  transitivity (x {0 := b}).
  eapply red1_red. 

  specialize (IHΔ _ _ _ h).
   
  eapply inversion_Prod in IHΔ as [? [? [? [? ]]]].
  eapply type_Cumul; eauto.
  left. eexists _, _; intuition eauto using typing_wf_local.
  do 2 constructor.
  eapply cumul_Sort_inv in c.
  transitivity (Universe.sort_of_product x x0); auto using leq_universe_product.
  auto.
Qed.*)

Lemma inversion_it_mkProd_or_LetIn {cf:checker_flags} Σ {wfΣ : wf Σ.1}:
 forall {Γ Δ t s},
  assumption_context Δ ->
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ t : tSort s ->
  Σ ;;; Γ ,,, Δ |- t : tSort s.
Proof.
intros Γ Δ t s HΔ h. revert HΔ Γ t s h.
induction Δ; intros.
- apply h.
- destruct a as [na [b|] ty]; simpl in *;
  rewrite /mkProd_or_LetIn /= in h.
  elimtype False. depelim HΔ. simpl in H; noconf H.
  forward IHΔ. depelim HΔ. now simpl in H; noconf H.
  clear HΔ.
  specialize (IHΔ _ _ _ h).
  (* eapply inversion_LetIn in IHΔ as [s' [? [? [? [? ?]]]]].
  eapply type_Cumul. eapply t2.
  left. eexists _, _; intuition eauto using typing_wf_local.
  eapply invert_cumul_letin_l in c; auto.
  eapply invert_cumul_sort_r in c as [u' [redu' cumu']].
  transitivity (tSort u'). 2:do 2 constructor; auto. all:auto.
  eapply red_cumul. admit.
  specialize (IHΔ _ _ _ h).
   *)
  eapply inversion_Prod in IHΔ as [? [? [? [? ]]]].
  eapply type_Cumul; eauto.
  left. eexists _, _; intuition eauto using typing_wf_local.
  do 2 constructor.
  eapply cumul_Sort_inv in c.
  transitivity (Universe.sort_of_product x x0); auto using leq_universe_product.
  auto.
Qed.

Hint Extern 4 (_ ;;; _ |- _ <= _) => reflexivity : pcuic.
Ltac pcuic := eauto 5 with pcuic.

(** Requires Validity *)
Lemma type_mkApps_inv {cf:checker_flags} (Σ : global_env_ext) Γ f u T : wf Σ ->
  Σ ;;; Γ |- mkApps f u : T ->
  { T' & { U & ((Σ ;;; Γ |- f : T') * (typing_spine Σ Γ T' u U) * (Σ ;;; Γ |- U <= T))%type } }.
Proof.
  intros wfΣ; induction u in f, T |- *. simpl. intros.
  { exists T, T. intuition pcuic. constructor. eapply validity; auto with pcuic.
    now eapply typing_wf_local. eauto. eapply cumul_refl'. }
  intros Hf. simpl in Hf.
  destruct u. simpl in Hf.
  - eapply inversion_App in Hf as [na' [A' [B' [Hf' [Ha HA''']]]]].
    eexists _, _; intuition eauto.
    econstructor; eauto with pcuic. eapply validity; eauto with wf pcuic.
    constructor. all:eauto with pcuic.
    eapply validity; eauto with wf.
    eapply type_App; eauto. 
  - specialize (IHu (tApp f a) T).
    specialize (IHu Hf) as [T' [U' [[H' H''] H''']]].
    eapply inversion_App in H' as [na' [A' [B' [Hf' [Ha HA''']]]]]. 2:{ eassumption. }
    exists (tProd na' A' B'), U'. intuition; eauto.
    econstructor. eapply validity; eauto with wf.
    eapply cumul_refl'. auto.
    clear -H'' HA''' wfΣ. depind H''.
    econstructor; eauto. eapply cumul_trans; eauto.  
Qed.

Lemma subslet_app {cf:checker_flags} Σ Γ s s' Δ Δ' : 
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
    depelim subl; simpl in H1; noconf H1.
    depelim subl. rewrite subst_empty in H0. rewrite H0 in subr.
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
    depelim subl; simpl in H1; noconf H1.
    depelim subl. rewrite subst_empty in t2. rewrite H0 in subr.
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