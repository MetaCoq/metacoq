(* Distributed under the terms of the MIT license. *)
From Coq Require Import CRelationClasses ProofIrrelevance.
From MetaCoq.Template Require Import config Universes utils BasicAst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICSigmaCalculus 
     PCUICUnivSubst PCUICTyping PCUICUnivSubstitution
     PCUICCumulativity PCUICPosition PCUICEquality
     PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion
     PCUICWeakeningEnv PCUICClosed PCUICSubstitution PCUICContextSubst
     PCUICWeakening PCUICGeneration PCUICUtils PCUICContexts
     PCUICArities.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.
Require Import ssreflect.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).


Derive Signature for ctx_inst.

Notation ctx_inst := (ctx_inst typing).

Lemma typing_spine_eq {cf:checker_flags} Σ Γ ty s s' ty' :
  s = s' ->
  typing_spine Σ Γ ty s ty' ->
  typing_spine Σ Γ ty s' ty'.
Proof. now intros ->. Qed.

Lemma typing_spine_strengthen {cf:checker_flags} Σ Γ T args U : 
  wf Σ.1 ->
  typing_spine Σ Γ T args U ->
  forall T', Σ ;;; Γ |- T' <= T ->
  typing_spine Σ Γ T' args U.
Proof.
  induction 2 in |- *; intros T' (*WAT*)redT.
  - constructor. eauto. transitivity ty; auto.
  - specialize (IHX0 (B {0 := hd})).
    forward IHX0. { reflexivity. }
    eapply type_spine_cons with na A B; auto.
    etransitivity; eauto.
Qed.

Lemma subslet_app {cf:checker_flags} Σ Γ s s' Δ Δ' : 
  subslet Σ Γ s (subst_context s' 0 Δ) ->
  subslet Σ Γ s' Δ' ->
  subslet Σ Γ (s ++ s') (Δ' ,,, Δ).
Proof.
induction Δ in s, s', Δ' |- *; simpl; auto; move=> sub'.
- depelim sub'. auto.
- rewrite subst_context_snoc in sub' => sub''.
  move:(subslet_length sub') => /=.
  rewrite /snoc /= subst_context_length /= => Hlen.
  destruct a as [na [b|] ty].
  * depelim sub'; simpl in t0, Hlen.
    rewrite -subst_app_simpl' /=. lia.
    constructor. eauto.
    now rewrite - !subst_app_simpl' in t0; try lia.
  * rewrite /subst_decl /map_decl /snoc /= in sub'.
    depelim sub'; simpl in Hlen.
    rewrite - !subst_app_simpl' in t0; try lia.
    simpl; constructor; eauto.
Qed.

Lemma subslet_skipn {cf:checker_flags} Σ Γ s Δ n : 
  subslet Σ Γ s Δ ->
  subslet Σ Γ (skipn n s) (skipn n Δ).
Proof.
  induction n in s, Δ |- *.
  - now rewrite !skipn_0.
  - intros H; depelim H.
    * rewrite !skipn_nil. constructor.
    * rewrite !skipn_S. auto.
    * rewrite !skipn_S. auto.
Qed.

Lemma untyped_subslet_skipn Γ s Δ n : 
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ (skipn n s) (skipn n Δ).
Proof.
  induction n in s, Δ |- *.
  - now rewrite !skipn_0.
  - intros H; depelim H.
    * rewrite !skipn_nil. constructor.
    * rewrite !skipn_S. auto.
    * rewrite !skipn_S. auto.
Qed.

Lemma untyped_subslet_eq_subst Γ s s' Δ : 
  untyped_subslet Γ s Δ -> s = s' ->
  untyped_subslet Γ s' Δ.
Proof. now intros H ->. Qed.

Lemma context_subst_app_inv {ctx ctx' : context} {args s : list term} :
  context_subst (subst_context (skipn #|ctx| s) 0 ctx)
    (skipn (context_assumptions ctx') args) 
    (firstn #|ctx| s)
  × context_subst ctx' (firstn (context_assumptions ctx') args)	(skipn #|ctx| s) ->
  context_subst (ctx ++ ctx') args s.
Proof.
  move=> [Hl Hr].
  rewrite -(firstn_skipn (context_assumptions ctx') args).
  assert (lenctx' : context_assumptions ctx' + context_assumptions ctx = #|args|).
  { assert (lenctx'' : context_assumptions ctx' <= #|args|).
    move: (context_subst_assumptions_length Hr).
    rewrite firstn_length; lia.
    move: (context_subst_assumptions_length Hr).
    move: (context_subst_assumptions_length Hl).
    rewrite firstn_length skipn_length; try lia.
    intros H1 H2. rewrite context_assumptions_subst in H1. lia. }
  move: args s ctx' lenctx' Hl Hr.
  induction ctx => args s ctx' lenctx' Hl Hr.
  - simpl in *. depelim Hl. rewrite H app_nil_r. now rewrite skipn_0 in Hr.
  - simpl in *. destruct s as [|u s];
    simpl in *; rewrite subst_context_snoc0 in Hl; depelim Hl.
    simpl in H. noconf H.
    * destruct a as [na [b|] ty]; simpl in *; noconf H.
      rewrite skipn_S in Hl, Hr. destruct args using rev_case. rewrite skipn_nil in H0.
      apply (f_equal (@length _)) in H0. simpl in H0. autorewrite with len in H0.
      simpl in H0; lia. rewrite H0.
      rewrite skipn_app in H0.
      rewrite app_length /= in lenctx'.
      specialize (IHctx args s ctx'). forward IHctx by lia.
      assert (context_assumptions ctx' - #|args| = 0) by lia.
      rewrite H skipn_0 in H0. apply app_inj_tail in H0 as [Ha xu]. subst x.
      rewrite -Ha.
      rewrite -Ha in Hl. specialize (IHctx Hl).
      rewrite firstn_app in Hr |- *.
      rewrite H [firstn _ [u]]firstn_0 // app_nil_r in Hr |- *.
      specialize (IHctx Hr). rewrite app_assoc.
      now econstructor.
    * rewrite skipn_S in Hl, Hr, H.
      destruct a as [na' [b'|] ty']; simpl in *; noconf H.
      pose proof (context_subst_length Hl). rewrite subst_context_length in H.
      rewrite {3}H -subst_app_simpl [firstn #|ctx| _ ++ _]firstn_skipn. constructor.
      apply IHctx => //.
Qed.

Lemma ctx_inst_inst {cf:checker_flags} Σ ext u Γ i Δ  :
  wf_global_ext Σ.1 ext ->
  ctx_inst (Σ.1, ext) Γ i Δ ->
  consistent_instance_ext Σ ext u ->
  ctx_inst Σ (subst_instance u Γ)
    (map (subst_instance u) i)
    (subst_instance u Δ).
Proof.
  intros wfext ctxi cu.
  induction ctxi; simpl; constructor; auto.
  * destruct Σ as [Σ univs].
    eapply (typing_subst_instance'' Σ); eauto. apply wfext.
    apply wfext.
  * rewrite (subst_telescope_subst_instance u [i]).
    apply IHctxi.
  * rewrite (subst_telescope_subst_instance u [b]).
    apply IHctxi.
Qed.

Lemma subst_type_local_ctx {cf:checker_flags} Σ Γ Γ' Δ Δ' s ctxs : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ ,,, Γ') ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, Δ ,,, Γ') Δ' ctxs ->
  subslet Σ Γ s Δ ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, subst_context s 0 Γ') (subst_context s #|Γ'| Δ') ctxs.
Proof.
  induction Δ' in Γ' |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  + destruct a0; simpl; rewrite subst_context_snoc /= /subst_decl /map_decl /=.
    intuition auto.
    - exists x; auto.
      rewrite -app_context_assoc in t.
      eapply substitution in t; eauto.
      rewrite subst_context_app app_context_assoc in t.
      simpl in t. rewrite Nat.add_0_r in t. 
      now rewrite app_context_length in t.
    - rewrite -app_context_assoc in b1.
      eapply substitution in b1; eauto.
      rewrite subst_context_app app_context_assoc Nat.add_0_r in b1.
      now rewrite app_context_length in b1.
  + rewrite subst_context_snoc /= /subst_decl /map_decl /=.
      intuition auto.
      rewrite -app_context_assoc in b.
      eapply substitution in b; eauto.
      rewrite subst_context_app app_context_assoc in b.
      rewrite Nat.add_0_r in b. 
      now rewrite app_context_length in b.
Qed.

Lemma subst_sorts_local_ctx {cf:checker_flags} Σ Γ Γ' Δ Δ' s ctxs : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ ,,, Γ') ->
  sorts_local_ctx (lift_typing typing) Σ (Γ ,,, Δ ,,, Γ') Δ' ctxs ->
  subslet Σ Γ s Δ ->
  sorts_local_ctx (lift_typing typing) Σ (Γ ,,, subst_context s 0 Γ') (subst_context s #|Γ'| Δ') ctxs.
Proof.
  induction Δ' in Γ', ctxs |- *; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  + destruct a0; simpl; rewrite subst_context_snoc /= /subst_decl /map_decl /=.
    intuition auto.
    - exists x; auto.
      rewrite -app_context_assoc in t.
      eapply substitution in t; eauto.
      rewrite subst_context_app app_context_assoc in t.
      simpl in t. rewrite Nat.add_0_r in t. 
      now rewrite app_context_length in t.
    - rewrite -app_context_assoc in b1.
      eapply substitution in b1; eauto.
      rewrite subst_context_app app_context_assoc Nat.add_0_r in b1.
      now rewrite app_context_length in b1.
  + rewrite subst_context_snoc /= /subst_decl /map_decl /=.
    destruct ctxs => //.
    intuition auto.
    rewrite -app_context_assoc in b.
    eapply substitution in b; eauto.
    rewrite subst_context_app app_context_assoc in b.
    rewrite Nat.add_0_r in b. 
    now rewrite app_context_length in b.
Qed.

Record spine_subst {cf:checker_flags} Σ Γ inst s Δ := mkSpineSubst {
  spine_dom_wf : wf_local Σ Γ;
  spine_codom_wf : wf_local Σ (Γ ,,, Δ);
  inst_ctx_subst :> context_subst Δ inst s;
  inst_subslet :> subslet Σ Γ s Δ }.
Arguments inst_ctx_subst {cf Σ Γ inst s Δ}.
Arguments inst_subslet {cf Σ Γ inst s Δ}.
Hint Resolve inst_ctx_subst inst_subslet : pcuic.

Lemma spine_subst_eq {cf:checker_flags} {Σ Γ inst s Δ Δ'} : 
  spine_subst Σ Γ inst s Δ ->
  Δ = Δ' ->
  spine_subst Σ Γ inst s Δ'.
Proof.
  now intros sp ->.
Qed.

Lemma spine_subst_inj_subst {cf:checker_flags} {Σ Γ inst s s' Δ} :
  spine_subst Σ Γ inst s Δ ->
  spine_subst Σ Γ inst s' Δ ->
  s = s'.
Proof.
  intros [_ _ c _] [_ _ c' _].
  induction c in s', c' |- *; depelim c'; simpl; auto. 
  apply app_inj_tail in H as [-> ->].
  f_equal; eauto.
  specialize (IHc _ c'). now subst. 
Qed.

Inductive arity_spine {cf : checker_flags} (Σ : global_env_ext) (Γ : context) : 
  term -> list term -> term -> Type :=
| arity_spine_nil ty : arity_spine Σ Γ ty [] ty
| arity_spine_conv ty ty' : isType Σ Γ ty' ->
  Σ ;;; Γ |- ty <= ty' -> arity_spine Σ Γ ty [] ty'  
| arity_spine_def : forall (tl : list term) 
                      (na : aname) (A a B B' : term),                      
                    arity_spine Σ Γ (B {0 := a}) tl B' ->
                    arity_spine Σ Γ (tLetIn na a A B) tl B'
| arity_spine_ass : forall (hd : term) (tl : list term) 
                      (na : aname) (A B B' : term),
                    Σ;;; Γ |- hd : A ->
                    arity_spine Σ Γ (B {0 := hd}) tl B' ->
                    arity_spine Σ Γ (tProd na A B) (hd :: tl) B'.

Derive Signature for arity_spine.

Record wf_arity_spine {cf:checker_flags} Σ Γ T args T' :=
{ wf_arity_spine_wf : isType Σ Γ T;
  wf_arity_spine_spine : arity_spine Σ Γ T args T' }.

Lemma wf_arity_spine_typing_spine {cf:checker_flags} Σ Γ T args T' :
  wf Σ.1 ->
  wf_arity_spine Σ Γ T args T' ->
  typing_spine Σ Γ T args T'.
Proof.
  intros wfΣ [wf sp].
  have wfΓ := isType_wf_local wf.
  induction sp; try constructor; auto. reflexivity.
  eapply isType_tLetIn_red in wf; auto.
  specialize (IHsp wf).
  eapply typing_spine_strengthen; eauto.
  apply red_cumul. apply red1_red. constructor.

  econstructor; eauto. reflexivity. apply IHsp.
  eapply isType_tProd in wf => //.
  destruct wf as [wfA wfB].
  unshelve eapply (@isType_subst _ _ wfΣ Γ [vass na A] _ _ [hd]) in wfB => //.
  constructor; auto.
  constructor. constructor. now rewrite subst_empty.
Qed.

Lemma arity_typing_spine {cf:checker_flags} Σ Γ Γ' s inst s' : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ') ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (tSort s)) inst (tSort s') ->
  (#|inst| = context_assumptions Γ') * leq_universe (global_ext_constraints Σ) s s' *
  ∑ instsubst, spine_subst Σ Γ inst instsubst Γ'.
Proof.
  intros wfΣ wfΓ'; revert s inst s'.
  assert (wf_local Σ Γ). now apply wf_local_app_l in wfΓ'. move X after wfΓ'.
  rename X into wfΓ.
  generalize (le_n #|Γ'|).
  generalize (#|Γ'|) at 2.
  induction n in Γ', wfΓ' |- *.
  - destruct Γ' using rev_ind; try clear IHΓ'; simpl; intros len s inst s' Hsp.
    + depelim Hsp.
      ++ intuition auto.
         now eapply cumul_Sort_inv.
         exists []. split; try constructor; auto.
      ++ now eapply cumul_Sort_Prod_inv in c.
    + rewrite app_length /= in len; elimtype False; lia.
  - intros len s inst s' Hsp.
    destruct Γ' using rev_ind; try clear IHΓ'.
    -- depelim Hsp. 1:intuition auto.
      --- now eapply cumul_Sort_inv.
      --- exists []; split; try constructor; auto.
      --- now eapply cumul_Sort_Prod_inv in c.
    -- rewrite app_length /= in len.
      rewrite it_mkProd_or_LetIn_app in Hsp.
      destruct x as [na [b|] ty]; simpl in *; rewrite /mkProd_or_LetIn /= in Hsp.
      + rewrite context_assumptions_app /= Nat.add_0_r.
        eapply typing_spine_letin_inv in Hsp; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in Hsp.
        specialize (IHn (subst_context [b] 0 l)).
        forward IHn. {
          rewrite app_context_assoc in wfΓ'.
          apply All_local_env_app_inv in wfΓ' as [wfb wfa].
          depelim wfb.
          eapply substitution_wf_local. eauto. 
          epose proof (cons_let_def Σ Γ [] [] na b ty ltac:(constructor)).
          rewrite !subst_empty in X. eapply X. auto.
          eapply All_local_env_app; split.
          constructor; auto. apply wfa. }
        forward IHn by rewrite subst_context_length; lia.
        specialize (IHn s inst s' Hsp). 
        split. now rewrite context_assumptions_subst in IHn.
        destruct IHn as [[instlen leq] [instsubst [wfdom wfcodom cs subi]]].
        exists (instsubst ++ [subst0 [] b]).
        split; auto.
        * apply context_subst_app_inv. cbn.
          rewrite !skipn_0 {1}subst_empty.
          assert(#|l| <= n) by lia.
          rewrite context_assumptions_subst in instlen.
          pose proof (context_subst_length cs). rewrite subst_context_length in H0.
          rewrite !(firstn_app_left _ 0). lia. simpl. rewrite !app_nil_r.
          split. now rewrite H0 skipn_all_app.
          rewrite H0 skipn_all_app. repeat constructor.
        * apply subslet_app. now rewrite subst_empty.
          repeat constructor.
          rewrite app_context_assoc in wfΓ'. simpl in wfΓ'.
          apply wf_local_app_l in wfΓ'. depelim wfΓ'; now rewrite !subst_empty.
      + rewrite context_assumptions_app /=.
        depelim Hsp. 
        now eapply cumul_Prod_Sort_inv in c.
        eapply cumul_Prod_inv in c as [conva cumulB].
        eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cumulB; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
        specialize (IHn (subst_context [hd] 0 l)).
        forward IHn. {
          rewrite app_context_assoc in wfΓ'.
          apply All_local_env_app_inv in wfΓ' as [wfb wfa]; eauto.
          depelim wfb. 
          eapply substitution_wf_local. auto. 
          constructor. constructor. rewrite subst_empty.
          eapply type_Cumul'. eapply t.
          eapply l0.
          eapply conv_cumul; auto. now symmetry. 
          eapply All_local_env_app; eauto; split.
          constructor; eauto. eapply isType_tProd in i; intuition eauto. }
        forward IHn by rewrite subst_context_length; lia.
        specialize (IHn s tl s'). 
        rewrite context_assumptions_subst in IHn.
        eapply typing_spine_strengthen in Hsp.
        3:eapply cumulB. all:eauto.
        simpl. specialize (IHn Hsp).
        destruct IHn as [[instlen leq] [instsubst [wfdom wfcodom cs subi]]].
        intuition auto. lia.
        exists (instsubst ++ [hd]).
        split; auto.
        * apply context_subst_app_inv. cbn.
          rewrite !skipn_S skipn_0.
          assert(#|l| <= n) by lia.
          pose proof (context_subst_length cs). rewrite subst_context_length in H0.
          rewrite !(firstn_app_left _ 0). lia. simpl. rewrite !app_nil_r.
          split. now rewrite H0 skipn_all_app.
          rewrite H0 skipn_all_app. apply (context_subst_ass _ []). constructor.
        * apply subslet_app => //.
          repeat constructor.
          rewrite app_context_assoc in wfΓ'. simpl in wfΓ'.
          apply wf_local_app_l in wfΓ'. depelim wfΓ'.
          rewrite !subst_empty. red in l0.
          eapply type_Cumul'; eauto. eapply conv_cumul. now symmetry.
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

Lemma typing_spine_it_mkProd_or_LetIn_gen {cf:checker_flags} Σ Γ Δ Δ' T args s s' args' T' : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args s' = Some s -> 
  typing_spine Σ Γ (subst0 s T) args' T' ->
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s (Δ' ,,, Δ) ->
  isType Σ Γ (it_mkProd_or_LetIn Δ' (it_mkProd_or_LetIn Δ T)) ->
  typing_spine Σ Γ (subst0 s' (it_mkProd_or_LetIn Δ T)) (args ++ args') T'.
Proof.
  intros wfΣ.
  generalize (le_n #|Δ|).
  generalize (#|Δ|) at 2.
  induction n in Δ, Δ', args, s, s', T |- *.
  - destruct Δ using rev_ind.
    + intros le Hsub Hsp.
      destruct args; simpl; try discriminate.
      simpl in Hsub. now depelim Hsub.
    + rewrite app_length /=; intros; elimtype False; lia.
  - destruct Δ using rev_ind.
    1:intros le Hsub Hsp; destruct args; simpl; try discriminate;
    simpl in Hsub; now depelim Hsub.
  clear IHΔ.
  rewrite app_length /=; intros Hlen Hsub Hsp Hargs.
  rewrite context_assumptions_app in Hargs.
  destruct x as [na [b|] ty]; simpl in *.
  * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite Nat.add_0_r in Hargs.
    rewrite rev_app_distr in Hsub. simpl in Hsub.
    intros subs. rewrite app_context_assoc in subs.
    specialize (IHn Δ _ T args s _ ltac:(lia) Hsub Hsp Hargs subs).
    intros Har. forward IHn.
    rewrite it_mkProd_or_LetIn_app.
    now simpl.
    eapply typing_spine_letin; auto.
    rewrite /subst1.
    now rewrite -subst_app_simpl.
  * rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    rewrite rev_app_distr in Hsub. 
    simpl in Hsub. destruct args; try discriminate.
    simpl in Hargs. rewrite Nat.add_1_r in Hargs. noconf Hargs.
    intros subs. rewrite app_context_assoc in subs.    
    specialize (IHn Δ _ T args s _ ltac:(lia) Hsub Hsp H subs).
    intros Har.
    forward IHn. now rewrite it_mkProd_or_LetIn_app.
    eapply subslet_app_inv in subs as [subsl subsr].
    depelim subsl.
    have Hskip := make_context_subst_skipn Hsub. 
    rewrite List.rev_length in Hskip. rewrite Hskip in H0; noconf H0.
    simpl; eapply typing_spine_prod; auto; first
    now rewrite /subst1 -subst_app_simpl.
    eapply isType_substitution_it_mkProd_or_LetIn in Har; eauto.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Δ T args s args' T' : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args [] = Some s -> 
  typing_spine Σ Γ (subst0 s T) args' T' ->
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
Proof.
  intros. 
  pose proof (typing_spine_it_mkProd_or_LetIn_gen Σ Γ Δ [] T args s [] args' T'); auto.
  now rewrite subst_empty app_context_nil_l in X3.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn' {cf:checker_flags} Σ Γ Δ T args s args' T' : 
  wf Σ.1 ->
  spine_subst Σ Γ args s Δ ->
  typing_spine Σ Γ (subst0 s T) args' T' ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
Proof.
  intros. destruct X0.
  eapply typing_spine_it_mkProd_or_LetIn; eauto.
  eapply make_context_subst_spec_inv. now rewrite List.rev_involutive.
  now pose proof (context_subst_length2 inst_ctx_subst0).
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_close {cf:checker_flags} Σ Γ Δ T args s : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args [] = Some s -> 
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args (subst0 s T).
Proof.
  intros. 
  pose proof (typing_spine_it_mkProd_or_LetIn_gen Σ Γ Δ [] T args s [] []); auto.
  rewrite app_nil_r subst_empty in X2. apply X2; eauto.
  constructor. 2:eauto.
  eapply isType_substitution_it_mkProd_or_LetIn; eauto with pcuic. pcuic.
  now rewrite app_context_nil_l.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_close_eq {cf:checker_flags} Σ Γ Δ T args s T' : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args [] = Some s -> 
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  T' = (subst0 s T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T'.
Proof.
  intros; subst; now apply typing_spine_it_mkProd_or_LetIn_close.
Qed. 

Lemma typing_spine_it_mkProd_or_LetIn_close' {cf:checker_flags} Σ Γ Δ T args s T' : 
  wf Σ.1 ->
  spine_subst Σ Γ args s Δ ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  T' = (subst0 s T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T'.
Proof.
  intros wfΣ [].
  intros; eapply typing_spine_it_mkProd_or_LetIn_close_eq; eauto.
  eapply make_context_subst_spec_inv.
  now rewrite List.rev_involutive.
  now eapply context_subst_length2 in inst_ctx_subst0.
Qed. 


Lemma context_subst_subst Δ inst0 s Γ inst s'  :
  context_subst Δ inst0 s ->
  context_subst (subst_context s 0 Γ) inst s' ->
  context_subst (Δ ,,, Γ) (inst0 ++ inst) (s' ++ s).
Proof.
induction Γ in inst, s' |- *.
+ intros HΔ Hi. depelim Hi.
  now rewrite app_nil_r.
+ intros H' Hsub. 
  rewrite subst_context_snoc0 in Hsub.
  destruct a as [na [b|] ty];
  depelim Hsub.
  - specialize (IHΓ _ _ H' Hsub).
    assert(#|Γ| = #|s0|) as ->.
    { apply context_subst_length in Hsub.
      now rewrite subst_context_length in Hsub. }
    rewrite -(subst_app_simpl s0 s 0 b).
    simpl. now constructor.
  - specialize (IHΓ _ _ H' Hsub).
    assert(#|Γ| = #|s0|).
    { apply context_subst_length in Hsub.
      now rewrite subst_context_length in Hsub. }
    rewrite app_assoc /=. now constructor.
Qed.

Lemma spine_subst_conv {cf:checker_flags} Σ Γ inst insts Δ inst' insts' Δ' :
  wf Σ.1 ->
  spine_subst Σ Γ inst insts Δ ->
  spine_subst Σ Γ inst' insts' Δ' ->
  All2_fold (fun Δ Δ' => conv_decls Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ' ->
  All2 (conv Σ Γ) inst inst' -> All2 (conv Σ Γ) insts insts'.
Proof.
  move=> wfΣ [_ wf cs sl] [_ _ cs' sl'] cv.
  move: inst insts cs wf sl inst' insts' cs' sl'.
  induction cv; intros; depelim cs; depelim cs'.
  1:constructor; auto.
  all:depelim p.
  - eapply All2_app_inv in X as [[l1 l2] [[? ?] ?]].
    depelim a2. depelim a2. apply app_inj_tail in e0 as [? ?]; subst.
    depelim sl; depelim sl'; depelim wf.
    specialize (IHcv _ _ cs wf sl _ _ cs' sl' a1).
    constructor; auto.
  - depelim sl; depelim sl'; depelim wf.
    specialize (IHcv _ _ cs wf sl _ _ cs' sl' X).
    constructor; auto.
    eapply (subst_conv _ _ _ []); eauto.
Qed.

Lemma spine_subst_subst {cf:checker_flags} Σ Γ Γ0 Γ' i s Δ sub : 
  wf Σ.1 ->
  spine_subst Σ (Γ ,,, Γ0 ,,, Γ') i s Δ ->
  subslet Σ Γ sub Γ0 ->
  spine_subst Σ (Γ ,,, subst_context sub 0 Γ') (map (subst sub #|Γ'|) i) (map (subst sub #|Γ'|) s)
   (subst_context sub #|Γ'| Δ).
Proof.
  move=> wfΣ [wfl wfΔ cs subl] subs.
  split.
  eapply substitution_wf_local; eauto.
  pose proof (subst_context_app sub 0 Γ' Δ). rewrite Nat.add_0_r in H. rewrite -app_context_assoc -H.
  clear H.
  eapply substitution_wf_local; eauto. now rewrite app_context_assoc.
  clear subl wfl wfΔ.
  induction cs in Γ, Γ0, Γ', subs |- *; rewrite ?subst_context_snoc ?map_app; simpl; try constructor.
  eapply IHcs; eauto.
  specialize (IHcs _ _ Γ' subs).
  epose proof (context_subst_def _ _ _ na (subst sub (#|Γ1| + #|Γ'|) b) (subst sub (#|Γ1| + #|Γ'|) t) IHcs).
  rewrite /subst_decl /map_decl /=.
  rewrite distr_subst. 
  now rewrite (context_subst_length cs) in X |- *.
  clear cs wfΔ.
  induction subl; rewrite ?subst_context_snoc ?map_app; simpl; try constructor; auto.
  - eapply substitution in t0; eauto. simpl.
    rewrite -(subslet_length subl).
    now rewrite -distr_subst.
  - eapply substitution in t0; eauto. simpl.
    rewrite -(subslet_length subl).
    rewrite !distr_subst in t0.
    epose proof (cons_let_def _  _ _ _ _  _ _ IHsubl t0).
    now rewrite - !distr_subst in X.
Qed.

Lemma spine_subst_subst_first {cf:checker_flags} Σ Γ Γ' i s Δ sub : 
  wf Σ.1 ->
  spine_subst Σ (Γ ,,, Γ') i s Δ ->
  subslet Σ [] sub Γ ->
  spine_subst Σ (subst_context sub 0 Γ') (map (subst sub #|Γ'|) i) (map (subst sub #|Γ'|) s)
   (subst_context sub #|Γ'| Δ).
Proof.
  move=> wfΣ sp subs.
  epose proof (spine_subst_subst Σ [] Γ Γ' i s Δ sub wfΣ).
  rewrite !app_context_nil_l in X. apply X; auto.
Qed.

Lemma weaken_subslet {cf:checker_flags} Σ s Δ Γ Γ' :
  wf Σ.1 ->
  wf_local Σ Γ -> wf_local Σ Γ' ->
  subslet Σ Γ' s Δ -> subslet Σ (Γ ,,, Γ') s Δ.
Proof.
  intros wfΣ wfΔ wfΓ'.
  induction 1; constructor; auto.
  + eapply (weaken_ctx Γ); eauto.
  + eapply (weaken_ctx Γ); eauto.
Qed.

Lemma spine_subst_weaken {cf:checker_flags} Σ Γ i s Δ Γ' : 
  wf Σ.1 ->
  wf_local Σ Γ' ->
  spine_subst Σ Γ i s Δ ->
  spine_subst Σ (Γ' ,,, Γ) i s Δ.
Proof.
  move=> wfΣ wfl [cs subl].
  split; auto.
  eapply weaken_wf_local => //.
  rewrite -app_context_assoc. eapply weaken_wf_local => //.
  eapply weaken_subslet; eauto.
Qed.



Lemma spine_subst_app_inv {cf:checker_flags} Σ Γ Δ Δ' inst inst' insts :
  wf Σ.1 -> 
  #|inst| = context_assumptions Δ ->
  spine_subst Σ Γ (inst ++ inst') insts (Δ ,,, Δ') ->
  spine_subst Σ Γ inst (skipn #|Δ'| insts) Δ *
  spine_subst Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ').
Proof.
  intros wfΣ len sp.
  destruct sp as [wfdom wfcodom cs subs].
  eapply context_subst_app in cs as [csl csr].
  rewrite skipn_all_app_eq in csl => //.
  rewrite (firstn_app_left _ 0) in csr => //. lia.
  rewrite firstn_0 in csr => //. rewrite app_nil_r in csr.
  eapply subslet_app_inv in subs as [sl sr].
  split; split; auto. rewrite app_context_assoc in wfcodom.
  now eapply All_local_env_app_inv in wfcodom as [? ?].
  eapply substitution_wf_local; eauto.
  now rewrite app_context_assoc in wfcodom.
Qed.

Lemma spine_subst_inst {cf:checker_flags} Σ ext u Γ i s Δ  :
  wf Σ.1 ->
  wf_global_ext Σ.1 ext ->
  spine_subst (Σ.1, ext) Γ i s Δ ->
  consistent_instance_ext Σ ext u ->
  spine_subst Σ (subst_instance u Γ)
    (map (subst_instance u) i)
    (map (subst_instance u) s)
    (subst_instance u Δ).
Proof.
  intros wfΣ wfext [wfdom wfcodom cs subsl] cu.
  split.
  eapply wf_local_subst_instance; eauto.
  rewrite -subst_instance_app_ctx.
  eapply wf_local_subst_instance; eauto.
  clear -cs cu wfext wfΣ.
  induction cs; simpl; rewrite ?map_app; try constructor; auto.
  rewrite subst_instance_cons; simpl.
  rewrite subst_instance_subst.
  constructor; auto.

  clear -subsl cu wfΣ wfext.
  induction subsl; simpl; rewrite ?subst_instance_subst; constructor; auto.
  * destruct Σ as [Σ univs].
    rewrite -subst_instance_subst.
    eapply (typing_subst_instance'' Σ); simpl; auto.
    apply wfext. simpl in wfext. apply t0. 
    apply wfext. auto.
  * rewrite - !subst_instance_subst. simpl.
    destruct Σ as [Σ univs].
    eapply (typing_subst_instance'' Σ); simpl; auto.
    apply wfext. simpl in wfext. apply t0. 
    apply wfext. auto.
Qed.

Lemma spine_subst_weakening {cf:checker_flags} Σ Γ i s Δ Γ' : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ') ->
  spine_subst Σ Γ i s Δ ->
  spine_subst Σ (Γ ,,, Γ') (map (lift0 #|Γ'|) i) (map (lift0 #|Γ'|) s) (lift_context #|Γ'| 0 Δ).
Proof.
  move=> wfΣ wfl [cs subl].
  split; auto.
  eapply weakening_wf_local; eauto.
  now apply context_subst_lift.
  now apply subslet_lift.
Qed.

Lemma ctx_inst_length {cf:checker_flags} Σ Γ args Δ :
  ctx_inst Σ Γ args Δ -> 
  #|args| = context_assumptions Δ.
Proof.
  induction 1; simpl; auto.
  rewrite /subst_telescope in IHX.
  rewrite context_assumptions_mapi in IHX. congruence.
  rewrite context_assumptions_mapi in IHX. congruence.
Qed.

Lemma ctx_inst_subst {cf:checker_flags} Σ Γ Γ0 Γ' i Δ sub : 
  wf Σ.1 ->
  ctx_inst Σ (Γ ,,, Γ0 ,,, Γ') i Δ ->
  subslet Σ Γ sub Γ0 ->
  ctx_inst Σ (Γ ,,, subst_context sub 0 Γ') (map (subst sub #|Γ'|) i) (subst_telescope sub #|Γ'| Δ).
Proof.
  move=> wfΣ ctxinst subs.
  induction ctxinst in sub, subs |- *.
  - simpl; intros; constructor; auto.
  - intros. rewrite subst_telescope_cons; simpl; constructor.
    * simpl. eapply substitution; eauto.
    * specialize (IHctxinst _ subs).
      now rewrite (subst_telescope_comm [i]).
  - intros. rewrite subst_telescope_cons; simpl; constructor.
    specialize (IHctxinst _ subs).
    now rewrite (subst_telescope_comm [b]).
Qed.

Lemma ctx_inst_weaken {cf:checker_flags} Σ Γ i Δ Γ' : 
  wf Σ.1 ->
  wf_local Σ Γ' ->
  ctx_inst Σ Γ i Δ ->
  ctx_inst Σ (Γ' ,,, Γ) i Δ.
Proof.
  move=> wfΣ wfl subl.
  induction subl; constructor; auto.
  now eapply (weaken_ctx Γ').
Qed.

Lemma make_context_subst_tele s s' Δ inst sub : 
  make_context_subst (subst_telescope s' #|s| Δ) inst s = Some sub ->
  make_context_subst Δ inst (s ++ s') = Some (sub ++ s').
Proof.
  induction Δ in s, s', sub, inst |- *.
  simpl. destruct inst; try discriminate.
  intros [= ->]. reflexivity.
  rewrite subst_telescope_cons.
  destruct a as [na [b|] ty]; simpl in *.
  intros. specialize (IHΔ _ _ _ _ H).
  now rewrite -subst_app_simpl in IHΔ.
  destruct inst. discriminate.
  intros. now specialize (IHΔ _ _ _ _ H).
Qed.

Fixpoint ctx_inst_sub {cf:checker_flags} {Σ Γ Δ args} (c : ctx_inst Σ Γ args Δ) {struct c} : list term :=
  match c return _ with
  | ctx_inst_nil => []
  | ctx_inst_ass na t i inst Δ P c => ctx_inst_sub c ++ [i]
  | ctx_inst_def na b t inst Δ c => ctx_inst_sub c ++ [b]
  end.

Lemma ctx_inst_sub_spec {cf:checker_flags} {Σ Γ Δ args} (c : ctx_inst Σ Γ args Δ) : 
  make_context_subst Δ args [] = Some (ctx_inst_sub c).
Proof.
  induction c; simpl; auto.
  now apply (make_context_subst_tele [] [i]) in IHc.
  apply (make_context_subst_tele [] [b]) in IHc.
  now rewrite subst_empty.
Qed.
  
Lemma subst_telescope_empty k Δ : subst_telescope [] k Δ = Δ.
Proof.
  unfold subst_telescope, mapi. generalize 0. induction Δ; simpl; auto.
  intros.
  destruct a as [na [b|] ty]; unfold map_decl at 1; simpl; rewrite !subst_empty.
  f_equal. apply IHΔ.
  f_equal. apply IHΔ.
Qed.

Lemma subst_telescope_app s k Γ Δ : subst_telescope s k (Γ ++ Δ) = subst_telescope s k Γ ++ 
  subst_telescope s (#|Γ| + k) Δ.
Proof.
  rewrite /subst_telescope /mapi.
  rewrite mapi_rec_app. f_equal. rewrite mapi_rec_add.
  apply mapi_rec_ext. intros. destruct x as [na [b|] ty]; simpl; f_equal; f_equal; lia.
Qed.
  
Hint Extern 0 => lia : lia.

Lemma context_assumptions_subst_telescope s k Δ : context_assumptions (subst_telescope s k Δ) = 
  context_assumptions Δ.
Proof.
  rewrite /subst_telescope /mapi. generalize 0. 
  induction Δ; simpl; auto.
  destruct a as [na [b|] ty]; simpl; auto with lia.
  intros. specialize (IHΔ (S n)). lia.
Qed.

Lemma subst_app_telescope s s' k Γ : 
  subst_telescope (s ++ s') k Γ = subst_telescope s k (subst_telescope s' (#|s| + k) Γ).
Proof.
  rewrite /subst_telescope /mapi.
  rewrite mapi_rec_compose.
  apply mapi_rec_ext. intros. destruct x as [na [b|] ty]; simpl; unfold map_decl; simpl; f_equal.
  rewrite subst_app_simpl. f_equal; f_equal. f_equal. lia.
  rewrite subst_app_simpl. f_equal; f_equal. lia.
  rewrite subst_app_simpl. f_equal; f_equal. lia.
Qed.

Lemma make_context_subst_length Γ args acc sub : make_context_subst Γ args acc = Some sub ->
  #|sub| = #|Γ| + #|acc|.
Proof.
  induction Γ in args, acc, sub |- *; simpl.
  destruct args; try discriminate. now intros [= ->].
  destruct a as [? [b|] ty] => /=. intros H.
  specialize (IHΓ _ _ _ H). simpl in IHΓ. lia.
  destruct args; try discriminate.
  intros H.
  specialize (IHΓ _ _ _ H). simpl in IHΓ. lia.
Qed.

Lemma subst_telescope_length s k Γ : #|subst_telescope s k Γ| = #|Γ|.
Proof.
  now rewrite /subst_telescope mapi_length.
Qed.

Lemma arity_spine_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Δ T args s args' T' : 
  wf Σ.1 ->
  spine_subst Σ Γ args s Δ ->
  arity_spine Σ Γ (subst0 s T) args' T' ->
  arity_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
Proof.
  intros wfΣ sp asp. destruct sp as [wfΓ _ cs subsl].
  move: Δ args s T cs subsl asp.
  induction Δ using ctx_length_rev_ind => args s T cs subsl asp.
  - depelim cs. depelim  subsl.
    now rewrite subst_empty in asp.
  - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    destruct d as [na [b|] ty]; simpl in *.
    * constructor. rewrite /subst1 subst_it_mkProd_or_LetIn.
      rewrite Nat.add_0_r.
      apply subslet_app_inv in subsl as [subsl subsl'].
      depelim subsl; depelim subsl.
      apply context_subst_app in cs as [cs cs'].
      simpl in *. rewrite skipn_0 in cs.
      specialize (X (subst_context (skipn #|Γ0| s) 0 Γ0) ltac:(now autorewrite with len) _ _ 
        (subst [b] #|Γ0| T) cs subsl').
      rewrite subst_empty in H.
      rewrite H in X. apply X.
      rewrite -subst_app_simpl'.
      apply subslet_length in subsl'.
      now autorewrite with len in subsl'.
      rewrite -H.  now rewrite firstn_skipn.
    * apply subslet_app_inv in subsl as [subsl subsl'].
      depelim subsl; depelim subsl.
      apply context_subst_app in cs as [cs cs'].
      simpl in *.
      destruct args. depelim cs'.
      depelim cs'. discriminate.
      simpl in *. rewrite skipn_S skipn_0 in cs.
      rewrite subst_empty in t0.
      depelim cs'; depelim cs'. simpl in H; noconf H.
      rewrite H1 in H0. noconf H0.
      constructor; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn.
      rewrite Nat.add_0_r.
      specialize (X (subst_context (skipn #|Γ0| s) 0 Γ0) ltac:(now autorewrite with len) _ _ 
      (subst [t1] #|Γ0| T) cs subsl').
      rewrite -{1}H1. apply X.
      rewrite -subst_app_simpl'.
      apply subslet_length in subsl'.
      now autorewrite with len in subsl'.
      rewrite -H1. now rewrite firstn_skipn.
Qed.

Lemma arity_spine_it_mkProd_or_LetIn_Sort {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} Γ ctx s s' args inst : 
  wf_universe Σ s' ->
  leq_universe Σ s s' ->
  spine_subst Σ Γ args inst ctx ->
  arity_spine Σ Γ (it_mkProd_or_LetIn ctx (tSort s)) args (tSort s').
Proof.
  intros wfs le sp. rewrite -(app_nil_r args).
  eapply arity_spine_it_mkProd_or_LetIn => //.
  eauto. constructor.
  eapply isType_Sort; eauto.
  eapply sp. simpl. constructor. now constructor.
Qed.

Lemma ctx_inst_app {cf:checker_flags} {Σ Γ} {Δ : context} {Δ' args} 
  (c : ctx_inst Σ Γ args (Δ ++ Δ')) :
  ∑ (dom : ctx_inst Σ Γ (firstn (context_assumptions Δ) args) Δ),
    ctx_inst Σ Γ (skipn (context_assumptions Δ) args) (subst_telescope (ctx_inst_sub dom) 0 Δ').    
Proof.
  revert args Δ' c.
  induction Δ using ctx_length_ind; intros.
  simpl. unshelve eexists. constructor.
  simpl. rewrite skipn_0. now rewrite subst_telescope_empty.
  depelim c; simpl.
  - specialize (X (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    rewrite subst_telescope_app in c.
    specialize (X _ _ c).
    rewrite context_assumptions_subst_telescope in X.
    destruct X as [dom codom].
    unshelve eexists.
    constructor; auto. simpl.
    pose proof (ctx_inst_sub_spec dom) as Hsub.
    simpl in *. rewrite Nat.add_0_r in codom. rewrite skipn_S.
    rewrite subst_app_telescope.
    apply make_context_subst_length in Hsub.
    rewrite subst_telescope_length Nat.add_0_r in Hsub.
    now rewrite Hsub Nat.add_0_r.
  - specialize (X (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
    rewrite subst_telescope_app in c.
    specialize (X _ _ c).
    rewrite context_assumptions_subst_telescope in X.
    destruct X as [dom codom].
    unshelve eexists.
    constructor; auto. simpl.
    pose proof (ctx_inst_sub_spec dom) as Hsub.
    simpl in *. rewrite Nat.add_0_r in codom.
    rewrite subst_app_telescope.
    apply make_context_subst_length in Hsub.
    rewrite subst_telescope_length Nat.add_0_r in Hsub.
    now rewrite Hsub Nat.add_0_r.
Qed.

Lemma ctx_inst_sub_eq {cf:checker_flags} {Σ Γ} {Δ : context} {Δ' args args'} (c : ctx_inst Σ Γ args Δ) (d : ctx_inst Σ Γ args' Δ') :
  args' = args ->
  Δ = Δ' -> ctx_inst_sub c = ctx_inst_sub d.
Proof.
  intros -> ->. induction c; depelim d; auto; simpl in *; now rewrite (IHc d).
Qed.

Lemma ctx_inst_subst_length {cf:checker_flags} {Σ Γ} {Δ : context} {args} (c : ctx_inst Σ Γ args Δ) :
  #|ctx_inst_sub c| = #|Δ|.
Proof.
  induction c; simpl; auto; try lia;
  rewrite app_length IHc subst_telescope_length /=; lia.
Qed.

Lemma ctx_inst_app_len {cf:checker_flags} {Σ Γ} {Δ : context} {Δ' args} (c : ctx_inst Σ Γ args (Δ ++ Δ')) :
  let (dom, codom) := ctx_inst_app c in
  ctx_inst_sub c = ctx_inst_sub codom ++ ctx_inst_sub dom.
Proof.
  destruct (ctx_inst_app c).
  induction Δ using ctx_length_ind in Δ', c, x, args, c0 |- *. simpl in *. depelim x. simpl in *.
  rewrite app_nil_r; apply ctx_inst_sub_eq. now rewrite skipn_0.
  now rewrite subst_telescope_empty.
  simpl in *. destruct d as [na [b|] ty]; simpl in *.
  depelim c; simpl in *. 
  depelim x; simpl in *.
  injection H0. discriminate. injection H0. discriminate.
  specialize (H (subst_telescope [b] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
  revert c. rewrite subst_telescope_app.
  intros c.
  specialize (H  _ _ c). simpl in *.
  revert H. rewrite context_assumptions_subst_telescope.
  intros.
  specialize (H x).
  revert c0. rewrite subst_app_telescope.
  rewrite (ctx_inst_subst_length x) subst_telescope_length.
  intros c1.
  now rewrite (H c1) app_assoc.

  depelim c; depelim x; simpl in *.
  specialize (H (subst_telescope [i] 0 Γ0) ltac:(now rewrite /subst_telescope mapi_length)).
  revert c. rewrite subst_telescope_app. intros c.
  specialize (H _ _ c). simpl in *.
  revert H. rewrite context_assumptions_subst_telescope.
  intros. 
  specialize (H x).
  revert c0. rewrite subst_app_telescope.
  rewrite (ctx_inst_subst_length x) subst_telescope_length.
  intros c1.
  now rewrite (H c1) app_assoc.
Qed.

Lemma context_assumptions_rev Γ : context_assumptions (List.rev Γ) = context_assumptions Γ.
Proof.
  induction Γ; simpl; auto. rewrite context_assumptions_app IHΓ /=.
  destruct (decl_body a); simpl; lia.
Qed.

Lemma ctx_inst_def {cf:checker_flags} {Σ Γ args na b t} (c : ctx_inst Σ Γ args [vdef na b t]) :
  ((args = []) * (ctx_inst_sub c = [b]))%type.
Proof.
  depelim c; simpl in c. depelim c; simpl in *. constructor; simpl in *; auto.
Qed.

Lemma ctx_inst_ass {cf:checker_flags} {Σ Γ args na t} (c : ctx_inst Σ Γ args [vass na t]) : 
  ∑ i, ((args = [i]) * (lift_typing typing Σ Γ i (Some t)) * (ctx_inst_sub c = [i]))%type.
Proof.
  depelim c; simpl in *. 
  depelim c. exists i; constructor; auto.
Qed.

Lemma ctx_inst_spine_subst {cf:checker_flags} Σ Γ Δ args : 
  wf Σ.1 -> wf_local Σ Γ -> 
  wf_local Σ (Γ ,,, Δ) ->
  forall ci : ctx_inst Σ Γ args (List.rev Δ),
  spine_subst Σ Γ args (ctx_inst_sub ci) Δ.
Proof.
  move=> wfΣ wfΓ wfΔ ci.
  pose proof (ctx_inst_sub_spec ci) as msub.
  eapply make_context_subst_spec in msub.
  rewrite List.rev_involutive in msub.
  split; auto.
  move: ci msub.
  induction Δ in wfΔ, args |- *.
  simpl. intros ci. depelim ci. constructor.
  intros. simpl in ci.
  pose proof (ctx_inst_app_len ci).
  destruct (ctx_inst_app ci). rewrite H in msub |- *.
  clear ci H.
  simpl in c.
  apply (@context_subst_app [a]) in msub.
  simpl in msub.
  destruct a as [na [b|] ty]; simpl in *.
  - pose proof (ctx_inst_def c) as [Hargs Hinst].
    rewrite Hinst in msub |- *. simpl in *.
    destruct msub as [subl subr].
    rewrite skipn_S skipn_0 in subr.
    generalize dependent x. rewrite context_assumptions_rev.
    intros.
    depelim wfΔ.
    specialize (IHΔ _ wfΔ _ subr). constructor; auto.
    red in l0. eapply (substitution _ _ _ _ []); eauto.
  - pose proof (ctx_inst_ass c) as [i [[Hargs Hty] Hinst]].
    rewrite Hinst in msub |- *. simpl in *.
    destruct msub as [subl subr].
    rewrite skipn_S skipn_0 in subr subl.
    generalize dependent x. rewrite context_assumptions_rev.
    intros.
    depelim wfΔ.
    specialize (IHΔ _ wfΔ _ subr). constructor; auto.
Qed.

Lemma subst_instance_rev u Γ :
  subst_instance u (List.rev Γ) = List.rev (subst_instance u Γ).
Proof.
  now rewrite /subst_instance /subst_instance_context /= /map_context List.map_rev.
Qed.

Lemma subst_telescope_subst_context s k Γ :
  subst_telescope s k (List.rev Γ) = List.rev (subst_context s k Γ).
Proof.
  rewrite /subst_telescope subst_context_alt.
  rewrite rev_mapi. apply mapi_rec_ext.
  intros n [na [b|] ty] le le'; rewrite /= /subst_decl /map_decl /=; 
  rewrite List.rev_length Nat.add_0_r in le'; 
  f_equal. f_equal. f_equal. lia. f_equal; lia.
  f_equal; lia. 
Qed.

Lemma lift_context_subst_context n s Γ: lift_context n 0 (subst_context s 0 Γ) =
  subst_context s n (lift_context n 0 Γ). 
Proof.
  induction Γ in n, s |- *.
  - reflexivity.
  - rewrite !subst_context_snoc.
    rewrite !lift_context_snoc !subst_context_snoc.
    f_equal; auto.
    rewrite /lift_decl /subst_decl /map_decl.
    simpl. f_equal. unfold option_map. destruct (decl_body a).
    rewrite !subst_context_length lift_context_length Nat.add_0_r.
    rewrite commut_lift_subst_rec; auto. reflexivity.
    rewrite !subst_context_length lift_context_length Nat.add_0_r.
    rewrite commut_lift_subst_rec; auto.
Qed.

Lemma subst_app_context_gen s s' k Γ : subst_context (s ++ s') k Γ = subst_context s k (subst_context s' (k + #|s|) Γ).
Proof.
  induction Γ in k |- *; simpl; auto.
  rewrite !subst_context_snoc /= /subst_decl /map_decl /=. simpl.
  rewrite IHΓ. f_equal. f_equal.
  - destruct a as [na [b|] ty]; simpl; auto.
    f_equal. rewrite subst_context_length.
    now rewrite subst_app_simpl.
  - rewrite subst_context_length.
    now rewrite subst_app_simpl.
Qed.

Lemma closed_k_ctx_subst n k ctx : closedn_ctx k ctx = true -> subst_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  simpl.
  move/andb_and => /= [Hctx Hd].
  rewrite subst_context_snoc /snoc /= IHctx // subst_decl_closed //.
Qed.

Fixpoint all_rels (Γ : context) (n : nat) (k : nat) :=
  match Γ with
  | nil => nil
  | cons d vs =>
    match decl_body d with
    | Some b =>
      let s := all_rels vs (S n) k in
      (subst0 s (lift k #|s| b)) :: s
    | None => tRel n :: all_rels vs (S n) k
    end
  end.

Lemma all_rels_length Γ n k : #|all_rels Γ n k| = #|Γ|.
Proof.
  induction Γ in n, k |- *; simpl; auto.
  now destruct a as [? [?|] ?] => /=; simpl; rewrite IHΓ. 
Qed.

Lemma nth_error_all_rels_spec Γ n k x i : nth_error (all_rels Γ n k) i = Some x ->
  ∑ decl, (nth_error Γ i = Some decl) *
    match decl_body decl with
    | Some b => x = subst0 (all_rels (skipn (S i) Γ) (S n + i) k) (lift k (#|Γ| - S i) b)
    | None => x = tRel (n + i)
    end.
Proof.
  induction Γ in n, k, i, x |- *.
  simpl. destruct i; simpl; discriminate.
  destruct i; simpl.
  destruct a as [? [?|] ?]; simpl.
  intros [= <-].
  eexists; split; eauto. simpl.
  now rewrite skipn_S skipn_0 Nat.add_0_r all_rels_length.
  intros [= <-].
  eexists; split; eauto. simpl.
  now rewrite Nat.add_0_r.
  intros. destruct (decl_body a);  try discriminate.
  rewrite skipn_S. 
  specialize  (IHΓ _ _ _ _ H).
  rewrite Nat.add_succ_r. apply IHΓ.
  rewrite skipn_S. 
  specialize  (IHΓ _ _ _ _ H).
  rewrite Nat.add_succ_r. apply IHΓ.
Qed.

Require Import PCUICParallelReductionConfluence.

Lemma subst_lift_lift s k t : subst0 (map (lift0 k) s) (lift k #|s| t) = lift0 k (subst0 s t).
Proof.
  now rewrite (distr_lift_subst_rec _ _ _ 0 0).
Qed.
Hint Rewrite all_rels_length : len.

Lemma all_rels_lift (Δ : context) n : all_rels Δ n (n + #|Δ|) = map (lift0 n) (all_rels Δ 0 #|Δ|).
Proof.
  rewrite -{1}(Nat.add_0_r n).
  generalize 0 at 1 3. revert n.
  induction Δ at 1 3.
  simpl. auto.
  intros n n'.
  destruct a as [na [?|] ?]. simpl.
  f_equal.
  specialize (IHc n (S n')).
  rewrite Nat.add_succ_r in IHc.
  rewrite {1}IHc.
  rewrite all_rels_length.
  assert(#|all_rels c (S n') #|Δ| | = #|c|) by now autorewrite with len.
  rewrite -(simpl_lift _ _ _ _ #|c|); try lia.
  rewrite -{1}H.
  epose proof (distr_lift_subst _ _ n 0).
  rewrite Nat.add_0_r in H0. now erewrite <-H0.
  specialize (IHc n (S n')).
  now rewrite -IHc.
  simpl.
  f_equal.
  specialize (IHc n (S n')).
  now rewrite -IHc.
Qed.

Lemma all_rels_subst {cf:checker_flags} Σ Δ Γ t :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)).
Proof.
  intros wfΣ wf.
  assert(forall Γ' t (wf : wf_local Σ Γ'),
    ((All_local_env_over typing 
      (fun Σ Γ' wfΓ' t T _ => 
        forall Γ Δ, Γ' = Γ ,,, Δ ->        
        red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)))
        Σ Γ' wf) *  
        (match t with
        | Some t => forall Γ Δ, Γ' = Γ ,,, Δ ->        
            red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t))
        | None => unit  end))).
  clear t Δ Γ wf. intros Γ' t.
  Subterm.rec_wf_rel IH (Γ', t) (Subterm.lexprod _ _ (precompose lt (@length context_decl))
     (precompose lt (fun x => match x with Some t => S (PCUICSize.size t) | None => 0 end))).
  simpl.
  rename pr1 into cf.
  rename pr0 into Σ.
  rename pr2 into wfΣ.
  rename pr3 into Γ.
  rename pr4 into t. clear H0.
  intros wf.
  split.
  - specialize (IH cf Σ wfΣ).
    destruct wf.
    constructor.
    constructor. 
    apply (IH Γ t ltac:(left; simpl; lia) wf).
    intros; subst Γ.
    now apply (IH (Γ0 ,,, Δ) (Some t0) ltac:(left; simpl; lia) wf).
    constructor; auto.
    apply (IH Γ t ltac:(left; simpl; lia) wf).
    intros.
    now apply (IH Γ (Some b) ltac:(left; simpl; lia) wf).
    now apply (IH Γ (Some t0) ltac:(left; simpl; lia) wf).

  - destruct t; [|exact tt].
    intros Γ0 Δ ->.
    rename Γ0 into Γ.
    specialize (IH cf Σ).
    assert (All_local_env_over typing
    (fun (Σ : PCUICEnvironment.global_env_ext)
       (Γ'0 : PCUICEnvironment.context) (_ : wf_local Σ Γ'0) 
       (t T : term) (_ : Σ;;; Γ'0 |- t : T) =>
     forall Γ Δ : context,
     Γ'0 = Γ ,,, Δ ->
     red Σ.1 (Γ ,,, Δ) t (subst0 (all_rels Δ 0 #|Δ|) (lift #|Δ| #|Δ| t)))
    Σ _ wf).
    { specialize (IH wfΣ (Γ ,,, Δ) None).
      forward IH. simpl. right. lia.
      apply (IH wf). }
    clear IH.

  change (Γ ,,, Δ) with (Γ ,,, Δ ,,, []).
  rewrite -{3}(Nat.add_0_r #|Δ|).
  change 0 with #|@nil context_decl| at 2 3.
  generalize (@nil context_decl) as Δ'.
  
  induction t using term_ind_size_app; try solve [constructor]; intros Δ'.
  * simpl.
     destruct (leb_spec_Set (#|Δ|  +#|Δ'|) n); simpl.
    **
      elim: leb_spec_Set => Hle.
      destruct (nth_error_spec (all_rels Δ 0 #|Δ|) (#|Δ| + n - #|Δ'|));
      rewrite all_rels_length in l0 |- *. lia.
      assert (#|Δ| + n - #|Δ| = n) as -> by lia.
      reflexivity. lia.
    **
      elim: leb_spec_Set => Hle.
      destruct (nth_error_spec (all_rels Δ 0 #|Δ|) (n - #|Δ'|));
      rewrite all_rels_length in l0 |- *; try lia.
      eapply nth_error_all_rels_spec in e.
      destruct e as [decl [Hnth Hdecl]].
      destruct decl as [? [?|] ?]; simpl in Hdecl; subst x.
      assert (n = #|Δ'| + (n - #|Δ'|)). lia.
      rewrite {1}H.
      change (tRel  (#|Δ'| + (n - #|Δ'|))) with
          (lift0 #|Δ'| (tRel (n - #|Δ'|))).
      eapply (weakening_red _ _ []); auto.
      simpl.
      set (i := n - #|Δ'|) in *. clearbody i.
      clear l Hle H.

      etransitivity.
      + eapply red1_red. constructor.
        rewrite nth_error_app_lt; auto.
        rewrite Hnth. reflexivity.
      + rewrite -{1 3 4}(firstn_skipn (S i) Δ).
        rewrite app_context_assoc.
        assert (Hf:#|firstn (S i) Δ| = S i) by now rewrite firstn_length_le; lia.
        rewrite app_length Hf.
        rewrite all_rels_lift.
        erewrite <-(simpl_lift _ _ _ _ #|skipn (S i) Δ|); try lia.
    
        epose proof (distr_lift_subst (lift #|skipn (S i) Δ| (#|Δ| - S i) t) 
        (all_rels (skipn (S i) Δ) 0 #|skipn (S i) Δ|) (S i) 0).
        rewrite Nat.add_0_r in H.
        autorewrite with len in H.
        rewrite -{}H.
        rewrite -{3 4}Hf.
        eapply (weakening_red _ _ []); auto. simpl.
        rewrite skipn_length. lia.
        simpl.
        unshelve eapply (nth_error_All_local_env_over (n:=i)) in X.
        2:{ rewrite nth_error_app_lt //. apply Hnth. }
        destruct X as [_ [Xb Xt]].
        specialize (Xb Γ (skipn (S i) Δ)).
        forward Xb. rewrite skipn_app. unfold app_context. f_equal.
        assert(S i - #|Δ| = 0) by lia. rewrite H. apply skipn_0.
        now rewrite skipn_length in Xb; try lia.
        rewrite skipn_length; lia.
      + simpl. assert(#|Δ'| + (n - #|Δ'|) = n) as -> by lia.
        reflexivity.
      + reflexivity.

  * simpl; eapply red_evar.
    do 2 apply All2_map_right.
    apply (All_All2 X0); auto.

  * simpl. eapply red_prod. auto.
    specialize (IHt2 (Δ' ,, vass n t1)).
    now rewrite -Nat.add_succ_r.

  * simpl; eapply red_abs; auto.
    rewrite -Nat.add_succ_r.
    eapply (IHt2 (Δ' ,, vass n _)).

  * simpl; eapply red_letin; auto.
    rewrite -Nat.add_succ_r.
    eapply (IHt3 (Δ' ,, vdef n _ _)).

  * simpl; eapply red_app; auto.
  * todo "case".
     (* simpl; eapply red_case; auto.
    red in X0.
    do 2 eapply All2_map_right.
    eapply (All_All2 X0).
    simpl; intros.
    split; auto. *)

  * simpl; eapply red_proj_c. auto.

  * simpl; eapply red_fix_congr.
    do 2 eapply All2_map_right.
    eapply (All_All2 X0); simpl; intuition auto.
    rewrite map_length.
    specialize (b (Δ' ,,, fix_context m)).
    autorewrite with len in b.
    rewrite Nat.add_shuffle3.
    now rewrite app_context_assoc in b.

  * simpl. eapply red_cofix_congr.
    do 2 eapply All2_map_right.
    eapply (All_All2 X0); simpl; intuition auto.
    rewrite map_length.
    specialize (b (Δ' ,,, fix_context m)).
    autorewrite with len in b.
    rewrite Nat.add_shuffle3.
    now rewrite app_context_assoc in b.
  
- specialize (X (Γ ,,, Δ)  (Some t) wf). simpl in X.
  apply X. reflexivity.
Qed.

Lemma all_rels_subst_lift {cf:checker_flags} Σ Δ Γ Δ' t :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  Σ ;;; Γ ,,, Δ ,,, Δ' |- lift0 #|Δ'| t =
   subst0 (all_rels Δ #|Δ'| (#|Δ| + #|Δ'|)) (lift (#|Δ| + #|Δ'|) #|Δ| t).
Proof.
  intros.
  rewrite Nat.add_comm.
  erewrite <-(simpl_lift _ _ _ _ #|Δ|); try lia.
  rewrite all_rels_lift.
  epose proof (distr_lift_subst (lift #|Δ| #|Δ| t) (all_rels Δ 0 #|Δ|) #|Δ'| 0).
  rewrite Nat.add_0_r in H.
  rewrite -{2}(all_rels_length Δ 0 #|Δ|).
  rewrite -H.
  apply red_conv.
  eapply (weakening_red _ _ []); auto. clear H.
  simpl.
  eapply all_rels_subst; auto.
Qed.

Lemma spine_subst_to_extended_list_k {cf:checker_flags} Σ Δ Γ :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  spine_subst Σ (Γ ,,, Δ) (reln [] 0 Δ) (all_rels Δ 0 #|Δ|)
    (lift_context #|Δ| 0 Δ).
Proof.
  move=> wfΣ wf.
  split; auto.
  apply weakening_wf_local; auto.
  clear wf.
  generalize 0 at 2 3.
  induction Δ at 2 3 4; intros n; rewrite ?lift_context_snoc0; simpl; auto.
  destruct a as [na [?|] ?]  => /=;
  rewrite /lift_decl /= /map_decl /=.
  specialize (IHc (S n)).
  eapply (context_subst_def _ _ _ _ (lift #|Δ| (#|c| + 0) t)) in IHc.
  rewrite Nat.add_1_r.
  rewrite all_rels_length.
  rewrite Nat.add_0_r in IHc |- *.
  apply IHc.
  rewrite reln_acc.
  constructor.
  specialize (IHc (S n)).
  now rewrite Nat.add_1_r.

  generalize (@eq_refl _ Δ).
  change Δ with ([] ++ Δ) at 1.
  change 0 with (length (@nil context_decl)) at 1.
  generalize (@nil context_decl).
  induction Δ at 1 4 7; rewrite /= => l eql.
  - constructor.
  - specialize (IHc (l ++ [a])).
    rewrite -app_assoc in IHc. specialize (IHc eql).
    destruct a as [na [?|] ?]  => /=;
    rewrite lift_context_snoc /lift_decl /map_decl /=.
    * rewrite app_length /= Nat.add_1_r in IHc. 
      rewrite all_rels_length Nat.add_0_r.
      constructor; auto.
      assert (Some (Some t) = option_map decl_body (nth_error Δ #|l|)).
      destruct (nth_error_spec Δ #|l|).
      rewrite -eql in e.
      rewrite nth_error_app_ge in e. lia.
      rewrite Nat.sub_diag in e. simpl in e. noconf e. simpl. reflexivity.
      rewrite -eql in l0. autorewrite with len in l0. simpl  in l0. lia.
      eapply (substitution _ _ _ _ [] _ _ _ IHc); auto.
      simpl.
      pose proof wf as wf'.
      rewrite -eql in wf'.
      rewrite app_context_assoc in wf'.
      apply wf_local_app_l in wf'. depelim wf'.
      eapply (weakening_typing); auto.
    * rewrite app_length /= Nat.add_1_r in IHc.
      constructor; auto.
    
      pose proof wf as wf'.
      rewrite -eql in wf'.
      rewrite app_context_assoc in wf'.
      apply wf_local_app_l in wf'. depelim wf'.
      rewrite Nat.add_0_r.

      eapply type_Cumul'.
      constructor. auto.
      rewrite -eql.
      rewrite nth_error_app_lt.
      rewrite app_length /=. lia.
      rewrite nth_error_app_ge //.
      rewrite Nat.sub_diag //.
      destruct l0.
      exists x.
      change (tSort x) with  
        (subst0 (all_rels c (S #|l|) #|Δ|) (lift #|Δ| #|c| (tSort x))).
      { eapply (substitution _ _ (lift_context #|Δ| 0 c) _ []); cbn; auto.
        change (tSort x) with (lift #|Δ| #|c| (tSort x)).
        eapply (weakening_typing); eauto. }
      eapply conv_cumul. simpl.
      rewrite -{1}eql. simpl.
      rewrite !app_context_assoc.
      rewrite /app_context !app_assoc.
      
      epose proof (all_rels_subst_lift Σ c Γ 
      (l ++ [{|decl_name := na; decl_body := None; decl_type := decl_type|}]) decl_type).
      assert (#|Δ| = #|c| + S #|l|).
      { rewrite -eql. autorewrite with len. simpl. lia. }
      rewrite H. rewrite app_length /= in X.
      rewrite Nat.add_1_r in X.
      unfold app_context in X.
      rewrite !app_tip_assoc /= in X.
      rewrite -app_assoc.
      apply X; auto.
Qed.

Lemma red_expand_let {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ.1} Γ na b ty t :
  wf_local Σ (Γ ,,, [vdef na b ty])  ->
  red Σ.1 (Γ ,,, [vdef na b ty]) t (lift0 1 (subst1 b 0 t)).
Proof.
  intros wfΓ.
  pose proof (all_rels_subst Σ [vdef na b ty] Γ t wfΣ wfΓ).
  simpl in X.
  rewrite subst_empty in X.
  now rewrite distr_lift_subst.
Qed.

Lemma type_it_mkProd_or_LetIn_inv {cf} {Σ : global_env_ext} {wfΣ : wf Σ}:
 forall {Γ Δ t s},
  Σ ;;; Γ |- it_mkProd_or_LetIn Δ t : tSort s ->
  ∑ Δs ts, sorts_local_ctx (lift_typing typing) Σ Γ Δ Δs ×
           Σ ;;; Γ ,,, Δ |- t : tSort ts ×
           leq_universe Σ (sort_of_products Δs ts) s.
Proof.
  intros Γ Δ t s h. revert Γ t s h.
  induction Δ; intros.
  - exists [], s; splits. apply h. apply leq_universe_refl.
  - destruct a as [na [b|] ty]; simpl in *;
    rewrite /mkProd_or_LetIn /= in h.
    * specialize (IHΔ _ _ _ h) as (Δs & ts & sorts & IHΔ & leq).
      exists Δs, ts.
      pose proof (PCUICWfUniverses.typing_wf_universe _ IHΔ) as wfts.
      eapply inversion_LetIn in IHΔ as [s' [? [? [? [? ?]]]]]; auto.
      splits; eauto.
      eapply type_Cumul'. eapply t2. now pcuic.
      eapply invert_cumul_letin_l in c; auto.
      eapply invert_cumul_sort_r in c as [u' [redu' cumu']].
      transitivity (tSort u'). 2:do 2 constructor; auto.
      eapply cumul_alt.
      exists (tSort u'), (tSort u'). repeat split; auto.
      2:now constructor.
      transitivity (lift0 1 (x {0 := b})).
      eapply (red_expand_let _ _ _ _). pcuic.
      change (tSort u') with (lift0 1 (tSort u')).
      eapply (weakening_red _ (Γ ,,, Δ) [] [_]); auto.

    * specialize (IHΔ _ _ _ h) as (Δs & ts & sorts & IHΔ & leq).
      eapply inversion_Prod in IHΔ as [? [? [? [? ]]]]; tea.
      exists (x :: Δs), x0. splits; tea.
      eapply cumul_Sort_inv in c.
      transitivity (sort_of_products Δs ts); auto using leq_universe_product.
      simpl. eapply leq_universe_sort_of_products_mon. 
      eapply Forall2_same. reflexivity.
      exact: c.
Qed.

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
    eapply type_Cumul'. eapply t2. now pcuic.
    eapply invert_cumul_letin_l in c; auto.
    eapply invert_cumul_sort_r in c as [u' [redu' cumu']].
    transitivity (tSort u'). 2:do 2 constructor; auto.
    eapply cumul_alt.
    exists (tSort u'), (tSort u'). repeat split; auto.
    2:now constructor.
    transitivity (lift0 1 (x {0 := b})).
    eapply (red_expand_let _ _ _ _). pcuic.
    change (tSort u') with (lift0 1 (tSort u')).
    eapply (weakening_red _ (Γ ,,, Δ) [] [_]); auto.

    specialize (IHΔ _ _ _ h).
    eapply inversion_Prod in IHΔ as [? [? [? [? ]]]].
    eapply type_Cumul; eauto. econstructor; pcuic.
    do 2 constructor.
    eapply cumul_Sort_inv in c.
    transitivity (Universe.sort_of_product x x0); auto using leq_universe_product.
    auto.
Qed.

Lemma isType_it_mkProd_or_LetIn_app {cf} {Σ : global_env_ext} {wfΣ : wf Σ} Γ Δ Δ' args T s : 
  Σ ;;; Γ |- it_mkProd_or_LetIn (Δ ,,, Δ') T : tSort s -> 
  subslet Σ Γ args (smash_context [] Δ) ->
  Σ ;;; Γ |- subst_let_expand args Δ (it_mkProd_or_LetIn Δ' T) : tSort s.
Proof.
  intros Hs sub.
  move: Hs. rewrite it_mkProd_or_LetIn_app.
  move/inversion_it_mkProd_or_LetIn => Hs.
  eapply typing_expand_lets in Hs.
  eapply (PCUICSubstitution.substitution _ _ _ _ []) in Hs; tea.
Qed.


Lemma lift_to_extended_list_k n Γ : map (lift n #|Γ|) (to_extended_list_k Γ 0) = 
  to_extended_list_k Γ 0.
Proof.
  rewrite /to_extended_list_k.
  change [] with (map (lift n #|Γ|) []) at 2.
  rewrite -(Nat.add_0_r #|Γ|).
  generalize 0.
  move:(@nil term).
  induction Γ; simpl; auto.
  intros l n'.
  destruct a as [? [?|] ?].
  specialize (IHΓ l (S n')).
  rewrite Nat.add_succ_r in IHΓ.
  now rewrite Nat.add_1_r IHΓ.
  specialize (IHΓ (tRel n' :: l) (S n')).
  rewrite Nat.add_succ_r in IHΓ.
  rewrite Nat.add_1_r IHΓ. simpl.
  destruct (leb_spec_Set (S (#|Γ| + n')) n'). lia.
  reflexivity.
Qed.
 
Lemma reln_subst acc s Γ k : 
  reln (map (subst s (k + #|Γ|)) acc) k (subst_context s 0 Γ) = 
  map (subst s (k + #|Γ|)) (reln acc k Γ).
Proof.
  induction Γ in acc, s, k |- *; simpl; auto.
  rewrite subst_context_snoc.
  simpl.
  destruct a as [? [?|] ?]; simpl in *.
  specialize (IHΓ acc s (S k)).
  rewrite Nat.add_succ_r !Nat.add_1_r -IHΓ.
  f_equal.
  specialize (IHΓ (tRel k :: acc) s (S k)).
  rewrite Nat.add_succ_r !Nat.add_1_r -IHΓ.
  f_equal.
  simpl.
  destruct (leb_spec_Set (S (k + #|Γ|)) k). lia.
  reflexivity.
Qed.

Lemma subst_context_telescope s k Γ : subst_context s k Γ = List.rev (subst_telescope s k (List.rev Γ)).
Proof.
  now rewrite subst_telescope_subst_context List.rev_involutive.
Qed.

Lemma ctx_inst_sub_to_extended_list_k {cf:checker_flags} Σ Γ args Δ : 
  forall inst : ctx_inst Σ Γ args Δ,
  map (subst0 (ctx_inst_sub inst)) (to_extended_list_k (List.rev Δ) 0) = args.
Proof.
  induction inst; simpl; rewrite /to_extended_list_k; auto.
  rewrite reln_app. simpl.
  have len := ctx_inst_subst_length inst0.
  rewrite subst_telescope_length in len.
  rewrite List.rev_length.
  f_equal.
  rewrite nth_error_app_ge. lia.
  assert(#|Δ| + 0 - 0 - #|ctx_inst_sub inst0| = 0) as -> by lia.
  cbn. apply lift0_id.
  rewrite -{2}IHinst.
  rewrite -map_subst_app_simpl.
  rewrite -map_map_compose. f_equal.
  simpl. unfold to_extended_list_k.
  epose proof (reln_subst [] [i] (List.rev Δ) 0). simpl in H.
  rewrite subst_context_telescope in H.
  rewrite List.rev_involutive in H. rewrite H.
  now rewrite List.rev_length len.

  rewrite reln_app. simpl.
  have len := ctx_inst_subst_length inst0.
  rewrite subst_telescope_length in len.
  rewrite -{2}IHinst.
  rewrite -map_subst_app_simpl.
  rewrite -map_map_compose. f_equal.
  simpl. unfold to_extended_list_k.
  epose proof (reln_subst [] [b] (List.rev Δ) 0). simpl in H.
  rewrite subst_context_telescope in H.
  rewrite List.rev_involutive in H. rewrite H.
  now rewrite List.rev_length len.
Qed.

Lemma spine_subst_subst_to_extended_list_k {cf:checker_flags} {Σ Γ args s Δ} : 
  spine_subst Σ Γ args s Δ ->
  map (subst0 s) (to_extended_list_k Δ 0) = args.
Proof.
  intros [_ _ sub _].
  rewrite /to_extended_list_k.
  rewrite -(map_lift0 args).
  generalize 0 at 1 2 3.
  induction sub; simpl; auto.
  intros n.
  rewrite reln_acc.
  rewrite !map_app.
  simpl. rewrite Nat.leb_refl Nat.sub_diag /=.
  simpl.
  f_equal. rewrite -IHsub.
  rewrite reln_lift.
  rewrite (reln_lift 1).
  rewrite -{4}(Nat.add_0_r n).
  rewrite (reln_lift n 0).
  rewrite !map_map_compose.
  apply map_ext.
  intros x. rewrite (subst_app_decomp [a] s).
  f_equal. simpl.
  rewrite -(commut_lift_subst_rec _ _ _ 0)  //.
  rewrite simpl_subst_k //.

  intros n.
  rewrite -IHsub.
  rewrite reln_lift.
  rewrite (reln_lift 1).
  rewrite -{4}(Nat.add_0_r n).
  rewrite (reln_lift n 0).
  rewrite !map_map_compose.
  apply map_ext.
  intros x. rewrite (subst_app_decomp [subst0 s b] s).
  f_equal. simpl.
  rewrite -(commut_lift_subst_rec _ _ _ 0)  //.
  rewrite simpl_subst_k //.
Qed.

Lemma spine_subst_subst_to_extended_list_k_gen {cf:checker_flags} {Σ Γ args s Δ Δ'} : 
  spine_subst Σ Γ args s Δ -> 
  to_extended_list_k Δ 0 = to_extended_list_k Δ' 0 ->
  map (subst0 s) (to_extended_list_k Δ' 0) = args.
Proof.
  intros sp <-; eapply spine_subst_subst_to_extended_list_k; eauto.
Qed.

Lemma arity_spine_eq {cf:checker_flags} Σ Γ T T' :
  isType Σ Γ T' ->
  T = T' -> arity_spine Σ Γ T [] T'.
Proof. intros H ->; constructor;auto. Qed.

(* Lemma arity_spine_letin_inv {cf:checker_flags} {Σ Γ na b B T args S} : 
  wf Σ.1 ->
  arity_spine Σ Γ (tLetIn na b B T) args S ->
  arity_spine Σ Γ (T {0 := b}) args S.
Proof.
  intros wfΣ Hsp.
  depelim Hsp.
  econstructor. auto.
  now eapply invert_cumul_letin_l in c.
  auto.
Qed. *)

Lemma typing_spine_inv {cf : checker_flags} {Σ : global_env × universes_decl}
  {Γ Δ : context} {T args args' T'} :
  wf Σ.1 ->
  #|args| = context_assumptions Δ ->
  wf_local Σ Γ ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T' ->
  ∑ args_sub,
     spine_subst Σ Γ args args_sub Δ *
     isType Σ Γ (subst0 args_sub T) * 
     typing_spine Σ Γ (subst0 args_sub T) args' T'.
Proof.
  intros wfΣ len wfΓ.
  revert args len T.
  induction Δ as [|d Δ] using ctx_length_rev_ind; intros args. simpl.
  destruct args; simpl; try discriminate.
  - intros _ T sp; exists []; split; [split|]; [constructor|..]; auto;
    now rewrite subst_empty.
  - rewrite context_assumptions_app => eq T wat sp.
    assert (wfΓΔ := isType_it_mkProd_or_LetIn_wf_local _ _ (Δ ++ [d]) _ _ wat).
    rewrite it_mkProd_or_LetIn_app in sp, wat.
    destruct d as [? [b|] ?]; simpl in *.
    + rewrite Nat.add_0_r in eq.
      eapply typing_spine_letin_inv in sp => //.
      rewrite /subst1 subst_it_mkProd_or_LetIn in sp.
      specialize (X (subst_context [b] 0 Δ) ltac:(now autorewrite with len)).
      specialize (X args ltac:(now rewrite context_assumptions_subst)).
      rewrite Nat.add_0_r in sp.
      eapply isType_tLetIn_red in wat as wat' => //.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in wat'; auto.
      destruct (X _ wat' sp) as [args_sub [[sps wat''] sp']].
      clear wat'.
      exists (args_sub ++ [b]); split; [split;[constructor|]|]; auto.
      * eapply context_subst_app_inv.
        simpl. rewrite skipn_0.
        move: (context_subst_length sps).
        autorewrite with len.
        move=> eq'. rewrite eq'.
        rewrite skipn_all_app (firstn_app_left _ 0) //.
        rewrite firstn_0 // app_nil_r.
        split; auto. apply sps. rewrite -{2}(subst_empty 0 b).
        constructor. constructor.
      * eapply subslet_app => //. eapply sps.
        rewrite -{1}(subst_empty 0 b).
        repeat constructor. rewrite !subst_empty.
        eapply All_local_env_app_inv in wfΓΔ as [_ wf].
        eapply All_local_env_app_inv in wf as [wfd _].
        depelim wfd. apply l0.
      * rewrite subst_app_simpl.
        move: (context_subst_length sps).
        now  autorewrite with len => <-.
      * rewrite subst_app_simpl.
        move: (context_subst_length sps).
        now  autorewrite with len => <-.

    + rewrite /mkProd_or_LetIn /= in sp, wat.
      destruct args as [|a args]; simpl in eq; try lia.
      specialize (X (subst_context [a] 0 Δ) ltac:(now autorewrite with len)).
      specialize (X args ltac:(now rewrite context_assumptions_subst)).
      eapply isType_tProd in wat as wat' => //.
      destruct wat' as [wat' wat''] => //.
      specialize (X (subst [a] #|Δ| T)).
      depelim sp.
      eapply cumul_Prod_inv in c as [conv cum]; auto.
      eapply (substitution_cumul0 _ _ _ _ _ _ a) in cum; auto.
      eapply typing_spine_strengthen in sp; eauto.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp; auto.
      eapply type_Cumul' in t.
      2:{ eauto. }
      forward X. {
        pose proof wfΓΔ as wfΓΔ'.
        rewrite app_context_assoc in wfΓΔ'. eapply All_local_env_app_inv in wfΓΔ' as [wfΓΔ' _].
        eapply (isType_subst wfΣ wfΓΔ') in wat''; eauto.
        2:{ repeat constructor. now rewrite subst_empty. }
        now rewrite subst_it_mkProd_or_LetIn Nat.add_0_r in wat''. }
      specialize (X sp).
      destruct X as [args_sub [[sps wat'''] sp']].
      exists (args_sub ++ [a]); split; [split;[constructor|]|]; auto.
      * eapply context_subst_app_inv.
        simpl. rewrite skipn_S skipn_0.
        move: (context_subst_length sps).
        autorewrite with len.
        move=> eq'. rewrite eq'.
        rewrite skipn_all_app (firstn_app_left _ 0) //.
        rewrite firstn_0 // app_nil_r.
        split; auto. apply sps.
        eapply (context_subst_ass _ []). constructor.
      * eapply subslet_app => //. eapply sps.
        rewrite -{1}(subst_empty 0 a).
        repeat constructor. now rewrite !subst_empty.
      * rewrite subst_app_simpl.
        move: (context_subst_length sps).
        now autorewrite with len => <-.
      * rewrite subst_app_simpl.
        move: (context_subst_length sps).
        now autorewrite with len => <-.
      * apply conv_cumul. now symmetry.
Qed.

Lemma typing_spine_app {cf:checker_flags} Σ Γ ty args na A B arg :
  wf Σ.1 ->
  typing_spine Σ Γ ty args (tProd na A B) ->
  Σ ;;; Γ |- arg : A ->
  typing_spine Σ Γ ty (args ++ [arg]) (B {0 := arg}).
Proof.
  intros wfΣ H; revert arg.
  dependent induction H.
  - intros arg Harg. simpl. econstructor; eauto.
    constructor. 2:reflexivity.
    eapply isType_tProd in i as [watd wat].
    eapply (isType_subst wfΣ (Δ:=[vass na A])); eauto.
    constructor; auto. now apply typing_wf_local in Harg.
    constructor. constructor. now rewrite subst_empty. auto.
    now apply typing_wf_local in Harg.
  - intros arg Harg.
    econstructor; eauto.
Qed.

Lemma typing_spine_nth_error {cf:checker_flags} {Σ Γ Δ T args n arg concl} : 
  wf Σ.1 ->
  isType Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args concl ->
  nth_error args n = Some arg ->
  (n < context_assumptions Δ) ->
  ∑ decl, (nth_error (smash_context [] Δ) (context_assumptions Δ - S n) = Some decl) * 
    (Σ ;;; Γ |- arg : subst0 (List.rev (firstn n args)) (decl_type decl)).
Proof.
  intros wfΣ. revert n args T.
  induction Δ using ctx_length_rev_ind => /= // n args T.
  - simpl. lia.
  - rewrite it_mkProd_or_LetIn_app context_assumptions_app.
    destruct d as [na [b|] ty]; simpl.
    + move=> wat. rewrite /= Nat.add_0_r. simpl.
      move=>  sp.
      eapply typing_spine_letin_inv in sp => //.
      eapply isType_tLetIn_red in wat => //.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp, wat.
      specialize (X (subst_context [b] 0 Γ0) ltac:(autorewrite with len; lia) n args _ wat sp).
      rewrite context_assumptions_subst in X.
      move=> Hnth Hn. specialize (X Hnth Hn) as [decl [nthsmash Hty]].
      exists decl; split; auto.
      rewrite smash_context_app. simpl.
      now rewrite -(smash_context_subst []) /= subst_context_nil.
      now eapply isType_wf_local in wat.
    + simpl.
      move=> wat sp.
      depelim sp. rewrite nth_error_nil //.
      destruct n as [|n']; simpl.
      * move=> [=] eq; subst hd.
        move=> Hctx. exists {| decl_name := na; decl_body := None; decl_type := ty |}.
        rewrite smash_context_app. simpl.
        rewrite nth_error_app_ge; rewrite smash_context_length /=. lia.
        assert(context_assumptions Γ0 + 1 - 1 - context_assumptions Γ0 = 0) as -> by lia.
        split; auto. rewrite subst_empty.
        pose proof (isType_wf_local i).
        eapply cumul_Prod_inv in c as [conv cum]; auto.
        eapply type_Cumul'; eauto.
        eapply isType_tProd in wat as [dom codom]; auto.
        now apply conv_cumul, conv_sym.
      * move=> Hnth Hn'.
        pose proof  (isType_wf_local i).
        eapply isType_tProd in wat as [dom' codom']; auto.
        eapply cumul_Prod_inv in c as [conv cum]; auto.
        unshelve eapply (isType_subst wfΣ (Δ:=[vass na ty]) _ [hd]) in codom'.
        constructor; auto.
        2:{ repeat constructor. rewrite subst_empty.
            eapply type_Cumul'; eauto. now eapply conv_cumul, conv_sym. }
        specialize (X (subst_context [hd] 0 Γ0) ltac:(autorewrite with len; lia)).
        unshelve eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cum; auto.
        rewrite subst_it_mkProd_or_LetIn in codom'.
        specialize (X n' tl _ codom').
        forward X.
        rewrite -subst_it_mkProd_or_LetIn.
        eapply typing_spine_strengthen; eauto.
        rewrite /subst1 in cum.
        specialize (X Hnth).
        forward X by (rewrite context_assumptions_subst; lia).
        destruct X as [decl [Hnth' Hty]].
        rewrite (smash_context_subst []) nth_error_subst_context in Hnth'.
        rewrite smash_context_app. simpl.
        rewrite context_assumptions_subst in Hnth'.
        replace (context_assumptions Γ0  + 1 - S (S n')) with
          (context_assumptions Γ0 - S n') by lia.
        rewrite nth_error_app_context_lt ?smash_context_length. lia.
        destruct (nth_error (smash_context [] Γ0) _) eqn:Heq; try discriminate.
        simpl in Hnth'. exists c; split; auto.
        noconf Hnth'. 
        rewrite /= smash_context_length /= in Hty.
        replace ((context_assumptions Γ0 - S (context_assumptions Γ0 - S n') + 0))
          with n' in Hty by lia.
        rewrite subst_app_simpl /= List.rev_length firstn_length_le.
        now eapply nth_error_Some_length in Hnth.
        assumption.
Qed.

From MetaCoq.PCUIC Require Import PCUICInst.

Local Open Scope sigma.

Lemma spine_subst_smash {cf:checker_flags} {Σ Γ inst s Δ} : 
  wf Σ.1 ->
  spine_subst Σ Γ inst s Δ ->
  spine_subst Σ Γ inst (List.rev inst) (smash_context [] Δ).
Proof.
  intros wfΣ [].
  assert (context_subst (smash_context [] Δ) inst (List.rev inst)).
  { apply closed_wf_local in spine_dom_wf0.
    clear -inst_ctx_subst0 spine_dom_wf0. induction inst_ctx_subst0.
    constructor. rewrite List.rev_app_distr /=.
    rewrite smash_context_acc. simpl.
    constructor. auto.
    simpl. rewrite smash_context_acc. simpl. auto.
    auto. }
  split; auto.
  - eapply All_local_env_app; split; auto.
    eapply wf_local_rel_smash_context; auto.
  - induction inst_subslet0 in inst, inst_ctx_subst0, spine_codom_wf0 |- *.
    depelim inst_ctx_subst0.
    + constructor.
    + depelim inst_ctx_subst0.
      simpl. rewrite smash_context_acc.
      simpl. rewrite List.rev_app_distr.
      depelim spine_codom_wf0.
      constructor. now apply IHinst_subslet0.
      eapply meta_conv. eauto.
      simpl.
      autorewrite with sigma.
      apply inst_ext. rewrite ren_lift_renaming.
      autorewrite with sigma.
      unfold Upn. rewrite subst_consn_compose.
      autorewrite with sigma.
      apply subst_consn_proper.
      2:{ rewrite -(subst_compose_assoc (↑^#|Δ|)).
          rewrite subst_consn_shiftn.
          2:now autorewrite with len.
          autorewrite with sigma.
          rewrite subst_consn_shiftn //.
          rewrite List.rev_length.
          now apply context_subst_length2 in inst_ctx_subst0. }
      clear -inst_ctx_subst0.
      rewrite subst_consn_compose.
      rewrite map_inst_idsn. now autorewrite with len.
      now apply context_subst_extended_subst.
    + simpl. rewrite smash_context_acc.
      simpl. depelim spine_codom_wf0.
      depelim inst_ctx_subst0; apply IHinst_subslet0; auto.
Qed.


Lemma subst_rel0_lift_id n t : subst [tRel 0] n (lift 1 (S n) t) = t.
Proof.
  sigma. rewrite -{2}(subst_ids t).
  apply inst_ext.
  unfold Upn. sigma. unfold shiftk at 1 => /=.
  rewrite Nat.add_0_r.
  assert(idsn n ⋅n (tRel n ⋅ ↑^n) =1 idsn (S n) ⋅n ↑^n).
  { pose proof (@subst_consn_app _ (idsn n) [(tRel 0).[↑^n]] (↑^n)).
    simpl in H. rewrite -> (subst_consn_subst_cons (tRel 0).[↑^n] []) in H.
    simpl in H. rewrite -> subst_consn_nil in H.
    unfold shiftk at 3 in H. rewrite Nat.add_0_r in H.
    rewrite -H. unfold shiftk at 1; now rewrite Nat.add_0_r. }
  rewrite H. rewrite ren_shiftk. rewrite subst_consn_ids_ren.
  unfold lift_renaming. rewrite compose_ren.
  intros i. unfold ren, ids; simpl. f_equal.
  elim: Nat.leb_spec => H'. unfold subst_consn.
  elim: nth_error_spec => [i' e l|].
  rewrite app_length ren_ids_length /= in l. lia.
  rewrite app_length ren_ids_length /=. lia.
  unfold subst_consn.
  elim: nth_error_spec => [i' e l|].
  rewrite (@ren_ids_lt (S n) i) in e. lia. congruence.
  rewrite app_length ren_ids_length /=. lia.
Qed.

Lemma subst_context_lift_id Γ : subst_context [tRel 0] 0 (lift_context 1 1 Γ) = Γ.
Proof.
  rewrite subst_context_alt lift_context_alt.
  rewrite mapi_compose.
  replace Γ with (mapi (fun k x => x) Γ) at 2.
  2:unfold mapi; generalize 0; induction Γ; simpl; intros; auto; congruence.
  apply mapi_ext.
  autorewrite with len.
  intros n [? [?|] ?]; unfold lift_decl, subst_decl, map_decl; simpl.
  generalize (Nat.pred #|Γ| - n).
  intros.
  now rewrite !Nat.add_0_r !Nat.add_1_r !subst_rel0_lift_id.
  now rewrite !Nat.add_0_r !Nat.add_1_r !subst_rel0_lift_id.
Qed.

Lemma subst_extended_subst s Γ : extended_subst (subst_context s 0 Γ) 0 = 
  map (subst s (context_assumptions Γ)) (extended_subst Γ 0).
Proof.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto; rewrite subst_context_snoc /=;
    autorewrite with len; rewrite ? (lift_extended_subst _ 1); f_equal; auto.
  - rewrite IHΓ.
    rewrite commut_lift_subst_rec. auto.
    rewrite distr_subst. now autorewrite with len.
  - rewrite IHΓ. 
    rewrite !map_map_compose. apply map_ext.
    intros x. 
    erewrite (commut_lift_subst_rec). lia_f_equal.
    lia.
Qed.

Lemma map_subst_extended_subst_lift_to_extended_list_k Γ :
 map (subst0 (extended_subst Γ 0)) (map (lift (context_assumptions Γ) #|Γ|)
  (to_extended_list Γ)) = to_extended_list (smash_context [] Γ).
Proof.
  induction Γ as [|[na [b|] ty] ?]; cbn; auto.
  rewrite (reln_lift 1).
  rewrite -[reln [] 0 (smash_context [] Γ)]IHΓ.
  rewrite !map_map_compose. apply map_ext => x.
  rewrite -Nat.add_1_r -(permute_lift _ _ _ 1). lia.
  rewrite (subst_app_decomp [_]).
  rewrite simpl_subst_k /= //.
  rewrite reln_acc (reln_lift 1) map_app /=.
  rewrite smash_context_acc /= (reln_acc [tRel 0]) (reln_lift 1) map_app /=.
  f_equal.
  rewrite -[reln [] 0 (smash_context [] Γ)]IHΓ.
  rewrite !map_map_compose. apply map_ext => x.
  rewrite -(Nat.add_1_r #|Γ|) -(permute_lift _ _ _ 1). lia.
  rewrite (subst_app_decomp [_]).
  rewrite simpl_subst_k /= //.
  rewrite lift_extended_subst.
  rewrite distr_lift_subst. f_equal.
  autorewrite with len. rewrite simpl_lift; lia_f_equal.
Qed.

Lemma arity_spine_it_mkProd_or_LetIn_smash {cf:checker_flags} Σ Γ Δ T args args' T' : 
  wf Σ.1 ->
  subslet Σ Γ (List.rev args) (smash_context [] Δ) ->
  arity_spine Σ Γ (subst_let_expand (List.rev args) Δ T) args' T' -> 
  arity_spine Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T'.
Proof.
  intros wfΣ subsl asp.
  rewrite /subst_let_expand /expand_lets /expand_lets_k in asp.
  move: Δ T args subsl asp.
  induction Δ using ctx_length_rev_ind => T args subsl asp.
  - simpl in subsl. simpl in asp. rewrite subst_empty lift0_id in asp. depelim subsl.
    rewrite /= H !subst_empty in asp. destruct args => //.
    simpl in H. apply (f_equal (@List.length _)) in H. simpl in H.
    rewrite app_length /= in H. lia.
  - rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
    destruct d as [na [b|] ty]; simpl in *.
    * constructor. rewrite /subst1 subst_it_mkProd_or_LetIn.
      rewrite Nat.add_0_r.
      rewrite smash_context_app smash_context_acc /= in subsl.
      rewrite  lift0_id /= subst_context_nil app_nil_r 
        lift0_context in subsl.
      rewrite -(smash_context_subst []) /= subst_context_nil in subsl.
      rewrite subst_empty in subsl.
      apply (X (subst_context [b] 0 Γ0) ltac:(now autorewrite with len)
        (subst [b] #|Γ0| T) _ subsl).
      rewrite extended_subst_app /= in asp.
      rewrite !subst_empty lift0_id lift0_context in asp.
      erewrite subst_app_simpl' in asp.
      2:now autorewrite with len.
      simpl in asp. autorewrite with len in asp.
      simpl in asp.
      autorewrite with len.
      now rewrite -{1}(Nat.add_0_r #|Γ0|) distr_lift_subst_rec /= Nat.add_0_r.
    * simpl in *. autorewrite with len in asp. 
      simpl in asp.
      assert (len:=subslet_length subsl).
      autorewrite with len in len. simpl in len.
      rewrite Nat.add_1_r in len.
      rewrite smash_context_app smash_context_acc /= in subsl.
      rewrite subst_context_lift_id in subsl.
      eapply subslet_app_inv in subsl as [subsl subsr].
      destruct args; simpl in * => //. 
      noconf len.
      autorewrite with len in subsl, subsr. simpl in *.
      rewrite -H in subsl subsr. rewrite skipn_all_app_eq ?List.rev_length in subsl subsr => //.
      rewrite (firstn_app_left _ 0) ?firstn_0 ?app_nil_r ?List.rev_length in subsr => //.
      depelim subsl.
      constructor. now rewrite subst_empty in t1.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r.
      rewrite -(smash_context_subst []) /= in subsr.
      apply (X (subst_context [t] 0 Γ0) ltac:(now autorewrite with len)
        (subst [t] #|Γ0| T) _ subsr).
      rewrite extended_subst_app /= in asp.
      rewrite subst_context_lift_id in asp.
      erewrite subst_app_simpl' in asp.
      2:now autorewrite with len.
      simpl in asp.
      autorewrite with len.
      rewrite -{1}(Nat.add_0_r #|Γ0|) distr_lift_subst_rec /= Nat.add_0_r.
      move: asp. rewrite subst_app_simpl /=; autorewrite with len.
      rewrite distr_subst. autorewrite with len.
      rewrite (distr_subst_rec _ _ [t]).
      cbn [map]. rewrite -H. erewrite (subst_rel_eq _ _ 0) =>//.
      simpl; autorewrite with len.
      rewrite (Nat.add_1_r #|args|).
      erewrite <-(simpl_lift T #|args| _ 1 (#|Γ0| + 1 + #|args|)).
      all:try lia.
      rewrite (simpl_subst_k) //.
      now rewrite subst_extended_subst H.
Qed.

(** This shows that we can promote an argument spine for a given context to 
    a spine for a context whose types are higher in the cumulativity relation.
*)

Lemma subslet_cumul {cf:checker_flags} Σ Δ args Γ Γ' : 
  wf Σ.1 ->
  assumption_context Γ -> assumption_context Γ' -> 
  wf_local Σ (Δ ,,, Γ) ->
  wf_local Σ (Δ ,,, Γ') ->
  cumul_ctx_rel Σ Δ Γ Γ' ->
  subslet Σ Δ args Γ -> subslet Σ Δ args Γ'.
Proof.
  intros wfΣ ass ass' wf wf' a2. induction a2 in wf, wf', args, ass, ass' |- *.
  - inversion 1; constructor.
  - intros subsl; depelim subsl.
    specialize (IHa2 s).
    forward IHa2 by now depelim ass.
    forward IHa2 by now depelim ass'.
    depelim wf.
    depelim wf'.
    specialize (IHa2 wf wf' subsl).
    constructor; auto.
    eapply type_Cumul'; eauto.
    eapply isType_subst; eauto.
    eapply (substitution_cumul _ _ _ []). eauto.
    eapply wf. assumption.
    now depelim p.
    elimtype False; depelim ass'.
    elimtype False; inv ass.
Qed.

Lemma spine_subst_cumul {cf:checker_flags} Σ Δ args Γ Γ' : 
  wf Σ.1 ->
  assumption_context Γ -> assumption_context Γ' -> 
  wf_local Σ (Δ ,,, Γ) ->
  wf_local Σ (Δ ,,, Γ') ->
  cumul_ctx_rel Σ Δ Γ Γ' ->
  spine_subst Σ Δ args (List.rev args) Γ -> 
  spine_subst Σ Δ args (List.rev args) Γ'.
Proof.
  intros wfΣ ass ass' wf wf' a2.
  intros []; split; auto.
  - clear -a2 ass ass' inst_ctx_subst0.
    revert inst_ctx_subst0; generalize (List.rev args).
    intros l ctxs. 
    induction ctxs in ass, Γ', ass', a2 |- *; depelim a2; try (simpl in H; noconf H); try constructor; auto.
    * depelim c. constructor. eapply IHctxs. now depelim ass.
      now depelim ass'. auto.
    * elimtype False; depelim ass.
  - eapply subslet_cumul. 6:eauto. all:eauto.
Qed.

Lemma pre_type_mkApps_arity {cf} {Σ : global_env_ext} {wfΣ : wf Σ} (Γ : context) 
  (t : term) (u : list term) tty T :
  Σ;;; Γ |- t : tty -> isType Σ Γ tty ->
  arity_spine Σ Γ tty u T -> 
  Σ;;; Γ |- mkApps t u : T.
Proof.
  intros Ht Hty Har.
  eapply type_mkApps; tea.
  eapply wf_arity_spine_typing_spine; tea.
  constructor; tas.
Qed.
