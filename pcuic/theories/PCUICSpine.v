(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia
     Classes.CRelationClasses ProofIrrelevance ssreflect.
From MetaCoq.Template Require Import config Universes monad_utils utils BasicAst
     AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICUnivSubstitution
     PCUICCumulativity PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICConversion PCUICContextConversion PCUICValidity
     PCUICParallelReductionConfluence PCUICWeakeningEnv
     PCUICClosed PCUICPrincipality PCUICSubstitution
     PCUICWeakening PCUICGeneration PCUICUtils PCUICCtxShape PCUICContexts
     PCUICUniverses PCUICArities.
From Equations Require Import Equations.

Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation_Properties.

Derive Signature for typing_spine.
  
Notation ctx_inst Σ Γ i Δ := (ctx_inst (lift_typing typing) Σ Γ i Δ).

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
  * depelim sub'; simpl in H; noconf H.
    simpl in t0, Hlen.
    rewrite -subst_app_simpl' /=. lia.
    constructor. eauto.
    now rewrite - !subst_app_simpl' in t0; try lia.
  * rewrite /subst_decl /map_decl /snoc /= in sub'.
    depelim sub'; simpl in H; noconf H. simpl in Hlen.
    rewrite - !subst_app_simpl' in t0; try lia.
    simpl; constructor; eauto.
Qed.

Lemma context_subst_app_inv {ctx ctx' : list PCUICAst.context_decl} {args s : list term} :
  context_subst (subst_context (skipn #|ctx| s) 0 ctx)
    (skipn (PCUICAst.context_assumptions ctx') args) 
    (firstn #|ctx| s)
  × context_subst ctx' (firstn (PCUICAst.context_assumptions ctx') args)	(skipn #|ctx| s) ->
  context_subst (ctx ++ ctx') args s.
Proof.
  move=> [Hl Hr].
  rewrite -(firstn_skipn (context_assumptions ctx') args).
  assert (lenctx' : context_assumptions ctx' + context_assumptions ctx = #|args|).
  { assert (lenctx'' : context_assumptions ctx' <= #|args|).
    move: (context_subst_assumptions_length _ _ _ Hr).
    rewrite firstn_length; lia.
    move: (context_subst_assumptions_length _ _ _ Hr).
    move: (context_subst_assumptions_length _ _ _ Hl).
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
    * destruct a as [na' [b'|] ty']; simpl in *; simpl in H; noconf H. simpl in H.
      rewrite skipn_S in Hl, Hr, H. rewrite -H.
      pose proof (context_subst_length _ _ _ Hl). rewrite subst_context_length in H0.
      rewrite {3}H0 -subst_app_simpl [firstn #|ctx| _ ++ _]firstn_skipn. constructor.
      apply IHctx => //.
Qed.


Lemma ctx_inst_inst {cf:checker_flags} Σ ext u Γ i Δ  :
  wf_global_ext Σ.1 ext ->
  ctx_inst (Σ.1, ext) Γ i Δ ->
  consistent_instance_ext Σ ext u ->
  ctx_inst Σ (subst_instance_context u Γ)
    (map (subst_instance_constr u) i)
    (subst_instance_context u Δ).
Proof.
  intros wfext ctxi cu.
  induction ctxi; simpl; constructor; auto.
  * red in p |- *.
    destruct Σ as [Σ univs].
    eapply (typing_subst_instance'' Σ); eauto. apply wfext.
    apply wfext.
  * rewrite (subst_telescope_subst_instance_constr u [i]).
    apply IHctxi.
  * rewrite (subst_telescope_subst_instance_constr u [b]).
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

Inductive arity_spine {cf : checker_flags} (Σ : PCUICAst.global_env_ext) (Γ : PCUICAst.context) : 
  term -> list term -> term -> Type :=
| arity_spine_nil ty ty' :
  isWfArity_or_Type Σ Γ ty' ->
  Σ ;;; Γ |- ty <= ty' ->
  arity_spine Σ Γ ty [] ty'
| arity_spine_def : forall (tl : list term) 
                      (na : name) (A a B B' : term),                      
                    arity_spine Σ Γ (B {0 := a}) tl B' ->
                    arity_spine Σ Γ (tLetIn na a A B) tl B'
| arity_spine_ass : forall (hd : term) (tl : list term) 
                      (na : name) (A B B' : term),
                    Σ;;; Γ |- hd : A ->
                    arity_spine Σ Γ (B {0 := hd}) tl B' ->
                    arity_spine Σ Γ (tProd na A B) (hd :: tl) B'.

Record wf_arity_spine {cf:checker_flags} Σ Γ T args T' :=
{ wf_arity_spine_wf : isWfArity_or_Type Σ Γ T;
  wf_arity_spine_spine : arity_spine Σ Γ T args T' }.

Lemma wf_arity_spine_typing_spine {cf:checker_flags} Σ Γ T args T' :
  wf Σ.1 ->
  wf_arity_spine Σ Γ T args T' ->
  typing_spine Σ Γ T args T'.
Proof.
  intros wfΣ [wf sp].
  have wfΓ := isWAT_wf_local wf.
  induction sp; try constructor; auto.
  eapply isWAT_tLetIn_red in wf; auto.
  specialize (IHsp wf).
  eapply typing_spine_strengthen; eauto.
  apply red_cumul. apply red1_red. constructor.

  econstructor; eauto. reflexivity. apply IHsp.
  eapply isWAT_tProd in wf => //.
  destruct wf as [wfA wfB].
  unshelve eapply (@isWAT_subst _ _ wfΣ Γ [vass na A] _ _ [hd]) in wfB => //.
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
  assert (wf_local Σ Γ). now apply wf_local_app in wfΓ'. move X after wfΓ'.
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
      + rewrite PCUICCtxShape.context_assumptions_app /= Nat.add_0_r.
        eapply typing_spine_letin_inv in Hsp; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in Hsp.
        specialize (IHn (subst_context [b] 0 l)).
        forward IHn. {
          rewrite app_context_assoc in wfΓ'.
          apply All_local_env_app in wfΓ' as [wfb wfa].
          depelim wfb. simpl in H; noconf H. simpl in H. noconf H.
          eapply substitution_wf_local. eauto. 
          epose proof (cons_let_def Σ Γ [] [] na b ty ltac:(constructor)).
          rewrite !subst_empty in X. eapply X. auto.
          eapply All_local_env_app_inv; split.
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
          pose proof (context_subst_length _ _ _ cs). rewrite subst_context_length in H0.
          rewrite !(firstn_app_left _ 0). lia. simpl. rewrite !app_nil_r.
          split. now rewrite H0 skipn_all_app.
          rewrite H0 skipn_all_app. repeat constructor.
        * apply subslet_app. now rewrite subst_empty.
          repeat constructor.
          rewrite app_context_assoc in wfΓ'. simpl in wfΓ'.
          apply wf_local_app in wfΓ'. depelim wfΓ'; simpl in H; noconf H.
          now rewrite !subst_empty.
      + rewrite PCUICCtxShape.context_assumptions_app /=.
        depelim Hsp. 
        now eapply cumul_Prod_Sort_inv in c.
        eapply cumul_Prod_inv in c as [conva cumulB].
        eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cumulB; auto.
        rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
        specialize (IHn (subst_context [hd] 0 l)).
        forward IHn. {
          rewrite app_context_assoc in wfΓ'.
          apply All_local_env_app in wfΓ' as [wfb wfa]; eauto.
          depelim wfb. simpl in H; noconf H.
          eapply substitution_wf_local. auto. 
          constructor. constructor. rewrite subst_empty.
          eapply type_Cumul. eapply t.
          right; eapply l0.
          eapply conv_cumul; auto. now symmetry. 
          eapply All_local_env_app_inv; eauto; split.
          constructor; eauto. eapply isWAT_tProd in i; intuition eauto.
          simpl in H; noconf H.
        }
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
          pose proof (context_subst_length _ _ _ cs). rewrite subst_context_length in H0.
          rewrite !(firstn_app_left _ 0). lia. simpl. rewrite !app_nil_r.
          split. now rewrite H0 skipn_all_app.
          rewrite H0 skipn_all_app. apply (context_subst_ass _ []). constructor.
        * apply subslet_app => //.
          repeat constructor.
          rewrite app_context_assoc in wfΓ'. simpl in wfΓ'.
          apply wf_local_app in wfΓ'. depelim wfΓ'; simpl in H; noconf H.
          rewrite !subst_empty. red in l0.
          eapply type_Cumul; eauto. eapply conv_cumul. now symmetry.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_gen {cf:checker_flags} Σ Γ Δ Δ' T args s s' args' T' : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args s' = Some s -> 
  typing_spine Σ Γ (subst0 s T) args' T' ->
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s (Δ' ,,, Δ) ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ' (it_mkProd_or_LetIn Δ T)) ->
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
    simpl in Hargs. rewrite Nat.add_1_r in Hargs. noconf Hargs. simpl in H; noconf H.
    intros subs. rewrite app_context_assoc in subs.    
    specialize (IHn Δ _ T args s _ ltac:(lia) Hsub Hsp H subs).
    intros Har.
    forward IHn. now rewrite it_mkProd_or_LetIn_app.
    eapply subslet_app_inv in subs as [subsl subsr].
    depelim subsl; simpl in H1; noconf H1.
    have Hskip := make_context_subst_skipn Hsub. 
    rewrite List.rev_length in Hskip. rewrite Hskip in H0; noconf H0.
    simpl; eapply typing_spine_prod; auto; first
    now rewrite /subst1 -subst_app_simpl.
    eapply isWAT_it_mkProd_or_LetIn_app in Har; eauto.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Δ T args s args' T' : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args [] = Some s -> 
  typing_spine Σ Γ (subst0 s T) args' T' ->
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
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
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
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
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args (subst0 s T).
Proof.
  intros. 
  pose proof (typing_spine_it_mkProd_or_LetIn_gen Σ Γ Δ [] T args s [] []); auto.
  rewrite app_nil_r subst_empty in X2. apply X2; eauto.
  constructor. 2:eauto.
  eapply isWAT_it_mkProd_or_LetIn_app; eauto with pcuic. pcuic.
  now rewrite app_context_nil_l.
Qed.

Lemma typing_spine_it_mkProd_or_LetIn_close_eq {cf:checker_flags} Σ Γ Δ T args s T' : 
  wf Σ.1 ->
  make_context_subst (List.rev Δ) args [] = Some s -> 
  #|args| = context_assumptions Δ ->
  subslet Σ Γ s Δ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
  T' = (subst0 s T) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T'.
Proof.
  intros; subst; now apply typing_spine_it_mkProd_or_LetIn_close.
Qed. 

Lemma typing_spine_it_mkProd_or_LetIn_close' {cf:checker_flags} Σ Γ Δ T args s T' : 
  wf Σ.1 ->
  spine_subst Σ Γ args s Δ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Δ T) ->
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
  depelim Hsub; simpl in H; noconf H.
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
  context_relation (fun Δ Δ' => conv_decls Σ (Γ ,,, Δ) (Γ ,,, Δ')) Δ Δ' ->
  All2 (conv Σ Γ) inst inst' -> All2 (conv Σ Γ) insts insts'.
Proof.
move=> wfΣ [_ wf cs sl] [_ _ cs' sl'] cv.
move: inst insts cs wf sl inst' insts' cs' sl'.
induction cv; intros; depelim cs ; depelim cs';
  try (simpl in H; noconf H); try (simpl in H0; noconf H0).
- constructor; auto.    
- eapply All2_app_inv in X as [[l1 l2] [[? ?] ?]].
  depelim a2. depelim a2. apply app_inj_tail in e as [? ?]; subst.
  depelim sl; depelim sl'; simpl in H; noconf H; simpl in H0; noconf H0;
    try (simpl in H1; noconf H1).
  depelim wf; simpl in H; noconf H.
  specialize (IHcv _ _ cs wf sl _ _ cs' sl' a1).
  constructor; auto.
- depelim sl; depelim sl'; simpl in H; noconf H; simpl in H0; noconf H0;
    try (simpl in H1; noconf H1); try (simpl in H2; noconf H2).
  depelim wf; simpl in H; noconf H.
  specialize (IHcv _ _ cs wf sl _ _ cs' sl' X).
  constructor; auto.
  eapply (subst_conv _ _ _ []); eauto.
  depelim p; pcuic.
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
  now rewrite (context_subst_length _ _ _ cs) in X |- *.
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
  now eapply All_local_env_app in wfcodom as [? ?].
  eapply substitution_wf_local; eauto.
  now rewrite app_context_assoc in wfcodom.
Qed.

Lemma spine_subst_inst {cf:checker_flags} Σ ext u Γ i s Δ  :
  wf Σ.1 ->
  wf_global_ext Σ.1 ext ->
  spine_subst (Σ.1, ext) Γ i s Δ ->
  consistent_instance_ext Σ ext u ->
  spine_subst Σ (subst_instance_context u Γ)
    (map (subst_instance_constr u) i)
    (map (subst_instance_constr u) s)
    (subst_instance_context u Δ).
Proof.
  intros wfΣ wfext [wfdom wfcodom cs subsl] cu.
  split.
  eapply wf_local_subst_instance; eauto.
  rewrite -subst_instance_context_app.
  eapply wf_local_subst_instance; eauto.
  clear -cs cu wfext wfΣ.
  induction cs; simpl; rewrite ?map_app; try constructor; auto.
  simpl.
  rewrite -subst_subst_instance_constr.
  constructor; auto.

  clear -subsl cu wfΣ wfext.
  induction subsl; simpl; rewrite -?subst_subst_instance_constr; constructor; auto.
  * destruct Σ as [Σ univs].
    rewrite subst_subst_instance_constr.
    eapply (typing_subst_instance'' Σ); simpl; auto.
    apply wfext. simpl in wfext. apply t0. 
    apply wfext. auto.
  * rewrite !subst_subst_instance_constr. simpl.
    destruct Σ as [Σ univs].
    eapply (typing_subst_instance'' Σ); simpl; auto.
    apply wfext. simpl in wfext. apply t0. 
    apply wfext. auto.
Qed.

Lemma subslet_lift {cf:checker_flags} Σ (Γ Δ : context) s Δ' :
  wf Σ.1 -> wf_local Σ (Γ ,,, Δ) ->
  subslet Σ Γ s Δ' ->
  subslet Σ (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ').
Proof.
  move=> wfΣ wfl.
  induction 1; rewrite ?lift_context_snoc /=; try constructor; auto.
  simpl.
  rewrite -(subslet_length X).
  rewrite -distr_lift_subst. apply weakening; eauto.

  rewrite -(subslet_length X).
  rewrite distr_lift_subst. constructor; auto.
  rewrite - !distr_lift_subst. apply weakening; eauto.
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
