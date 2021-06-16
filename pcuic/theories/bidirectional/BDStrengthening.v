From Coq Require Import Bool List Arith Lia.
From Coq Require String.
From MetaCoq.Template Require Import config utils monad_utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICTyping PCUICSigmaCalculus PCUICRename PCUICOnFreeVars PCUICClosed PCUICConfluence PCUICSpine PCUICInductiveInversion PCUICParallelReductionConfluence.

From MetaCoq.PCUIC Require Import BDEnvironmentTyping BDTyping BDToPCUIC BDFromPCUIC.

Require Import ssreflect ssrbool.
Require Import Coq.Program.Equality.

Lemma on_free_vars_ctx_tip P d : on_free_vars_ctx P [d] = on_free_vars_decl P d.
Proof. cbn; rewrite andb_true_r // shiftnP0 //. Qed.

Lemma on_free_vars_it_mkLambda_or_LetIn {P Δ t} : 
  on_free_vars P (it_mkLambda_or_LetIn Δ t) = 
    on_free_vars_ctx P Δ && on_free_vars (shiftnP #|Δ| P) t.
Proof.
  move: P. induction Δ using rev_ind => P.
  - cbn. now rewrite shiftnP0.
  - destruct x as [na [b|] ty]; rewrite it_mkLambda_or_LetIn_app /= /mkLambda_or_LetIn /=.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /= 
      /on_free_vars_decl /test_decl /=. ring.
    rewrite on_free_vars_ctx_app /= IHΔ !lengths /= shiftnP_add on_free_vars_ctx_tip /= 
     /on_free_vars_decl /test_decl /=. ring.
Qed.

Lemma on_free_vars_case_predicate_context `{checker_flags} Σ ci mdecl idecl p P :
  wf Σ ->
  declared_inductive Σ ci mdecl idecl ->
  forallb (on_free_vars P) (pparams p) ->
  wf_predicate mdecl idecl p ->
  All2 (compare_decls eq eq) (pcontext p) (ind_predicate_context ci mdecl idecl) ->
  on_free_vars_ctx P (case_predicate_context ci mdecl idecl p).
Proof.
  intros.
  rewrite /case_predicate_context /case_predicate_context_gen /pre_case_predicate_context_gen /inst_case_context.
  erewrite <- on_free_vars_map2_cstr_args.
  2: rewrite fold_context_k_length !map_length ; eapply All2_length ; tea.
  apply on_free_vars_ctx_subst_context.
  2: by rewrite forallb_rev.
  rewrite on_free_vars_subst_instance_context List.rev_length.
  apply closedn_ctx_on_free_vars_shift.
  replace #|pparams p| with (context_assumptions (ind_params mdecl)).
  1: eapply closed_ind_predicate_context ; tea ; eapply declared_minductive_closed ; eauto.
  erewrite wf_predicate_length_pars ; tea.
  eapply PCUICDeclarationTyping.onNpars, PCUICWeakeningEnv.on_declared_minductive ; eauto.
Qed.

Section OnFreeVars.

  Context `{cf : checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ).

  Let Pinfer Γ t T :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    on_free_vars P T.

  Let Psort (Γ : context) (t : term) (u : Universe.t) := True.

  Let Pprod Γ t (na : aname) A B :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    on_free_vars P A × on_free_vars (shiftnP 1 P) B.

  Let Pind Γ (ind : inductive) t (u : Instance.t) args :=
    forall P,
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    All (on_free_vars P) args.

  Let Pcheck (Γ : context) (t : term) (T : term) := True.

  Let PΓ (Γ : context) :=
    True.

  Let PΓ_rel (Γ Γ' : context) := True.

  Theorem bidirectional_on_free_vars : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ PΓ_rel.
  Proof.
    apply bidir_ind_env.

    - constructor.

    - constructor.

    - intros. red.
      intros P HΓ Hn. 
      eapply alli_Alli, Alli_nth_error in HΓ ; tea.
      apply on_free_vars_lift0.
      by move: HΓ => /implyP /(_ Hn) /andP [].

    - easy.
    - easy.
    - intros until bty.
      move => _ _ _ Hbty ? ? /= /andP [] ? ?.
      apply /andP ; split ; tea.
      apply Hbty ; tea.
      rewrite on_ctx_free_vars_snoc.
      apply /andP ; split ; tea.

    - intros until A.
      move => _ _ _ _ _ Ht ? ? /= /andP [] ? /andP [] ? ?.
      repeat (apply /andP ; split ; tea).
      apply Ht ; tea.
      rewrite on_ctx_free_vars_snoc.
      repeat (apply /andP ; split ; tea).

    - intros until u.
      move => _ HAB _ _ ? ? /= /andP [] ? ?.
      edestruct HAB ; tea.
      apply on_free_vars_subst1 ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      rewrite closedn_subst_instance.
      eapply declared_constant_closed_type ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      rewrite closedn_subst_instance.
      eapply declared_inductive_closed_type ; tea.

    - intros.
      intros ? ? ?.
      eapply closed_on_free_vars.
      eapply declared_constructor_closed_type ; tea.

    - intros.
      move => ? ? /= /and5P [] ? ? Hctx ? ?.
      rewrite on_free_vars_mkApps.
      apply /andP ; split.
      + rewrite on_free_vars_it_mkLambda_or_LetIn.
        rewrite test_context_k_closed_on_free_vars_ctx -closedn_ctx_on_free_vars in Hctx.
        apply /andP ; split.
        2: by rewrite case_predicate_context_length.
        eapply on_free_vars_case_predicate_context ; eassumption.
        
      + rewrite forallb_app.
        apply /andP ; split.
        2: by rewrite /= andb_true_r.
        apply All_forallb, All_skipn.
        auto.
    
    - intros until args.
      move => ? _ ? largs ? ? ? ?.
      apply on_free_vars_subst.
      + cbn ; apply /andP ; split ; auto.
        rewrite forallb_rev.
        apply All_forallb.
        auto.
      + eapply closedn_on_free_vars.
        rewrite closedn_subst_instance /= List.rev_length largs.
        eapply declared_projection_closed_type ; tea. 

    - intros until decl.
      move => ? ndec ? ? ? ? ? /= Hmfix.
      eapply forallb_nth_error in Hmfix.
      erewrite ndec in Hmfix.
      cbn in Hmfix.
      by move: Hmfix => /andP [].

    - intros until decl.
      move => ? ndec ? ? ? ? ? /= Hmfix.
      eapply forallb_nth_error in Hmfix.
      erewrite ndec in Hmfix.
      cbn in Hmfix.
      by move: Hmfix => /andP [].
    
    - easy.

    - intros ? ? ? ? ? ? _ HT Hred.
      intros ? HΓ Ht.
      specialize (HT _ HΓ Ht).
      eapply red_on_free_vars in Hred ; tea.
      by move: Hred => /= /andP [].
    - intros ? ? ? ? ? ? _ HT Hred.

      intros ? HΓ Ht.
      specialize (HT _ HΓ Ht).
      eapply red_on_free_vars in Hred ; tea.
      rewrite on_free_vars_mkApps in Hred.
      by move: Hred => /= /forallb_All.

    - easy.

  Qed.

  Lemma infering_on_free_vars P Γ t T :
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    Σ ;;; Γ |- t ▹ T ->
    on_free_vars P T.
  Proof.
    intros.
    edestruct bidirectional_on_free_vars as (_&_&_&p&_).
    eapply p ; eauto.
  Qed.

  Lemma infering_prod_on_free_vars P Γ t na A B :
    on_ctx_free_vars P Γ ->
    on_free_vars P t ->
    Σ ;;; Γ |- t ▹Π (na,A,B) ->
    on_free_vars P A × on_free_vars (shiftnP 1 P) B.
  Proof.
    intros.
    eapply bidirectional_on_free_vars ; eauto.
  Qed.

End OnFreeVars.

Lemma on_free_vars_type `{checker_flags} P Σ (wfΣ : wf Σ.1) Γ t T :
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Γ |- t : T ->
  ∑ T', on_free_vars P T' × Σ ;;; Γ |- t : T'.
Proof.
  intros oΓ ot ty.
  assert (wf_local Σ Γ) by (eapply typing_wf_local ; tea). 
  apply typing_infering in ty as [T' []] ; tea.
  exists T' ; split.
  - edestruct bidirectional_on_free_vars as (_&_&_&?&_).
    all: eauto.
  - by apply infering_typing.
Qed.

Definition unlift_renaming n k i := if i <? k then i else if i <? k + n then 0 else i - n.
Definition unlift n k := rename (unlift_renaming n k).

Lemma lift_unlift n k : (unlift_renaming n k) ∘ (lift_renaming n k) =1 ren_id .
Proof.
  intros i.
  rewrite /unlift_renaming /lift_renaming /ren_id.
  repeat match goal with
    | |- context [?x <? ?y] => destruct (Nat.ltb_spec0 x y) ; cbn
    | |- context [?x <=? ?y] => destruct (Nat.leb_spec0 x y) ; cbn
    | _ : context [?x <=? ?y] |- _ => destruct (Nat.leb_spec0 x y) ; cbn in *
  end.
  all: try congruence ; try lia.
Qed.

Corollary lift_unlift_term {n k} t : unlift n k (lift n k t) = t.
Proof.
  by rewrite lift_rename /unlift rename_compose lift_unlift rename_ren_id.
Qed.

(* Lemma shift_cond (P : nat -> bool) f f' :
  (forall i, P i -> f i = f' i) ->
  forall i n,
  shiftnP n P i -> shiftn n f i = shiftn n f' i.
Proof.
  rewrite /shiftn /shiftnP.
  intros H i n ?.
  destruct (i <? n) ; cbn in * ; auto.
  by rewrite H.
Qed.

Lemma cond_rename_ext (P : nat -> bool) f f' t:
  (forall i, P i -> f i = f' i) ->
  on_free_vars P t ->
  rename f t = rename f' t.
Proof.
  intros H HP.
  induction t using term_forall_list_ind in f, f', P, H, HP |- * ;
  intros; cbn in |- *; try easy.
  all: try solve [f_equal ; try rewrite H ; easy].
  all: cbn in HP ;
    repeat match goal with
    | H : is_true (_ && _) |- _ => move: H => /andP [? ?]
    | H : is_true (forallb _ _) |- _ => move: H => /forallb_All ?
    end.
  all: f_equal ; eauto.
  - apply All_map_eq.
    eapply All_mix in X ; tea.
    eapply All_impl ; tea.
    intros ? [] ; easy.
  - eapply IHt2 ; eauto.
    intros.
    eapply shift_cond ; eauto.
  - eapply IHt2 ; eauto.
    intros.
    eapply shift_cond ; eauto.
  - eapply IHt3 ; eauto.
    intros.
    eapply shift_cond ; eauto.
  - rewrite /rename_predicate.
    destruct X as (IHpar&?&IHret).
    f_equal.
    + apply All_map_eq.
      eapply All_mix in IHpar ; tea.
      eapply All_impl ; tea.
      intros ? [] ; easy.
    + eapply IHret ; tea.
      intros.
      eapply shift_cond ; eauto.
  - apply All_map_eq.
    eapply All_mix in X0 ; tea.
    eapply All_impl ; tea.
    intros ? [i [? e]].
    move: i => /andP [? ?].
    rewrite /map_branch_shift.
    f_equal.
    eapply e ; tea.
    intros.
    eapply shift_cond ; eauto.
  - apply All_map_eq.
    eapply All_mix in X ; tea.
    eapply All_impl ; tea.
    intros ? [i [e e']].
    move: i => /andP [? ?].
    rewrite /map_def.
    f_equal.
    + eapply e ; eauto.
    + eapply e' ; eauto.
      intros. eapply shift_cond ; eauto.
  - apply All_map_eq.
    eapply All_mix in X ; tea.
    eapply All_impl ; tea.
    intros ? [i [e e']].
    move: i => /andP [? ?].
    rewrite /map_def.
    f_equal.
    + eapply e ; eauto.
    + eapply e' ; eauto.
      intros. eapply shift_cond ; eauto.
Qed. *)

Lemma urenaming_strengthen P Γ Δ decl :
  urenaming (strengthenP #|Δ| 1 P) (Γ,,,Δ) (Γ ,, decl ,,, lift_context 1 0 Δ) (unlift_renaming 1 #|Δ|).
Proof.
  rewrite <- PCUICWeakening.rename_context_lift_context.
  intros i decl' pi nthi.
  rewrite /strengthenP in pi.
  destruct (Nat.ltb_spec0 i #|Δ|) as [iΔ|iΔ].
  - rewrite nth_error_app_context_lt in nthi.
    1: by rewrite fold_context_k_length.
    rewrite nth_error_rename_context in nthi.
    apply option_map_Some in nthi as [decl'' []].
    subst.
    eexists ; split ; [idtac|split ; [idtac|split]].
    + rewrite /unlift_renaming.
      move: (iΔ) => /Nat.ltb_spec0 ->.
      rewrite nth_error_app_context_lt //.
      eassumption.
    + reflexivity.
    + rewrite /= rename_compose.
      apply rename_proper ; auto.
      intros x.
      rewrite /rshiftk /shiftn /unlift_renaming /lift_renaming.
      repeat match goal with
        | |- context [?x <? ?y] => destruct (Nat.ltb_spec0 x y) ; cbn in *
        | |- context [?x <=? ?y] => destruct (Nat.leb_spec0 x y) ; cbn in *
        | _ : context [?x <? ?y] |- _ => destruct (Nat.ltb_spec0 x y) ; cbn in *
        | _ : context [?x <=? ?y] |- _ => destruct (Nat.leb_spec0 x y) ; cbn in *
      end.
      all: try congruence ; try lia.
    + cbn ; destruct (decl_body decl'') ; rewrite //=.
      f_equal.
      rewrite rename_compose.
      apply rename_proper ; auto.
      intros x.
      rewrite /unlift_renaming /shiftn /lift_renaming.
      repeat match goal with
        | |- context [?x <? ?y] => destruct (Nat.ltb_spec0 x y) ; cbn in *
        | |- context [?x <=? ?y] => destruct (Nat.leb_spec0 x y) ; cbn in *
        | _ : context [?x <? ?y] |- _ => destruct (Nat.ltb_spec0 x y) ; cbn in *
        | _ : context [?x <=? ?y] |- _ => destruct (Nat.leb_spec0 x y) ; cbn in *
      end.
      all: try congruence ; try lia.
  - change (Γ ,, decl) with (Γ ,,, [decl]) in nthi.
    rewrite -app_context_assoc /= in nthi.
    destruct (Nat.ltb_spec0 i (#|Δ| + 1)) as [iΔ'|iΔ'] ; cbn in * ; [congruence|..].
    apply Nat.nlt_ge in iΔ'.
    rewrite nth_error_app_context_ge app_length /= rename_context_length // in nthi.
    eexists ; repeat split.
    + rewrite /unlift_renaming.
      destruct (Nat.ltb_spec0 i #|Δ|) ; [lia|..].
      destruct (Nat.ltb_spec0 i (#|Δ| + 1)) ; [lia|..].
      rewrite nth_error_app_context_ge ; [lia|..].
      rewrite -nthi.
      f_equal.
      lia.
    + apply rename_proper ; auto.
      intros x.
      rewrite /unlift_renaming. 
      repeat match goal with
        | |- context [?x <? ?y] => destruct (Nat.ltb_spec0 x y) ; cbn in *
        | |- context [?x <=? ?y] => destruct (Nat.leb_spec0 x y) ; cbn in *
        | _ : context [?x <? ?y] |- _ => destruct (Nat.ltb_spec0 x y) ; cbn in *
        | _ : context [?x <=? ?y] |- _ => destruct (Nat.leb_spec0 x y) ; cbn in *
      end.
      all: try congruence ; try lia.
    + destruct (decl_body decl') ; rewrite //=.
      f_equal.
      apply rename_proper ; auto.
      intros x.
      rewrite /unlift_renaming.
      repeat match goal with
        | |- context [?x <? ?y] => destruct (Nat.ltb_spec0 x y) ; cbn in *
        | |- context [?x <=? ?y] => destruct (Nat.leb_spec0 x y) ; cbn in *
        | _ : context [?x <? ?y] |- _ => destruct (Nat.ltb_spec0 x y) ; cbn in *
        | _ : context [?x <=? ?y] |- _ => destruct (Nat.leb_spec0 x y) ; cbn in *
      end.
      all: try congruence ; try lia.
Qed.

Axiom fix_guard_rename : forall P Σ Γ Δ mfix f,
  urenaming P Γ Δ f ->
  let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
  fix_guard Σ Δ mfix ->
  fix_guard Σ Γ mfix'.

Axiom cofix_guard_rename : forall P Σ Γ Δ mfix f,
  urenaming P Γ Δ f ->
  let mfix' := map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix in
  cofix_guard Σ Δ mfix ->
  cofix_guard Σ Γ mfix'.

Section BDRenaming.

Context `{cf : checker_flags}.
Context (Σ : global_env_ext).
Context (wfΣ : wf Σ).

Let Pinfer Γ t T :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹ rename f T.

Let Psort Γ t u :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹□ u.

Let Pprod Γ t na A B :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹Π (na,rename f A,rename (shiftn 1 f) B).

Let Pind Γ ind t u args :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  Σ ;;; Δ |- rename f t ▹{ind} (u, map (rename f) args).
  

Let Pcheck Γ t T :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars P t ->
  on_free_vars P T ->
  Σ ;;; Δ |- rename f t ◃ rename f T.

Let PΓ :=
  All_local_env (lift_sorting (fun _ => Pcheck) (fun _ => Psort) Σ).

Let PΓ_rel Γ Γ' :=
  forall P Δ f,
  urenaming P Δ Γ f ->
  on_ctx_free_vars P Γ ->
  on_free_vars_ctx P Γ' ->
  wf_local_bd_rel Σ Δ (rename_context f Γ').

(* Lemma wf_local_app_renaming P Γ Γ' Δ f:
  on_ctx_free_vars P Γ ->
  wf_local_bd Σ (Γ ,,, Δ) ->
  PΓ (Γ ,,, Δ) ->
  urenaming P Γ' Γ f ->
  wf_local_bd Σ (Γ' ,,, rename_context f Δ).
Proof.
  intros hclo wfΓ hP u.
  induction Δ in Γ, Γ', wfΓ, f, u, hP |- *.
  - cbn in *.
    red in hP.
  
  
  - rewrite rename_context_snoc.
    destruct a as [? [] ?] ; cbn in *.
    + constructor ; cbn.
      * eapply IHΔ ; tea.
      * 

  
    rewrite rename_context_snoc /=.
    constructor ; eauto.
    eexists.
    red in p.
    eapply p ; eauto.
    + eapply urenaming_context. 
  
    simpl. destruct t0 as [s Hs].
    rewrite rename_context_snoc /=. constructor; auto.
    red. simpl. exists s.
    eapply (Hs P (Δ' ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
    split => //.
    eapply urenaming_ext.
    { len. now rewrite -shiftnP_add. }
    { reflexivity. } now eapply urenaming_context.
  - destruct t0 as [s Hs]. red in t1.
    rewrite rename_context_snoc /=. constructor; auto.
    * red. exists s.
      apply (Hs P (Δ' ,,, rename_context f Γ0) (shiftn #|Γ0| f)).
      split => //.
      eapply urenaming_ext.
      { len; now rewrite -shiftnP_add. }
      { reflexivity. } now eapply urenaming_context.
    * red. apply (t1 P). split => //.
      eapply urenaming_ext. 
      { len; now rewrite -shiftnP_add. }
      { reflexivity. } now eapply urenaming_context.
Qed. *)

Theorem bidirectional_renaming : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ PΓ_rel.
Proof.
  apply bidir_ind_env.

  - intros Γ wfΓ hΓ. red.
    induction hΓ.
    + constructor.
    + constructor ; tea.
      eexists ; eauto.
    + constructor ; tea.
      eexists ; eauto.

  - intros Γ Γ' wfΓ' allΓ'. red. move => P Δ f hf hΓ hΓ'.
    induction allΓ'.
    + constructor.
    + rewrite rename_context_snoc.
      rewrite on_free_vars_ctx_snoc in hΓ'.
      move: hΓ' => /andP [] ? ?.
      constructor ; eauto.
      1: by eapply IHallΓ' ; eauto.
      eexists.
      eapply s.
      * eapply urenaming_context ; tea.
      * rewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
      * eassumption.
    + rewrite rename_context_snoc.
      rewrite on_free_vars_ctx_snoc in hΓ'.
      move: hΓ' => /andP [] ? /andP /= [] ? ?.
      constructor ; eauto.
      * by eapply IHallΓ' ; eauto.
      * eexists.
        eapply s.
        1: eapply urenaming_context ; tea.
        2: eauto.
        rewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
      * eapply c.
        1: eapply urenaming_context ; tea.
        all: auto.
        rewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
  
  - intros Γ n decl isdecl P Δ f hf hΓ ht.
    eapply hf in isdecl as h => //.
    destruct h as [decl' [isdecl' [? [h1 h2]]]].
    rewrite lift0_rename rename_compose h1 -lift0_rename.
    econstructor. all: auto.

  - intros. red. intros. cbn in *.
    by constructor.
    
  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    econstructor ; eauto.
    eapply X2 ; tea.
    1: by apply urenaming_vass.
    rewrite on_ctx_free_vars_snoc /=.
    apply /andP ; split ; tea.
    
  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    econstructor ; eauto.
    eapply X2 ; tea.
    1: by apply urenaming_vass.
    rewrite on_ctx_free_vars_snoc /=.
    apply /andP ; split ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? /andP [] ? ?.
    econstructor ; eauto.
    eapply X4 ; tea.
    1: by apply urenaming_vdef.
    rewrite on_ctx_free_vars_snoc.
    repeat (apply /andP ; split ; tea).

  - intros. red. move => P Δ f hf hΓ /= /andP [] ? ?.
    rewrite rename_subst0 ; cbn.
    econstructor ; eauto.
    eapply X2 ; tea.
    eapply infering_prod_on_free_vars.
    4: eassumption.
    all: assumption.

  - intros. red. move => P Δ f hf hΓ /= _.
    rewrite rename_subst_instance.
    erewrite rename_closed.
    2: by eapply declared_constant_closed_type ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= _.
    rewrite rename_subst_instance.
    erewrite rename_closed.
    2: by eapply declared_inductive_closed_type ; tea.
    econstructor ; tea.
  
  - intros. red. move => P Δ f hf hΓ /= _.
    erewrite rename_closed.
    2: by eapply declared_constructor_closed_type ; tea.
    econstructor ; tea.

  - intros. red. move => P Δ f hf hΓ /= /andP [] on_pars /andP [] ? /andP [] ? /andP [] ? /forallb_All on_brs.
    rewrite rename_mkApps rename_it_mkLambda_or_LetIn map_app map_skipn /=.
    rewrite rename_case_predicate_context // case_predicate_context_length // rename_predicate_preturn.
    econstructor ; eauto.
    + by eapply rename_wf_predicate.
    + rewrite -rename_case_predicate_context ; tea.
      eapply X1 ; tea.
      eapply on_free_vars_case_predicate_context ; tea.
    + eapply X3 ; tea.
      * rewrite -rename_case_predicate_context //.
        erewrite <- case_predicate_context_length ; tea.
        apply urenaming_context ; assumption.
      * erewrite <- case_predicate_context_length ; tea.
        rewrite /predctx.
        erewrite on_ctx_free_vars_concat.
        apply /andP ; split ; tea.
        rewrite on_free_vars_ctx_on_ctx_free_vars.
        eapply on_free_vars_case_predicate_context ; tea.
    + revert X7.
      rewrite -{2}[subst_instance _ _](rename_closedn_ctx f 0).
      { pose proof (declared_inductive_closed_params isdecl).
        now rewrite closedn_subst_instance_context. }
      rewrite rename_context_telescope rename_telescope_shiftn0 /=.
      admit.
    + rewrite /= /id -map_skipn -map_app.
      eapply cumul_renameP in X8 ; tea.
      * by rewrite !rename_mkApps /= in X8.
      * rewrite on_free_vars_mkApps /=.
        eapply All_forallb, bidirectional_on_free_vars ; tea.
      * rewrite on_free_vars_mkApps /=.
        rewrite forallb_app ; apply /andP ; split ; tea.
        apply forallb_skipn.
        eapply All_forallb, bidirectional_on_free_vars ; tea.
    + by apply rename_wf_branches.
    + eapply Forall2_All2 in H4.
      eapply All2i_All2_mix_left in X9; eauto.
      eapply All2i_All_mix_right in X9 ; eauto.
      eapply All2i_nth_hyp in X9.
      eapply All2i_map_right, (All2i_impl X9) => i cdecl br.
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _).
      move=> [Hnth [ [wfbr [eqbctx [wfbctx [IHbctx [Hbod IHbod]]]]] /andP [on_ctx on_bod] ]].
      rewrite -(rename_closed_constructor_body mdecl cdecl f).
      { eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))); eauto.
        split; eauto. }
      split; auto.
      { simpl. rewrite -rename_cstr_branch_context //.
        1:eapply (declared_inductive_closed_params isdecl).
        rewrite rename_closedn_ctx //.
        eapply closed_cstr_branch_context.
        1:by eapply declared_minductive_closed ; eauto.
        eapply (declared_constructor_closed (c:=(ci.(ci_ind),i))). split; tea.
      }
      cbn -[case_branch_type case_predicate_context].
      rewrite case_branch_type_fst.
      rewrite -rename_case_branch_context_gen //.
      2-3:len.
      1:exact (declared_inductive_closed_params isdecl).
      1:rewrite (wf_branch_length wfbr) //.
      1:rewrite (wf_predicate_length_pars H0).
      1:erewrite declared_minductive_ind_npars ; eauto.
      assert (on_free_vars_ctx P brctxty.1).
      { rewrite test_context_k_closed_on_free_vars_ctx in on_ctx.        
        admit. }
      set (brctx' := rename_context f _).
      split.
      1:by eapply IHbctx ; eauto.
      rewrite rename_case_branch_type //.
      eapply IHbod.
      * rewrite case_branch_type_fst /=.
        relativize #|bcontext br| ; [eapply urenaming_context|] ; tea.
        by rewrite case_branch_context_length.
      * rewrite case_branch_context_length ; tea.
        relativize (#|bcontext br|).
        1: erewrite on_ctx_free_vars_concat.
        2: rewrite case_branch_type_length //.
        2: erewrite wf_branch_length ; eauto.
        apply /andP ; split ; tea.
        by rewrite on_free_vars_ctx_on_ctx_free_vars.
      * rewrite case_branch_type_length //.
        erewrite <- wf_branch_length ; eauto.
      * rewrite case_branch_context_length //.
        admit.
  
  - intros. red. move => P Δ f hf hΓ /= ?.
    rewrite rename_subst0 /= rename_subst_instance map_rev List.rev_length.
    erewrite rename_closedn.
    2: rewrite H0 ; eapply declared_projection_closed_type ; tea.
    econstructor ; eauto.
    by rewrite map_length.    

  - intros. red. move => P Δ f hf hΓ /= /forallb_All ht.
    erewrite map_dtype.
    econstructor.
    + eapply fix_guard_rename ; tea.
    + by rewrite nth_error_map H0 /=.
    + eapply All_mix in X ; tea.
      eapply All_map, All_impl ; tea.
      move => ? [] /andP [] ? ? [] ? [] ? p.
      rewrite -map_dtype.
      eexists.
      eapply p ; tea.
    + eapply All_mix in X0 ; tea.
      eapply All_map, All_impl ; tea.
      move => ? [] /andP [] ? ? [] ? p.
      rewrite -map_dbody -map_dtype rename_fix_context rename_context_length -(fix_context_length mfix) -rename_shiftn.
      eapply p ; tea.
      * rewrite -(fix_context_length mfix).
        eapply urenaming_context ; tea.
      * by apply on_ctx_free_vars_fix_context.
      * rewrite -(Nat.add_0_r (#|mfix|)) fix_context_length.
        apply on_free_vars_lift_impl.
        by rewrite shiftnP0.
    + by apply rename_wf_fixpoint. 

  - intros. red. move => P Δ f hf hΓ /= /forallb_All ht.
    erewrite map_dtype.
    econstructor.
    + eapply cofix_guard_rename ; tea.
    + by rewrite nth_error_map H0 /=.
    + eapply All_mix in X ; tea.
      eapply All_map, All_impl ; tea.
      move => ? [] /andP [] ? ? [] ? [] ? p.
      rewrite -map_dtype.
      eexists.
      eapply p ; tea.
    + eapply All_mix in X0 ; tea.
      eapply All_map, All_impl ; tea.
      move => ? [] /andP [] ? ? [] ? p.
      rewrite -map_dbody -map_dtype rename_fix_context rename_context_length -(fix_context_length mfix) -rename_shiftn.
      eapply p ; tea.
      * rewrite -(fix_context_length mfix).
        eapply urenaming_context ; tea.
      * by apply on_ctx_free_vars_fix_context.
      * rewrite -(Nat.add_0_r (#|mfix|)) fix_context_length.
        apply on_free_vars_lift_impl.
        by rewrite shiftnP0.
    + by apply rename_wf_cofixpoint. 
  
  - intros. red. intros P Δ f hf ht.
    econstructor ; eauto.
    rewrite -/(rename f (tSort u)).
    eapply red_rename ; tea.
    eapply infering_on_free_vars ; tea.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    rewrite -/(rename f (tProd na A B)).
    eapply red_rename ; tea.
    eapply infering_on_free_vars ; tea.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    rewrite -/(rename f (tInd ind ui)) -rename_mkApps.
    eapply red_rename ; tea.
    eapply infering_on_free_vars ; tea.

  - intros. red. intros P Δ f hf hΓ ht.
    econstructor ; eauto.
    eapply cumul_renameP ; tea.
    eapply infering_on_free_vars.
    4: eassumption.
    all: assumption.

Admitted.



Lemma strengthenP_unlift (p : nat -> bool) n k t : 
  on_free_vars (strengthenP k n p) t ->
  ∑ t', t = lift n k t' × on_free_vars p t'.
Proof.
  intros ofv.
  remember (strengthenP k n p) as q eqn:Heqq.
  assert (q =1 strengthenP k n p) by now subst.
  clear Heqq.
  revert n k p H.
  pattern q, t.
  revert ofv.
  eapply term_on_free_vars_ind.
  
  - intros.
    rewrite H0 /strengthenP in H.
    destruct (Nat.ltb_spec0 i k).
    1: exists (tRel i) ; split ; cbn ; [destruct (Nat.leb_spec0 k i) ; [lia|auto]|auto].
    destruct (Nat.ltb_spec0 i (k + n)).
    1: congruence.
    exists (tRel (i - n)) ; split ; cbn.
    2: auto.
    destruct (Nat.leb_spec0 k (i - n)).
    2: lia.
    f_equal.
    lia.
  
  - intros. exists (tVar i) ; auto.
  
  - intros.
    eapply All_impl in X0.
    2: intros ? H1 ; apply H1 ; tea.
    apply All_sigT in X0 as [l' a].
    apply All2_prod_inv in a as [a a'].
    apply All2_right in a'.
    eexists (tEvar _ _) ; split.
    + cbn ; f_equal.
      eapply All2_eq, All2_map_right ; eauto.
    + by apply All_forallb.

  - intros ; eexists (tSort _) ; split ; eauto ; reflexivity.
  
  - intros.
    edestruct X as [? []] ; eauto.
    edestruct X0 as [? []] ; eauto.
    { etransitivity.
      2: by apply shiftnP_strengthenP.
      rewrite H1 ; reflexivity.
    }
    subst.
    eexists (tProd _ _ _) ; split.
    all: cbn.
    1: reflexivity.
    by apply andb_true_iff ; split.

  - intros.
    edestruct X as [? []] ; eauto.
    edestruct X0 as [? []] ; eauto.
    { etransitivity.
      2: by apply shiftnP_strengthenP.
      rewrite H1 ; reflexivity.
    }
    subst.
    eexists (tLambda _ _ _) ; split.
    all: cbn.
    1: reflexivity.
    by apply andb_true_iff ; split.
    
  - intros.
    edestruct X as [? []] ; eauto.
    edestruct X0 as [? []] ; eauto.
    edestruct X1 as [? []] ; eauto.
    { etransitivity.
      2: by apply shiftnP_strengthenP.
      rewrite H2 ; reflexivity.
    }
    subst.
    eexists (tLetIn _ _ _ _) ; split.
    all: cbn.
    1: reflexivity.
    by repeat (apply andb_true_iff ; split).

  - intros.
    edestruct X as [? []] ; eauto.
    edestruct X0 as [? []] ; eauto.
    subst.
    eexists (tApp _ _) ; split.
    all: cbn.
    1: reflexivity.
    by apply andb_true_iff ; split.

  - intros.
    eexists (tConst _ _) ; split ; eauto.
    reflexivity.

  - intros.
    eexists (tInd _ _) ; split ; eauto.
    reflexivity.

  - intros.
    eexists (tConstruct _ _ _) ; split ; eauto.
    reflexivity.

  - intros.
    admit.
    
  - intros.
    edestruct X as [? []] ; eauto.
    subst.
    eexists (tProj _ _) ; split.
    1: reflexivity.
    auto.

  - intros.
    admit.
    
  - intros.
    admit.
    
Admitted.

Lemma strengthening_leq_term `{cf : checker_flags} (Σ : global_env_ext) (Γ' Γ'' : context) t u :
  leq_term Σ Σ (lift #|Γ''| #|Γ'| t) (lift #|Γ''| #|Γ'| u) ->
  leq_term Σ Σ t u.
Proof.
Admitted.

Lemma strengthening_red `{cf : checker_flags} Σ (wfΣ : wf Σ) Γ Γ' Γ'' t u :
  red Σ (Γ ,,, Γ'' ,,, (lift_context #|Γ''| 0 Γ')) (lift #|Γ''| #|Γ'| t) u ->
  ∑ u', u = lift #|Γ''| #|Γ'| u' × red Σ (Γ ,,, Γ') t u'.
Proof.
Admitted.

Lemma rename_context_lift_context n k Γ :
  rename_context (lift_renaming n k) Γ = lift_context n k Γ.
Proof.
  rewrite /rename_context /lift_context.
  apply fold_context_k_ext.
  intros i.
  rewrite shiftn_lift_renaming.
  symmetry.
  intro.
  by apply lift_rename.
Qed.

Lemma unlift_mkApps t args n k u:
  mkApps t args = lift n k u ->
  ∑ t' args', t = lift n k t' × args = map (lift n k) args' × u = mkApps t' args'.
Proof.
  intros.
  induction args in t, u, H |- *.
  - cbn in *.
    eexists ; exists [] ; by repeat split.
  - cbn in *.
    edestruct IHargs as (t'&?&e&?&?) ; tea.
    destruct t' ; inversion e ; subst ; clear e. 
    subst.
    eexists ; eexists (_ :: _) ; repeat split.
Qed.


Section BDStrengthening.

  (** We work in a fixed, well-formed global environment*)

  Context `{cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Let Pinfer Γ t T :=
    forall Δ Δ' Δ'' t',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    ∑ T',
    T = lift #|Δ''| #|Δ'| T' × Σ ;;; Δ ,,, Δ' |- t' ▹ T'.

  Let Psort Γ t u :=
    forall Δ Δ' Δ'' t',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    Σ ;;; Δ ,,, Δ' |- t' ▹□ u.

  Let Pprod Γ t na A B :=
    forall Δ Δ' Δ'' t',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    ∑ A' B',
    A = lift #|Δ''| #|Δ'| A' × B = lift #|Δ''| (S #|Δ'|) B' × Σ ;;; Δ ,,, Δ' |- t' ▹Π (na,A',B').

  Let Pind Γ ind t u args :=
    forall Δ Δ' Δ'' t',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    ∑ args',
    args = map (lift #|Δ''| #|Δ'|) args' × Σ ;;; Δ ,,, Δ' |- t' ▹{ind} (u,args').

  Let Pcheck Γ t T :=
    forall Δ Δ' Δ'' t' T',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    t = lift #|Δ''| #|Δ'| t' ->
    T = lift #|Δ''| #|Δ'| T' ->
    Σ ;;; Δ ,,, Δ' |- t' ◃ T'.
  
  Let PΓ (Γ : context) :=
    forall Δ Δ' Δ'',
    Γ = Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ' ->
    wf_local_bd Σ (Δ ,,, Δ').

  Theorem bidirectional_strengthening : env_prop_bd Σ Pcheck Pinfer Psort Pprod Pind PΓ.
  Proof.
    apply bidir_ind_env.

    - intros. red. intros.
      subst.
      apply All_local_env_app ; split.
      1: by clear X ; repeat apply All_local_env_app_inv in wfΓ as [wfΓ _].
      induction Δ' as [|[? [] ?] ].
      + constructor.
      + rewrite -/(snoc Δ' _) lift_context_snoc Nat.add_0_r !app_context_cons in wfΓ, X.
        inversion X ; subst.
        constructor.
        * eauto.
        * eexists.
          eauto.
        * eapply X1 ; eauto.
      + rewrite -/(snoc Δ' _) lift_context_snoc Nat.add_0_r !app_context_cons in wfΓ, X.
        inversion X ; subst.
        constructor ; eauto.
        eexists ; eauto. 
    
    - intros. red. intros.
      subst.
      destruct t' ; cbn in H1 ; inversion H1 ; subst ; clear H1.
      destruct (Nat.leb_spec0 #|Δ'| n0).
      + rewrite /app_context /lift_context -nth_error_ge // in H.
        eexists ; split.
        2: constructor ; tea.
        rewrite simpl_lift.
        3: f_equal.
        all: lia.
      + rewrite /app_context /lift_context nth_error_app_context_lt in H.
        1: by rewrite fold_context_k_length ; lia.
        fold (lift_context #|Δ''| 0 Δ') in H.
        rewrite -rename_context_lift_context in H.
        rewrite nth_error_rename_context in H.
        remember (nth_error Δ' n0) as decl'.
        destruct decl' ; cbn in * ; inversion H ; subst ; clear H.
        eexists ; split.
        2:{
          constructor.
          rewrite nth_error_app_context_lt ; eauto.
          lia.
        }
        cbn.
        rewrite shiftn_lift_renaming Nat.add_0_r -lift_rename permute_lift.
        2: f_equal.
        all: lia.


    - intros. red. intros. subst.
      destruct t' ; cbn in H1 ; inversion H1 ; subst ; clear H1.
      eexists ; split.
      2: by constructor.
      reflexivity.

    - intros. red in X0, X2 |- *. intros. subst.
      destruct t' ; cbn in H0 ; inversion H0 ; subst ; clear H0.
      eexists ; split.
      2:{ constructor ; eauto.
        rewrite -app_context_cons.
        eapply X2 ; eauto.
        by rewrite -app_context_cons lift_context_snoc Nat.add_0_r.
      }
      by reflexivity.

    - intros. red in X0, X2 |- *. intros. subst.
      destruct t' ; cbn in H0 ; inversion H0 ; subst ; clear H0.
      edestruct X2 as (?&?&?).
      2: change (S #|Δ'|) with (#|Δ' ,, vass na t'1|) ; reflexivity.
      1: rewrite -app_context_cons lift_context_snoc Nat.add_0_r ; reflexivity.
      eexists ; split.
      2: econstructor ; eauto.
      cbn.
      by f_equal.

    - intros. red in X0, X2 |- *. intros. subst.
      destruct t' ; cbn in H0 ; inversion H0 ; subst ; clear H0.
      edestruct X4 as (?&?&?).
      2: change (S #|Δ'|) with (#|Δ' ,, vdef na t'1 t'2|) ; reflexivity.
      1: rewrite -app_context_cons lift_context_snoc Nat.add_0_r ; reflexivity.
      eexists ; split.
      2: econstructor ; eauto.
      cbn.
      by f_equal.
    
    - intros. red in X0, X2 |- *. intros. subst.
      destruct t' ; cbn in H0 ; inversion H0 ; subst ; clear H0.
      edestruct X0 as (?&?&?&?&?).
      1-2: reflexivity.
      eexists ; split.
      2: econstructor ; eauto.
      subst.
      by rewrite distr_lift_subst10.
      
    - intros. red. intros. subst.
      destruct t' ; cbn in H2 ; inversion H2 ; subst ; clear H2.
      eexists ; split.
      2: constructor ; tea.
      erewrite <- (lift_closed _ _ (cst_type _)) at 1.
      1: by eapply subst_instance_lift.
      eapply closed_upwards.
      1: eapply declared_constant_closed_type ; tea.
      lia.
    
    - intros. red. intros. subst.
      destruct t' ; cbn in H2 ; inversion H2 ; subst ; clear H2.
      eexists ; split.
      2: econstructor ; tea.
      erewrite <- (lift_closed _ _ (ind_type _)) at 1.
      1: by eapply subst_instance_lift.
      eapply closed_upwards.
      1: eapply declared_inductive_closed_type ; tea.
      lia.

    - intros. red. intros. subst.
      destruct t' ; cbn in H2 ; inversion H2 ; subst ; clear H2.
      eexists ; split.
      2: econstructor ; tea.
      erewrite <- (lift_closed _ _ (type_of_constructor _ _ _ _)) at 1.
      1: reflexivity.
      eapply closed_upwards.
      1: eapply declared_constructor_closed_type ; tea.
      lia.
    
    - intros. red. intros. subst.
      destruct t' ; cbn in H6 ; inversion H6 ; subst ; clear H6.
      admit.
    
    - intros. red. intros. subst.
      destruct t' ; cbn in H2 ; inversion H2 ; subst ; clear H2.
      edestruct X0 as (?&?&?).
      1-2: reflexivity.
      subst.
      rewrite map_length in H0.
      eexists ; split.
      2: econstructor ; eauto.
      rewrite -map_rev -map_cons distr_lift_subst.
      f_equal.
      symmetry.
      apply lift_closed.
      rewrite closedn_subst_instance.
      eapply closed_upwards.
      1: eapply declared_projection_closed_type ; tea.
      rewrite /= List.rev_length.
      lia.

    - intros. red. intros. subst.
      destruct t' ; cbn in H3 ; inversion H3 ; subst ; clear H3.
      admit.
    
    - admit.
    
    - intros. red in X0 |- *. intros. subst.
      edestruct X0 as (?&?&?).
      1-2: reflexivity.
      subst.
      apply strengthening_red in X1 as [u' []] ; auto.
      destruct u' ; inversion e ; subst.
      econstructor ; tea.

    - intros. red in X0 |- *. intros. subst.
      edestruct X0 as (?&?&?).
      1-2: reflexivity.
      subst.
      apply strengthening_red in X1 as [u' []] ; auto.
      destruct u' ; inversion e ; subst.
      repeat eexists ; tea.

    - intros. red in X0 |- *. intros. subst.
      edestruct X0 as (?&?&?).
      1-2: reflexivity.
      subst.
      apply strengthening_red in X1 as [u' []] ; auto.
      apply unlift_mkApps in e as (?&?&?&?&?).
      destruct x0 ; inversion e.
      subst.
      repeat eexists ; tea.

    - intros. red in X0 |- *. intros. subst.
      edestruct X0 as (?&?&?).
      1-2: reflexivity.
      subst.
      econstructor ; tea.
      apply cumul_alt.
      apply cumul_alt in X1 as (?&?&(r&r')&?).
      apply strengthening_red in r as (?&?&?).
      apply strengthening_red in r' as (?&?&?).
      all: tea.
      subst.
      do 2 eexists ; split.
      1: split ; tea.
      eapply strengthening_leq_term ; tea.

  Admitted.
