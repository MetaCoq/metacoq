From Coq Require Import String Bool List PeanoNat Lia Morphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst
     PCUICLiftSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening PCUICInversion
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration PCUICUnivSubst
     PCUICParallelReductionConfluence
     PCUICUnivSubstitution PCUICConversion PCUICContexts PCUICArities
     PCUICSpine PCUICInductives PCUICContexts
     PCUICSigmaCalculus PCUICClosed.

From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.
Require Import ssreflect.

Derive Signature for typing cumul.

Arguments Nat.sub : simpl never.

Hint Extern 30 (wf_local ?Σ ?Γ) =>
match goal with
| [ H : typing Σ Γ _ _ |- _ ] => apply (typing_wf_local H)
end : pcuic.

Ltac pcuic := try solve [ intuition typeclasses eauto with pcuic ].

Section Validity.
  Context `{cf : config.checker_flags}.

  Definition weaken_env_prop_full
             (P : global_env_ext -> context -> term -> term -> Type) :=
    forall (Σ : global_env_ext) (Σ' : global_env), wf Σ' -> extends Σ.1 Σ' ->
                                                   forall Γ t T, P Σ Γ t T -> P (Σ', Σ.2) Γ t T.

  Lemma isWfArity_or_Type_weaken_full : weaken_env_prop_full (fun Σ Γ t T => isWfArity_or_Type Σ Γ T).
  Proof.
    red. intros.
    destruct X1. left. destruct i as [ctx [s [Heq Hs]]].
    exists ctx, s. split; auto with pcuic.
    right. destruct i as [u Hu]; exists u; pcuic.
    unshelve eapply (weaken_env_prop_typing _ _ _ _ X0 _ _ (Some (tSort u))); eauto with pcuic.
    red. simpl. destruct Σ. eapply Hu.
  Qed.
  Hint Resolve isWfArity_or_Type_weaken_full : pcuic.

  Lemma isWfArity_or_Type_weaken :
    weaken_env_prop
      (lift_typing (fun Σ Γ (_ T : term) => isWfArity_or_Type Σ Γ T)).
  Proof.
    red. intros.
    unfold lift_typing in *. destruct T. now eapply (isWfArity_or_Type_weaken_full (_, _)).
    destruct X1 as [s Hs]; exists s. now eapply (isWfArity_or_Type_weaken_full (_, _)).
  Qed.
  Hint Resolve isWfArity_or_Type_weaken : pcuic.

  Lemma isWfArity_or_Type_extends : forall (cf : checker_flags) (Σ : global_env)
      (Σ' : PCUICEnvironment.global_env) (φ : universes_decl),
    wf Σ' ->
    extends Σ Σ' ->
    forall Γ : context,
    forall t0 : term,
    isWfArity_or_Type (Σ, φ) Γ t0 -> isWfArity_or_Type (Σ', φ) Γ t0.
  Proof.
    intros.
    destruct X1 as [[ctx [s [eq wf]]]|[s Hs]].
    - left; exists ctx, s; intuition auto.
      apply (PCUICWeakeningEnv.weaken_wf_local (Σ, φ)); auto.
    - right. exists s.
      eapply (env_prop_typing _ _ PCUICWeakeningEnv.weakening_env (Σ, φ)); auto.
      simpl. now eapply wf_extends.
  Qed.

  Lemma weaken_env_prop_isWAT :
    weaken_env_prop
    (lift_typing
        (fun (Σ0 : PCUICEnvironment.global_env_ext)
          (Γ0 : PCUICEnvironment.context) (_ T : term) =>
        isWfArity_or_Type Σ0 Γ0 T)).
  Proof.
    red. intros.
    red in X1 |- *.
    destruct T. now eapply isWfArity_or_Type_extends.
    destruct X1 as [s Hs]; exists s; now eapply isWfArity_or_Type_extends.
  Qed.

  Local Notation isWAT :=
    (lift_typing
      (fun (Σ0 : PCUICEnvironment.global_env_ext) (Γ : context) (_ T : term)
    => isWfArity_or_Type Σ0 Γ T)).

  (* k is the projection number: 0 is the first argument *)
  Definition projection_type mdecl ind k ty := 
    let u := PCUICLookup.abstract_instance (PCUICEnvironment.ind_universes mdecl) in
    let indsubst := inds (inductive_mind ind) u (ind_bodies mdecl) in
    let projsubst := projs ind (ind_npars mdecl) k in
    subst indsubst (S (ind_npars mdecl))
        (subst0 projsubst (lift 1 k 
          (subst (extended_subst (ind_params mdecl) 0) k
           (lift (context_assumptions (ind_params mdecl)) (k + #|ind_params mdecl|)
            ty)))).
            
  Definition projection_type' mdecl ind k ty :=
    let u := PCUICLookup.abstract_instance (PCUICEnvironment.ind_universes mdecl) in
    let indsubst := inds (inductive_mind ind) u (ind_bodies mdecl) in
    let projsubst := projs ind (ind_npars mdecl) k in
    (subst0 projsubst
      (subst (extended_subst (ind_params mdecl) 0) (S k)
      (lift 1 k (subst indsubst (k + #|ind_params mdecl|) ty)))).
 
  Definition projection_decl_type mdecl ind k ty := 
    let u := PCUICLookup.abstract_instance (PCUICEnvironment.ind_universes mdecl) in
    let indsubst := inds (inductive_mind ind) u (ind_bodies mdecl) in
    let projsubst := projs ind (ind_npars mdecl) k in
    subst indsubst (S (ind_npars mdecl))
        (subst0 projsubst (lift 1 k ty)).

  Lemma on_projections_decl {Σ mdecl ind idecl cs} :
    forall (Hdecl : declared_inductive Σ mdecl ind idecl) (wfΣ : wf Σ),
    let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl in
    let u := PCUICLookup.abstract_instance (ind_universes mdecl) in
    on_projections mdecl (inductive_mind ind) (inductive_ind ind) idecl (oib.(ind_indices)) cs ->
    Alli (fun i decl => 
      ∑ pdecl, 
        (nth_error (ind_projs idecl) (context_assumptions (cshape_args cs) - S i) = Some pdecl))
      0 (smash_context [] cs.(cshape_args)).
  Proof.
    intros.
    destruct X as [_ _ _ on_projs_all on_projs].
    eapply forall_nth_error_Alli.
    intros.
    pose proof (equiv_inv _ _ (nth_error_Some' (ind_projs idecl) (context_assumptions (cshape_args cs) - S i))).
    apply X. eapply nth_error_Some_length in H. 
      autorewrite with len in H. simpl in H; lia.
  Qed.

  Lemma consistent_instance_ext_abstract_instance Σ mdecl mind :
    wf Σ ->
    declared_minductive Σ mind mdecl ->
    consistent_instance_ext (Σ, ind_universes mdecl) (ind_universes mdecl)
       (PCUICLookup.abstract_instance (ind_universes mdecl)).
  Proof.
    todo "universes"%string.
  Defined.

  Lemma subst_id s Γ t : 
    closedn #|s| t ->
    assumption_context Γ ->
    s = List.rev (to_extended_list Γ) ->
    subst s 0 t = t.
  Proof.
    intros cl ass eq.
    autorewrite with sigma.
    rewrite -{2}(subst_ids t).
    eapply inst_ext_closed; eauto.
    intros.
    unfold ids, subst_consn. simpl.
    destruct (equiv_inv _ _ (nth_error_Some' s x) H). rewrite e.
    subst s.
    rewrite /to_extended_list /to_extended_list_k in e.
    rewrite List.rev_length in cl, H. autorewrite with len in *.
    rewrite reln_alt_eq in e.
    rewrite app_nil_r List.rev_involutive in e.
    clear -ass e. revert e.
    rewrite -{2}(Nat.add_0_r x).
    generalize 0.
    induction Γ in x, ass, x0 |- * => n. simpl in *. rewrite nth_error_nil => //.
    depelim ass; simpl.
    destruct x. simpl in *. congruence.
    move=> e; specialize (IHΓ ass); simpl in e.
    specialize (IHΓ _ _ _ e). subst x0. f_equal. lia.
  Qed.
  
  Lemma isType_closed {Σ Γ T} : wf Σ.1 -> isType Σ Γ T -> closedn #|Γ| T.
  Proof. intros wfΣ [s Hs]. now eapply subject_closed in Hs. Qed.

  Lemma subst_instance_context_id Σ univs Γ : 
    let u :=  PCUICLookup.abstract_instance univs in
    wf_local (Σ, univs) Γ ->
    subst_instance_context u Γ = Γ.
  Proof.
    todo "universes"%string.
  Qed.

  Lemma subst_instance_ind_sort_id Σ mdecl ind idecl : 
    declared_inductive Σ mdecl ind idecl ->
    forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl)
    (inductive_mind ind) mdecl (inductive_ind ind) idecl),
    let u :=  PCUICLookup.abstract_instance (ind_universes mdecl) in
    subst_instance_univ u (ind_sort oib) = ind_sort oib.
  Proof.
    todo "universes"%string.
  Qed.
  
  Lemma subst_instance_ind_type_id Σ mdecl ind idecl : 
    declared_inductive Σ mdecl ind idecl ->
    let u :=  PCUICLookup.abstract_instance (ind_universes mdecl) in
    subst_instance_constr u (ind_type idecl) = ind_type idecl.
  Proof.
    todo "universes"%string.
  Qed.

  Lemma isType_subst_instance_id Σ univs Γ T : 
    let u :=  PCUICLookup.abstract_instance univs in
    isType (Σ, univs) Γ T -> subst_instance_constr u T = T.
  Proof.
    todo "universes"%string.
  Qed.

  Lemma wf_local_smash_end Σ Γ Δ : 
    wf Σ.1 ->
    wf_local Σ (Γ ,,, Δ) -> wf_local Σ (Γ ,,, smash_context [] Δ).
  Proof.
    intros wfΣ  wf. 
    apply All_local_env_app_inv. split.
    now apply All_local_env_app in wf.
    eapply wf_local_rel_smash_context; auto.
  Qed.

  (* Well, it's a smash_context mess! *)
  Lemma declared_projections {Σ : global_env_ext} {mdecl ind idecl} : 
    forall (wfΣ : wf Σ.1) (Hdecl : declared_inductive Σ mdecl ind idecl),
    let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ Hdecl in
    let u := PCUICLookup.abstract_instance (ind_universes mdecl) in
    match ind_cshapes oib return Type with
    | [cs] => 
      on_projections mdecl (inductive_mind ind) (inductive_ind ind) 
        idecl (ind_indices oib) cs -> 
      Alli (fun i pdecl => 
      isType (Σ.1, ind_universes mdecl)
        ((vass nAnon (mkApps (tInd ind u) 
              (to_extended_list (smash_context [] (ind_params mdecl)))))::
           smash_context [] (ind_params mdecl)) pdecl.2 * 
        ∑ decl, 
          (nth_error (smash_context [] (cshape_args cs)) 
            (context_assumptions (cshape_args cs) - S i) = Some decl) *
          wf_local (Σ.1, ind_universes mdecl) 
            (arities_context (ind_bodies mdecl) ,,, 
              ind_params mdecl ,,, smash_context [] (cshape_args cs)) *
          (projection_type mdecl ind i decl.(decl_type) = pdecl.2) *
          (projection_type mdecl ind i decl.(decl_type) = 
             projection_type' mdecl ind  i decl.(decl_type)))%type
        0 (ind_projs idecl)
    | _ => True
    end.
  Proof.
    intros wfΣ decli oib u.
    destruct (ind_cshapes oib) as [|? []] eqn:Heq; try contradiction; auto.
    intros onps.
    eapply forall_nth_error_Alli.
    set (eos := CoreTactics.the_end_of_the_section).
    intros i. Subterm.rec_wf_rel IH i lt. clear eos.
    rename pr1 into i. simpl; clear H0.
    set (p := ((ind, ind_npars mdecl), i)).
    intros pdecl Hp. simpl.
    set(isdecl := (conj decli (conj Hp eq_refl)) :
       declared_projection Σ.1 mdecl idecl p pdecl).
    destruct (on_declared_projection wfΣ isdecl) as [oni onp].
    set (declared_inductive_inv _ _ _ _) as oib' in onp.
    change oib' with oib in *. clear oib'.
    simpl in oib.
    have onpars := onParams _ _ _ _ 
      (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ decli.p1).
    have parslen := onNpars _ _ _ _ 
      (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ decli.p1).
    simpl in onp. rewrite Heq in onp. 
    destruct onp as [[[wfargs onProjs] Hp2] onp].
    red in onp.
    destruct (nth_error (smash_context [] _) _) eqn:Heq'; try contradiction.
    destruct onp as [onna onp].
    rewrite {}onp.
    apply on_projections_decl in onps.
    clearbody oib.
    assert(projslen : #|ind_projs idecl| = (context_assumptions (cshape_args c))).
    { now destruct onProjs. }
    assert (some_proj :#|ind_projs idecl| > 0).
    { destruct isdecl as [ [] []]. now apply nth_error_Some_length in H1. }
    simpl.
    assert (wfarities : wf_local (Σ.1, ind_universes mdecl)
       (arities_context (ind_bodies mdecl))).
    { eapply wf_arities_context; eauto. now destruct isdecl as [[] ?]. }
    eapply PCUICClosed.type_local_ctx_All_local_env in wfargs.
    2:{ eapply All_local_env_app_inv. split; auto.
        red in onpars. eapply (All_local_env_impl _ _ _ onpars).
        intros. destruct T; simpl in *.
        - eapply weaken_ctx; auto.
        - destruct X as [s Hs]. exists s. apply weaken_ctx; auto. }
    pose proof wfargs as X.
    rewrite -(app_context_nil_l (arities_context _)) in X.
    rewrite -app_context_assoc in X.
    eapply (substitution_wf_local _ []) in X; auto.
    2:{ eapply subslet_inds_gen; eauto. }
    rewrite app_context_nil_l in X.
    move: X.
    rewrite subst_context_app.
    rewrite (closed_ctx_subst _ _ (ind_params mdecl)).
    red in onpars. eapply closed_wf_local; [|eauto]. auto.
    assert (parsu : subst_instance_context u (ind_params mdecl) = ind_params mdecl). 
    { red in onpars. eapply subst_instance_context_id. eauto. }
    assert (sortu : subst_instance_univ u (ind_sort oib) = ind_sort oib).
    { apply subst_instance_ind_sort_id; eauto. }
    pose proof (spine_subst_to_extended_list_k (Σ.1, ind_universes mdecl)
      (ind_params mdecl) []).
    forward X; auto.
    forward X. rewrite app_context_nil_l; auto.
    rewrite app_context_nil_l in X.
    rewrite closed_ctx_lift in X.
    red in onpars. eapply closed_wf_local; [|eauto]. auto.
    assert(wf_local (Σ.1, ind_universes mdecl) (ind_params mdecl ,,
       vass nAnon (mkApps (tInd ind u) (to_extended_list (ind_params mdecl))))).
    { constructor. auto. red. exists (ind_sort oib).
      eapply type_mkApps. econstructor; eauto.
      destruct isdecl as []; eauto. subst u.
      eapply consistent_instance_ext_abstract_instance. 2:destruct decli; eauto. 
      now auto.
      rewrite (ind_arity_eq oib).
      rewrite subst_instance_constr_it_mkProd_or_LetIn.
      rewrite -(app_nil_r (to_extended_list _)).
      eapply typing_spine_it_mkProd_or_LetIn'; auto.
      rewrite parsu. eapply X.
      constructor. left. eexists _, _; simpl; intuition auto.
      simpl in oib.
      pose proof (onProjs.(on_projs_noidx _ _ _ _ _ _)).
      destruct (ind_indices oib); simpl in H; try discriminate.
      simpl. rewrite sortu. reflexivity.
      rewrite -subst_instance_constr_it_mkProd_or_LetIn.
      right. pose proof (onArity oib). rewrite -(oib.(ind_arity_eq)).
      destruct X0 as [s Hs]. exists s.
      eapply (weaken_ctx (Γ:=[])); auto.
      rewrite (subst_instance_ind_type_id Σ.1 _ ind); auto. }
    intros wf.
    generalize (weakening_wf_local _ _ _ [_] _ wf X0).
    simpl; clear X0 wf.
    move/wf_local_smash_context => /=.
    rewrite smash_context_app /= smash_context_acc.

    set(indsubst := (inds (inductive_mind ind) 
      (PCUICLookup.abstract_instance (PCUICEnvironment.ind_universes mdecl))
      (PCUICEnvironment.ind_bodies mdecl))) in *.
    set (projsubst :=  (projs {| inductive_mind := inductive_mind ind; 
       inductive_ind := inductive_ind ind |}
      (PCUICEnvironment.ind_npars mdecl) i)) in *.
    rewrite lift_context_app. simpl.
    rewrite [subst_context _ _ (_ ++ _)]subst_context_app.
    simpl. unfold app_context. simpl.
    unfold lift_context at 3. unfold fold_context. simpl.
    unfold map_decl. simpl. rewrite lift_mkApps. simpl.
    rewrite {3}/subst_context /fold_context /= /map_decl /= subst_mkApps /=.
    rewrite /to_extended_list lift_to_extended_list_k.
    rewrite extended_subst_to_extended_list_k.
    fold (to_extended_list (smash_context [] (ind_params mdecl))).
    intros wfl.
    rewrite PCUICClosed.closed_ctx_lift in wfl.
    { eapply closedn_smash_context.
      eapply closed_wf_local in wfargs; auto.
      rewrite closedn_ctx_app in wfargs.
      simpl in wfargs; autorewrite with len in wfargs.
      move/andP: wfargs => [_ clargs].
      clear -isdecl wfΣ clargs.
      eapply (closedn_ctx_lift 1).
      rewrite Nat.add_0_r.
      eapply (closedn_ctx_subst 0 #|ind_params mdecl|).
      now unfold indsubst; rewrite inds_length.
      unfold indsubst.
      eapply declared_minductive_closed_inds.
      2:destruct isdecl as [ [] ?]; eauto. eauto. } 
    rewrite -app_assoc in wfl.
    apply All_local_env_app in wfl as [wfctx wfsargs].
    rewrite smash_context_app in Heq'.
    rewrite smash_context_acc in Heq'. 
    rewrite nth_error_app_lt in Heq'.
    autorewrite with len. lia.
    set (idx := context_assumptions (cshape_args c) - S i) in *.
    unshelve epose proof (nth_error_All_local_env (n:=idx) _ wfsargs).
    autorewrite with len. rewrite /lift_context /subst_context !context_assumptions_fold.
    subst idx; lia.
    destruct (nth_error (subst_context _ 1 _) idx) as [c1|] eqn:hidx.
    simpl in X0. unfold on_local_decl in X0.
    assert(decl_body c1 = None).
    { apply nth_error_assumption_context in hidx; auto.
      rewrite /subst_context /lift_context.
      apply assumption_context_fold, smash_context_assumption_context. constructor. }
    rewrite H in X0. 2:{ simpl in X0; contradiction. }
    destruct X0 as [s Hs].
    eapply (substitution (Σ.1, ind_universes mdecl) (_ :: _) (skipn _ _) projsubst []) 
      in Hs; auto.
    simpl in Hs.
    rewrite nth_error_subst_context in Heq'.
    autorewrite with len in Heq'. simpl in Heq'.
    epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl))).
    autorewrite with len in H0.
    erewrite H0 in Heq'. simpl in Heq'. clear H0.
    rewrite !option_map_two in Heq'.
    apply option_map_Some in Heq' as [arg [nthidx eq]].
    rewrite nth_error_subst_context in hidx.
    autorewrite with len in hidx. simpl in hidx.
    rewrite (smash_context_lift []) in hidx.
    rewrite (smash_context_subst []) in hidx.
    rewrite (nth_error_lift_context_eq _ [vass nAnon (mkApps (tInd ind u)  [])]) in hidx.
    simpl in hidx. autorewrite with len in hidx.
    rewrite nth_error_subst_context in hidx. autorewrite with len in hidx.
    simpl in hidx.
    rewrite !option_map_two in hidx.
    assert(clarg : closedn (i + #|ind_params mdecl| + #|ind_bodies mdecl|) (decl_type arg)).
    { assert(wf_local (Σ.1, ind_universes mdecl)
       (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, 
        smash_context [] (cshape_args c))).
      apply All_local_env_app_inv; split; auto.
      now apply All_local_env_app in wfargs as [wfindpars wfargs].
      apply wf_local_rel_smash_context; auto.
      eapply closed_wf_local in X0; auto.
      eapply (closedn_ctx_decl (n:=idx)) in X0; eauto.
      2:{ rewrite nth_error_app_lt. autorewrite with len. simpl; lia.
          now eapply nthidx. }
      move/andP: X0 => [_ clty]. 
      eapply closed_upwards; eauto.
      autorewrite with len; simpl. simpl in idx. lia. }
    rewrite nthidx in hidx. simpl in hidx. noconf hidx. simpl in *.
    subst c0.
    destruct ind as [mind ind]; simpl in *.
    autorewrite with len. simpl.
    revert Hs.
    assert(context_assumptions (cshape_args c) - S idx = i) as -> by lia.
    rewrite !context_assumptions_fold.
    assert(context_assumptions (cshape_args c) - S idx + 1 = S i) as -> by lia.
    intros Hs.
    assert (projection_type mdecl {| inductive_mind := mind; inductive_ind := ind |}
       i (decl_type arg) = 
      projection_type' mdecl {| inductive_mind := mind; inductive_ind := ind |} i
         (decl_type arg)).
    { eapply nth_error_Some_length in nthidx.
      autorewrite with len in nthidx. simpl in nthidx.
      unfold projection_type, projection_type'. simpl.
      fold indsubst projsubst.
      rewrite distr_subst.
      f_equal. 
      { clear. subst projsubst. induction i; simpl; auto.
        f_equal. auto. }
      rewrite /projsubst projs_length.
      replace (context_assumptions (cshape_args c) - S idx + 1) with
      (context_assumptions (cshape_args c) - idx) by lia.
      simpl in idx.
      epose proof (commut_lift_subst_rec _ _ 1 (i + ind_npars mdecl) i).
      rewrite -Nat.add_1_r Nat.add_assoc. erewrite <-H0. 2:lia.
      clear H0.
      epose proof (commut_lift_subst_rec _ _ 1 i i) as hs.
      rewrite Nat.add_1_r in hs. rewrite <- hs; try lia. clear hs. f_equal.
      rewrite distr_subst_rec.
      clear H.
      rewrite map_subst_closedn.
      rewrite -parslen.
      eapply closedn_extended_subst. eapply closed_wf_local. 2:eauto. auto.
      f_equal. autorewrite with len.
      epose proof (commut_lift_subst_rec _ _ (ind_npars mdecl) (i + #|ind_params mdecl|) 
        (i + #|ind_params mdecl|)) as hs.
      rewrite parslen. erewrite <-hs. 2:lia.
      rewrite lift_closed; auto.
      apply (closedn_subst _ 0). 
      unfold indsubst.
      eapply (declared_minductive_closed_inds _ {| inductive_mind := mind; 
                            inductive_ind := ind |}). 
      2:destruct isdecl as [[] ?]; eauto. auto.
      simpl. eapply subject_closed in Hs.
      now rewrite /indsubst inds_length. auto. }
    split.
    unfold projection_type in H0.
    rewrite H0. exists s; auto.
    exists arg. intuition auto.

    apply wf_local_smash_end; auto.

    unfold projsubst. clear Hs.
    clear -wfΣ parslen onps projslen some_proj IH Hp2 decli.
    rewrite (smash_context_lift []).
    rewrite (smash_context_subst []).
    rewrite -(firstn_skipn (S idx) (smash_context [] (cshape_args c))).
    rewrite subst_context_app lift_context_app subst_context_app.
    autorewrite with len.
    rewrite skipn_all_app_eq.
    autorewrite with len.
    rewrite firstn_length_le; auto. rewrite smash_context_length.
    simpl. lia.
    induction i. subst idx.
    - assert (S (context_assumptions (cshape_args c) - 1) =
       (context_assumptions (cshape_args c))) as -> by lia.
      rewrite skipn_all2.
      autorewrite with len; simpl; auto.
      constructor.
    - forward IHi.
      intros. eapply (IH i0). lia. auto. 
      forward IHi by lia. simpl in IHi.
      subst idx.
      destruct (skipn (S (context_assumptions (cshape_args c) - S (S i))) 
        (smash_context [] (cshape_args c))) eqn:eqargs.
      apply (f_equal (@length _)) in eqargs.
      autorewrite with len in eqargs.
      rewrite skipn_length in eqargs. autorewrite with len. simpl; lia.
      autorewrite with len in eqargs. simpl in eqargs. lia.
      rewrite subst_context_snoc lift_context_snoc subst_context_snoc.
      simpl.
      destruct c0 as [? [] ?].
      * simpl in eqargs.
        pose proof (@smash_context_assumption_context [] (cshape_args c)).
        forward H by constructor.
        eapply assumption_context_skipn in H.
        rewrite -> eqargs in H. elimtype False; inv H.
      * apply skipn_eq_cons in eqargs as [Hnth eqargs].
        constructor.
        + replace (S (S (context_assumptions (cshape_args c) - S (S i)))) 
            with (S (context_assumptions (cshape_args c) - S i)) in eqargs by lia.
          rewrite eqargs in IHi. apply IHi.
        + set substdecl := (subst
             (inds (inductive_mind ind) u (ind_bodies mdecl)) (S (ind_npars mdecl))
            (subst (projs ind (ind_npars mdecl) i) 0
              (lift 1 i decl_type))).
          specialize (IH i ltac:(lia)).
          autorewrite with len.
          eapply (f_equal (@length _)) in eqargs.
          rewrite skipn_length in eqargs.
          autorewrite with len. simpl; lia.
          autorewrite with len in eqargs. simpl in eqargs.
          eapply nth_error_alli in onps; eauto. simpl in onps.
          destruct onps as [pdecl Hnth'].
          replace ((context_assumptions (cshape_args c) - 
            S (S (context_assumptions (cshape_args c) - S (S i)))))
            with i in eqargs, Hnth' by lia. rewrite -eqargs.
          rewrite /lift_decl /subst_decl. simpl.
          autorewrite with len.
          epose proof (commut_lift_subst_rec _ _ 1 (i + #|ind_params mdecl|) i).
          erewrite H. 2:lia. clear H.
          specialize (IH _ Hnth').

          eapply meta_conv. econstructor.
          split; eauto. simpl.
          eapply meta_conv. econstructor.
          destruct IH as [[s isTy] _].
          now eapply typing_wf_local in isTy.
          simpl. reflexivity. simpl.
          rewrite lift_mkApps. simpl. destruct ind; simpl.
          reflexivity. autorewrite with len.
          simpl. 
          rewrite context_assumptions_smash_context /= //.
          assert(subst_instance_constr u pdecl.2 = pdecl.2) as ->.
          { eapply isType_subst_instance_id. apply IH. }
          destruct IH as [isTy [decl [[[nthdecl _] eqpdecl] ptyeq]]].
          move ptyeq at bottom. 
          replace  (S (context_assumptions (cshape_args c) - S (S i))) with 
           (context_assumptions (cshape_args c) - S i) in Hnth by lia.
          rewrite nthdecl in Hnth. noconf Hnth. simpl in ptyeq.
          rewrite -eqpdecl. simpl.
          rewrite ptyeq. unfold projection_type'.
          fold indsubst. destruct ind as [mind ind]; simpl in *.
          set (projsubst := projs {| inductive_mind := mind; inductive_ind := ind |} (ind_npars mdecl) i) in *.
          rewrite -eqpdecl in isTy.
          eapply isType_closed in isTy.
          simpl in isTy. autorewrite with len in isTy. simpl in isTy.
          rewrite ptyeq in isTy.
          unfold projection_type' in isTy.
          epose proof (commut_lift_subst_rec _ _ 1 (i + #|ind_params mdecl|) i).
          erewrite H in isTy by lia.
          rewrite H; try lia.
          rewrite (subst_id _ (({|
            decl_name := nAnon;
            decl_body := None;
            decl_type := mkApps
                          (tInd
                              {| inductive_mind := mind; inductive_ind := ind |}
                              u)
                          (to_extended_list
                              (smash_context [] (ind_params mdecl))) |}
            :: smash_context [] (ind_params mdecl)))).
          ++ simpl. autorewrite with len.
            rewrite context_assumptions_smash_context //.                            
          ++ constructor. apply smash_context_assumption_context; constructor.
          ++ unfold to_extended_list, to_extended_list_k.  simpl.
            rewrite -reln_lift /= (reln_acc [_]) rev_app_distr /= //.
          ++ now rewrite (Nat.add_1_r i).
          ++ simpl. auto.
  Qed.

  Lemma declared_projection_type {Σ : global_env_ext} {mdecl idecl p pdecl} : 
    wf Σ.1 ->
    declared_projection Σ mdecl idecl p pdecl ->
    let u := PCUICLookup.abstract_instance (ind_universes mdecl) in    
    isType (Σ.1, ind_universes mdecl)
      ((vass nAnon (mkApps (tInd p.1.1 u) 
            (to_extended_list (smash_context [] (ind_params mdecl)))))::
         smash_context [] (ind_params mdecl)) pdecl.2.
  Proof.
    intros wfΣ declp.
    destruct (on_declared_projection wfΣ declp) as [oni onp].
    specialize (declared_projections wfΣ (let (x, _) := declp in x)).
    set(oib := declared_inductive_inv _ _ _ _) in *.
    intros onprojs u.
    clearbody oib.
    simpl in *.
    destruct (ind_cshapes oib) as [|? []]; try contradiction.
    forward onprojs. intuition auto.
    destruct declp as [decli [Hnth Hpars]].
    eapply nth_error_alli in onprojs; eauto.
    simpl in onprojs. intuition auto.
  Qed.

  Lemma declared_projection_type_and_eq {Σ : global_env_ext} {mdecl idecl p pdecl} : 
     forall (wfΣ : wf Σ.1) (Hdecl : declared_projection Σ mdecl idecl p pdecl),
     let u := PCUICLookup.abstract_instance (ind_universes mdecl) in
     let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in x) in
     let u := PCUICLookup.abstract_instance (ind_universes mdecl) in
     match ind_cshapes oib return Type with
     | [cs] => 
       isType (Σ.1, ind_universes mdecl)
         ((vass nAnon (mkApps (tInd p.1.1 u) 
               (to_extended_list (smash_context [] (ind_params mdecl)))))::
            smash_context [] (ind_params mdecl)) pdecl.2 *
        ∑ decl, 
        (nth_error (smash_context [] (cshape_args cs)) 
          (context_assumptions (cshape_args cs) - S p.2) = Some decl) *
        (wf_local (Σ.1, ind_universes mdecl) 
            (arities_context (ind_bodies mdecl) ,,, 
              ind_params mdecl ,,, smash_context [] (cshape_args cs))) *
        (projection_type mdecl p.1.1 p.2 decl.(decl_type) = pdecl.2) *
        (projection_type mdecl p.1.1 p.2 decl.(decl_type) = 
          projection_type' mdecl p.1.1 p.2 decl.(decl_type))%type
    | _ => False
     end.
   Proof.
     intros wfΣ declp.
     destruct (on_declared_projection wfΣ declp) as [oni onp].
     specialize (declared_projections wfΣ (let (x, _) := declp in x)).
     set(oib := declared_inductive_inv _ _ _ _) in *.
     intros onprojs u.
     clearbody oib.
     simpl in *.
     destruct (ind_cshapes oib) as [|? []]; try contradiction.
     forward onprojs. intuition auto.
     destruct declp as [decli [Hnth Hpars]].
     eapply nth_error_alli in onprojs; eauto.
     simpl in onprojs. intuition auto.
   Qed.

  Lemma subst_instance_subst_context u s k Γ : 
    subst_instance_context u (subst_context s k Γ) =
    subst_context (map (subst_instance_constr u) s) k (subst_instance_context u Γ).
  Proof.
    rewrite /subst_instance_context /map_context !subst_context_alt.
    rewrite map_mapi mapi_map. apply mapi_rec_ext.
    intros. rewrite /subst_decl !PCUICAstUtils.compose_map_decl.
    apply PCUICAstUtils.map_decl_ext => ?.
    rewrite map_length. now rewrite subst_subst_instance_constr.
  Qed.

  Lemma subst_instance_context_smash u Γ Δ : 
    subst_instance_context u (smash_context Δ Γ) = 
    smash_context (subst_instance_context u Δ) (subst_instance_context u Γ).
  Proof.
    induction Γ as [|[? [] ?] ?] in Δ |- *; simpl; auto.
    - rewrite IHΓ. f_equal.
      now rewrite subst_instance_subst_context.
    - rewrite IHΓ subst_instance_context_app /= //.
  Qed.

  Lemma map_inst_idsn l l' n :
    #|l| = n ->
    map (inst (l ⋅n l')) (idsn n) = l.
  Proof.
    induction n in l, l' |- *.
    - destruct l => //.
    - destruct l as [|l a] using rev_case => // /=.
      rewrite app_length /= Nat.add_1_r => [=].
      intros; subst n.
      simpl. rewrite map_app.
      f_equal. rewrite subst_consn_app.
      now apply IHn.
      simpl.
      destruct (subst_consn_lt #|l| (l ++ [a]) l') as [a' [hnth heq]].
      rewrite app_length. simpl; lia.
      rewrite heq. rewrite nth_error_app_ge in hnth; auto.
      rewrite Nat.sub_diag in hnth. simpl in hnth. congruence.
  Qed.
  
  Lemma context_subst_extended_subst Γ args s : 
    context_subst Γ args s ->
    s = map (inst (List.rev args ⋅n ids)) (extended_subst Γ 0).
  Proof.
    induction 1.
    - simpl; auto.
    - simpl.
      rewrite lift_extended_subst.
      rewrite map_map_compose.
      rewrite List.rev_app_distr. simpl. f_equal.
      rewrite IHX. apply map_ext.
      intros. autorewrite with sigma.
      apply inst_ext.
      rewrite subst_consn_subst_cons.
      now rewrite subst_cons_shift.
    - simpl.
      f_equal; auto.
      rewrite IHX.
      autorewrite with sigma.
      apply inst_ext.
      rewrite ren_lift_renaming. autorewrite with len.
      rewrite subst_consn_compose.
      autorewrite with sigma.
      unfold Upn.
      rewrite subst_consn_compose.
      apply subst_consn_proper; first last.
      rewrite -subst_consn_app.
      rewrite shiftk_compose.
      rewrite subst_consn_shiftn //.
      autorewrite with len. now rewrite (context_subst_length2 X).
      rewrite map_inst_idsn //. now autorewrite with len.
  Qed.

  Lemma spine_subst_smash {Σ Γ inst s Δ} : 
    wf Σ.1 ->
    spine_subst Σ Γ inst s Δ ->
    spine_subst Σ Γ inst (List.rev inst) (smash_context [] Δ).
  Proof.
    intros wfΣ [].
    assert (context_subst (smash_context [] Δ) inst (List.rev inst)).
    { apply closed_wf_local in spine_dom_wf.
      clear -inst_ctx_subst spine_dom_wf. induction inst_ctx_subst.
      constructor. rewrite List.rev_app_distr /=.
      rewrite smash_context_acc. simpl.
      constructor. auto.
      simpl. rewrite smash_context_acc. simpl. auto.
      auto. }
    split; auto.
    - eapply All_local_env_app_inv; split; auto.
      eapply wf_local_rel_smash_context; auto.
    - induction inst_subslet in inst, inst_ctx_subst, spine_codom_wf |- *.
      depelim inst_ctx_subst.
      + constructor.
      + depelim inst_ctx_subst; simpl in H; noconf H.
        simpl. rewrite smash_context_acc.
        simpl. rewrite List.rev_app_distr.
        depelim spine_codom_wf; simpl in H; noconf H.
        constructor. now apply IHinst_subslet.
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
            now apply context_subst_length2 in inst_ctx_subst. }
        clear -inst_ctx_subst.
        rewrite subst_consn_compose.
        rewrite map_inst_idsn. now autorewrite with len.
        now apply context_subst_extended_subst.
      + simpl. rewrite smash_context_acc.
        simpl. depelim spine_codom_wf; simpl in H; noconf H.
        depelim inst_ctx_subst; simpl in H; noconf H; simpl in H0; noconf H0.
        apply IHinst_subslet; auto.
  Qed.

  Lemma subst_instance_instance_id u mdecl : 
    subst_instance_instance u (PCUICLookup.abstract_instance (ind_universes mdecl)) = u.
  Proof.
    todo "universes"%string.
  Qed.

  Theorem validity :
    env_prop (fun Σ Γ t T => isWfArity_or_Type Σ Γ T)
      (fun Σ Γ wfΓ =>
      All_local_env_over typing
      (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ) 
         (t T : term) (_ : Σ;;; Γ |- t : T) => isWfArity_or_Type Σ Γ T) Σ Γ
      wfΓ).
  Proof.
    apply typing_ind_env; intros; rename_all_hyps.

    - auto.

    - destruct (nth_error_All_local_env_over heq_nth_error X) as [HΓ' Hd].
      destruct decl as [na [b|] ty]; cbn -[skipn] in *.
      + destruct Hd as [Hd _].
        eapply isWfArity_or_Type_lift; eauto. clear HΓ'. 
        now apply nth_error_Some_length in heq_nth_error.
      + destruct lookup_wf_local_decl; cbn -[skipn] in *.
        destruct o. right. exists x0. simpl in Hd.
        rewrite <- (firstn_skipn (S n) Γ).
        assert (S n = #|firstn (S n) Γ|).
        { apply nth_error_Some_length in heq_nth_error. rewrite firstn_length_le; auto with arith. }
        rewrite {3}H.
        apply (weakening Σ (skipn (S n) Γ) (firstn (S n) Γ) ty (tSort x0)); eauto with wf.
        unfold app_context. now rewrite (firstn_skipn (S n) Γ).

    - (* Universe *) left. exists [], (Universe.super l). split; auto.
    - (* Product *) left. eexists [], _. split; eauto. simpl. reflexivity.
    - (* Lambda *)
      destruct X3.
      + left. destruct i as [ctx [s [Heq Hs]]].
        red. simpl. pose proof (PCUICClosed.destArity_spec [] bty).
        rewrite Heq in H. simpl in H. subst bty. clear Heq.
        eexists _, s. split; auto.
        * rewrite destArity_it_mkProd_or_LetIn. simpl. reflexivity.
        * apply All_local_env_app_inv; split; auto.
          apply All_local_env_app_inv; split; auto.
          -- repeat constructor.
             simpl.
             exists s1; easy.
          -- apply All_local_env_app in Hs. unfold snoc.
             intuition auto. clear -b0.
             induction b0; constructor; eauto.
             ++ destruct t1 as [u Hu]. exists u.
                rewrite app_context_assoc. apply Hu.
             ++ simpl in t1 |- *.
                rewrite app_context_assoc. apply t1.
             ++ simpl in t2.
                rewrite app_context_assoc. apply t2.
      + destruct i as [u Hu].
        right. exists (Universe.sort_of_product s1 u); constructor; auto.

    - (* Let *)
      destruct X5.
      + left. destruct i as [ctx [s [Heq Hs]]].
        eexists _, s.
        simpl. split; auto.
        pose proof (PCUICClosed.destArity_spec [] b'_ty).
        rewrite Heq in H. simpl in H. subst b'_ty.
        rewrite destArity_it_mkProd_or_LetIn. simpl.
        reflexivity. rewrite app_context_assoc. simpl.
        apply All_local_env_app_inv; split; eauto with wf.
        apply All_local_env_app in Hs as [Hp Hs].
        apply Hs.
      + right.
        destruct i as [u Hu]. exists u.
        econstructor.
        eapply type_LetIn; eauto. left. exists [], u; intuition eauto with wf.
        eapply cumul_alt. exists (tSort u), (tSort u); intuition auto.
        apply red1_red; repeat constructor.
        reflexivity.

    - (* Application *)
      destruct X1 as [[ctx [s [Heq Hs]]]|].
      simpl in Heq. pose proof (PCUICClosed.destArity_spec ([],, vass na A) B).
      rewrite Heq in H.
      simpl in H. unfold mkProd_or_LetIn in H. simpl in H.
      destruct ctx using rev_ind; noconf H.
      simpl in H. rewrite it_mkProd_or_LetIn_app in H. simpl in H.
      destruct x as [na' [b|] ty]; noconf H.
      left. eexists _, s. split.
      unfold subst1. rewrite subst_it_mkProd_or_LetIn.
      rewrite destArity_it_mkProd_or_LetIn. simpl. reflexivity.
      rewrite app_context_nil_l. apply All_local_env_app_inv; intuition auto.
      apply All_local_env_app in Hs as [wf'Γ wfctx].
      apply All_local_env_app in wfctx as [wfd wfctx].
      eapply All_local_env_subst; eauto. simpl; intros.
      destruct T; simpl in *.
      + rewrite Nat.add_0_r. eapply substitution; eauto. constructor. constructor.
        2: simpl; eauto; now rewrite app_context_assoc in X0.
        now rewrite subst_empty.
      + rewrite Nat.add_0_r. destruct X0 as [u' Hu']. exists u'.
        eapply (substitution _ _ _ _ _ _ (tSort u')); eauto. constructor. constructor.
        2: simpl; eauto; now rewrite app_context_assoc in Hu'.
        now rewrite subst_empty.
      + right.
        destruct i as [u' Hu']. exists u'.
        eapply (substitution0 _ _ na _ _ _ (tSort u')); eauto.
        apply inversion_Prod in Hu' as [na' [s1 [s2 Hs]]]; tas. intuition.
        eapply type_Cumul; pcuic.
        eapply (weakening_cumul Σ Γ [] [vass na A]) in b; pcuic.
        simpl in b. eapply cumul_trans. auto. 2:eauto.
        constructor. constructor. simpl. apply leq_universe_product.

    - destruct decl as [ty [b|] univs]; simpl in *.
      * eapply declared_constant_inv in X; eauto.
        red in X. simpl in X.
        eapply isWAT_weaken; eauto.
        eapply (isWAT_subst_instance_decl (Γ:=[])); eauto.
        apply weaken_env_prop_isWAT.
      * eapply isWAT_weaken; eauto.
        have ond := on_declared_constant _ _ _ wf H.
        do 2 red in ond. simpl in ond.
        eapply (isWAT_subst_instance_decl (Γ:=[])); eauto.
        right. simpl. apply ond.

    - (* Inductive type *)
      destruct (on_declared_inductive wf isdecl); pcuic.
      destruct isdecl.
      apply onArity in o0.
      eapply isWAT_weaken; eauto.
      eapply (isWAT_subst_instance_decl (Γ:=[])); eauto.
      right; simpl; apply o0.

    - (* Constant type *)
      destruct (on_declared_constructor wf isdecl) as [[oni oib] [cs [declc onc]]].
      unfold type_of_constructor.
      right. have ctype := on_ctype onc.
      destruct ctype as [s' Hs].
      exists (subst_instance_univ u s').
      eapply instantiate_minductive in Hs; eauto.
      2:(destruct isdecl as [[] ?]; eauto).
      simpl in Hs.
      eapply (weaken_ctx (Γ:=[]) Γ); eauto.
      eapply (substitution _ [] _ (inds _ _ _) [] _ (tSort _)); eauto.
      eapply subslet_inds; eauto. destruct isdecl; eauto.
      now rewrite app_context_nil_l.

    - (* Case predicate application *)
      right. red.
      eapply (isWAT_mkApps_Ind wf isdecl) in X4 as [parsubst [argsubst Hind]]; auto.
      destruct (on_declared_inductive wf isdecl) as [onmind oib]. simpl in Hind.
      destruct Hind as [[sparsubst sargsubst] cu].
      subst npar.
      eapply (build_case_predicate_type_spec _ _ _ _ _ _ _ _ oib) in heq_build_case_predicate_type as
        [pars [cs eqty]].
      exists ps.
      eapply type_mkApps; eauto.
      eapply wf_arity_spine_typing_spine; auto.
      split; auto.
      rewrite eqty. clear typep eqty X2.
      eapply arity_spine_it_mkProd_or_LetIn; auto.
      pose proof (context_subst_fun cs sparsubst). subst pars.
      eapply sargsubst.
      simpl. constructor; first last.
      constructor; auto. left; eexists _, _; intuition eauto.
      reflexivity.
      rewrite subst_mkApps.
      simpl.
      rewrite map_app. subst params.
      rewrite map_map_compose. rewrite map_subst_lift_id_eq.
      rewrite (subslet_length sargsubst). now autorewrite with len.
      unfold to_extended_list.
      eapply spine_subst_subst_to_extended_list_k in sargsubst.
      rewrite to_extended_list_k_subst
         PCUICSubstitution.map_subst_instance_constr_to_extended_list_k in sargsubst.
      rewrite sargsubst firstn_skipn. eauto.

    - (* Proj *)
      right.
      pose proof isdecl as isdecl'.
      eapply declared_projection_type in isdecl'; eauto.
      subst ty.
      destruct isdecl' as [s Hs].
      unshelve eapply isWAT_mkApps_Ind in X2 as [parsubst [argsubst [[sppar sparg] cu]]]; eauto.
      eapply isdecl.p1.
      eapply (typing_subst_instance_decl _ _ _ _ _ _ _ wf isdecl.p1.p1) in Hs; eauto.
      simpl in Hs.
      exists (subst_instance_univ u s).
      unfold PCUICTypingDef.typing in *.
      eapply (weaken_ctx Γ) in Hs; eauto.
      rewrite -heq_length in sppar. rewrite firstn_all in sppar.
      rewrite subst_instance_context_smash in Hs. simpl in Hs.
      eapply spine_subst_smash in sppar => //.
      eapply (substitution _ Γ _ _ [_] _ _ wf sppar) in Hs.
      simpl in Hs.
      eapply (substitution _ Γ [_] [c] [] _ _ wf) in Hs.
      simpl in Hs. rewrite (subst_app_simpl [_]) /= //.
      constructor. constructor.
      simpl. rewrite subst_empty.
      rewrite subst_instance_constr_mkApps subst_mkApps /=.
      rewrite subst_instance_instance_id.
      rewrite subst_instance_to_extended_list.
      rewrite subst_instance_context_smash.
      rewrite (spine_subst_subst_to_extended_list_k sppar).
      assumption.
      
    - (* Fix *)
      eapply nth_error_all in X0; eauto.
      firstorder auto.
    
    - (* CoFix *)
      eapply nth_error_all in X0; eauto.
      firstorder auto.

    - (* Conv *)
      destruct X2. red in i. left. exact (projT1 i).
      right. destruct s as [u [Hu _]]. now exists u.
  Qed.

End Validity.

Lemma validity_term {cf:checker_flags} {Σ Γ t T} :
  wf Σ.1 -> Σ ;;; Γ |- t : T -> isWfArity_or_Type Σ Γ T.
Proof.
  intros. eapply validity; try eassumption.
Defined.

(* This corollary relies strongly on validity.
   It should be used instead of the weaker [invert_type_mkApps],
   which is only used as a stepping stone to validity.
 *)
Lemma inversion_mkApps :
  forall `{checker_flags} {Σ Γ t l T},
    wf Σ.1 ->
    Σ ;;; Γ |- mkApps t l : T ->
    ∑ A, Σ ;;; Γ |- t : A × typing_spine Σ Γ A l T.
Proof.
  intros cf Σ Γ f u T wfΣ; induction u in f, T |- *. simpl. intros.
  { exists T. intuition pcuic. constructor. eapply validity; auto with pcuic.
    eauto. eapply cumul_refl'. }
  intros Hf. simpl in Hf.
  destruct u. simpl in Hf.
  - pose proof (env_prop_typing _ _  validity _ wfΣ _ _ _ Hf). simpl in X.
     eapply inversion_App in Hf as [na' [A' [B' [Hf' [Ha HA''']]]]].
    eexists _; intuition eauto.
    econstructor; eauto with pcuic. eapply validity; eauto with wf pcuic.
    constructor. all:eauto with pcuic.
  - specialize (IHu (tApp f a) T).
    specialize (IHu Hf) as [T' [H' H'']].
    eapply inversion_App in H' as [na' [A' [B' [Hf' [Ha HA''']]]]]. 2:{ eassumption. }
    exists (tProd na' A' B'). intuition; eauto.
    econstructor. eapply validity; eauto with wf.
    eapply cumul_refl'. auto.
    clear -H'' HA''' wfΣ. depind H''.
    econstructor; eauto. eapply cumul_trans; eauto.  
Qed.
