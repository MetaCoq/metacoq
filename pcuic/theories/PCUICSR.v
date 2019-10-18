(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

Require Import Equations.Prop.DepElim.
From Coq Require Import Bool List Program Lia Arith.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality
     PCUICValidity PCUICConfluence
     PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICPrincipality PCUICContexts PCUICArities
     PCUICParallelReduction. 

Require Import ssreflect.
Set Asymmetric Patterns.
Set SimplIsCbn.

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

Derive Signature for typing_spine.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

(* Commented otherwise extraction would produce an axiom making the whole
   extracted code unusable *)

Arguments Universe.sort_of_product : simpl nomatch.

Lemma mkApps_inj f a f' l :
  tApp f a = mkApps f' l -> l <> [] ->
  f = mkApps f' (removelast l) /\ (a = last l a).
Proof.
  induction l in f' |- *; simpl; intros H. noconf H. intros Hf. congruence.
  intros . destruct l; simpl in *. now noconf H.
  specialize (IHl _ H). forward IHl by congruence.
  apply IHl.
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
      * cbn. now rewrite destArity_app H1.
      * now rewrite app_context_assoc.
    + right. destruct HA as [sA HA], HB as [sB HB].
      eexists. econstructor; eassumption.
Defined.

Lemma type_tFix_inv {cf:checker_flags} (Σ : global_env_ext) Γ mfix idx T : wf Σ ->
  Σ ;;; Γ |- tFix mfix idx : T ->
  { T' & { rarg & {f & (unfold_fix mfix idx = Some (rarg, f)) * (Σ ;;; Γ |- f : T') * (Σ ;;; Γ |- T' <= T) }}}%type.
Proof.
  intros wfΣ H. depind H.
  - unfold unfold_fix. rewrite e.
    specialize (nth_error_all e a0) as [Hty ->].
    destruct decl as [name ty body rarg]; simpl in *.
    clear e.
    eexists _, _, _. split.
    + split.
      * eauto.
      * eapply (substitution _ _ types _ [] _ _ wfΣ); simpl; eauto with wf.
        -- subst types. rename i into hguard. clear -a a0 hguard.
           pose proof a0 as a0'. apply All_rev in a0'.
           unfold fix_subst, fix_context. simpl.
           revert a0'. rewrite <- (@List.rev_length _ mfix).
           rewrite rev_mapi. unfold mapi.
           assert (#|mfix| >= #|List.rev mfix|) by (rewrite List.rev_length; lia).
           assert (He :0 = #|mfix| - #|List.rev mfix|) by (rewrite List.rev_length; auto with arith).
           rewrite {3}He. clear He. revert H.
           assert (forall i, i < #|List.rev mfix| -> nth_error (List.rev mfix) i = nth_error mfix (#|List.rev mfix| - S i)).
           { intros. rewrite nth_error_rev. 1: auto.
             now rewrite List.rev_length List.rev_involutive. }
           revert H.
           generalize (List.rev mfix).
           intros l Hi Hlen H.
           induction H.
           ++ simpl. constructor.
           ++ simpl. constructor.
              ** unfold mapi in IHAll.
                 simpl in Hlen. replace (S (#|mfix| - S #|l|)) with (#|mfix| - #|l|) by lia.
                 apply IHAll.
                 --- intros. simpl in Hi. specialize (Hi (S i)). apply Hi. lia.
                 --- lia.
              ** clear IHAll. destruct p.
                 simpl in Hlen. assert ((Nat.pred #|mfix| - (#|mfix| - S #|l|)) = #|l|) by lia.
                 rewrite H0. rewrite simpl_subst_k.
                 --- clear. induction l; simpl; auto with arith.
                 --- eapply type_Fix; auto.
                     simpl in Hi. specialize (Hi 0). forward Hi.
                     +++ lia.
                     +++ simpl in Hi.
                         rewrite Hi. f_equal. lia.
    + subst types. rewrite simpl_subst_k.
      * now rewrite fix_context_length fix_subst_length.
      * reflexivity.
  - destruct (IHtyping wfΣ) as [T' [rarg [f [[unf fty] Hcumul]]]].
    exists T', rarg, f. intuition auto.
    + eapply cumul_trans; eauto.
    + destruct b. eapply cumul_trans; eauto.
Qed.

Arguments subst_context !s _ !Γ.
Arguments it_mkProd_or_LetIn !l _.


Lemma build_case_predicate_type_spec {cf:checker_flags} Σ ind mdecl idecl pars u ps pty :
  forall (o : on_ind_body (lift_typing typing) Σ (inductive_mind ind) mdecl (inductive_ind ind) idecl),
  build_case_predicate_type ind mdecl idecl pars u ps = Some pty ->
  ∑ parsubst, (context_subst (subst_instance_context u (ind_params mdecl)) pars parsubst *
  (pty = it_mkProd_or_LetIn (subst_context parsubst 0 (subst_instance_context u o.(ind_indices))) 
      (tProd (nNamed (ind_name idecl))
          (mkApps (tInd ind u) (map (lift0 #|o.(ind_indices)|) pars ++ to_extended_list o.(ind_indices))) 
          (tSort ps)))).
Proof.
  intros []. unfold build_case_predicate_type.
  destruct instantiate_params eqn:Heq=> //.
  eapply instantiate_params_make_context_subst in Heq =>  /=.
  destruct destArity eqn:Har => //.
  move=> [=] <-. destruct Heq as [ctx'  [ty'' [s' [? [? ?]]]]].
  subst t. exists s'. split. apply make_context_subst_spec in H0.
  now rewrite List.rev_involutive in H0.
  clear onProjections. clear onConstructors.
  assert (p.1 = subst_context s' 0 (subst_instance_context u ind_indices)) as ->.
  move: H. rewrite ind_arity_eq subst_instance_constr_it_mkProd_or_LetIn.
  rewrite decompose_prod_n_assum_it_mkProd app_nil_r => [=].
  move=> Hctx' Hty'.
  subst ty''  ctx'.
  move: Har. rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
  rewrite destArity_it_mkProd_or_LetIn. simpl. move=> [=] <- /=. 
  now rewrite app_context_nil_l.
  f_equal. rewrite subst_context_length subst_instance_context_length.
  simpl.
  f_equal. f_equal.  f_equal.
  unfold to_extended_list.
  rewrite to_extended_list_k_subst PCUICSubstitution.map_subst_instance_constr_to_extended_list_k.
  reflexivity.
Qed.

(*
  Lemma type_Case_valid_btys {cf:checker_flags} Σ Γ ind u npar p c args :
    forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    wf Σ.1 ->
    mdecl.(ind_npars) = npar ->
    let params := List.firstn npar args in
    forall ps pty, build_case_predicate_type ind mdecl idecl params u ps =
                Some pty ->                
    Σ ;;; Γ |- p : pty ->
    existsb (leb_sort_family (universe_family ps)) (ind_kelim idecl) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    forall btys, map_option_out (build_branches_type ind mdecl idecl params u p) =
                Some btys ->
    All (fun br => Σ ;;; Γ |- br.2 : tSort ps) btys.
Proof.
  intros mdecl idecl isdecl wfΣ H0 pars ps pty X typ Hps tyc btys brtys.
  unfold build_case_predicate_type in X.
  destruct instantiate_params eqn:Heq; [|simpl; discriminate].
  simpl monad_utils.bind in X.
  pose proof isdecl as isdecl'.
  apply PCUICWeakeningEnv.on_declared_inductive in isdecl' as [oind oc]; auto.
  rewrite oc.(ind_arity_eq) in Heq.
  pose proof (PCUICClosed.destArity_spec [] t) as Hpty.
  move: X Hpty. destruct destArity eqn:da => // [=] Hpty. subst pty.


  unfold build_branches_type in H2.
  eapply map_option_out_All; tea. clear H2.
  apply All_mapi.
  pose proof oc.(onConstructors) as oc'.
  eapply Alli_impl. eapply All2_All_left_pack. tea. cbn.
  intros n [[id ct] k] [cs [Hnth [Hct1 Hct2]]]; cbn in *.
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) pars
             ((subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)))
                (subst_instance_constr u ct))); [|simpl; trivial].
  intros ct' Hct'. 
  case_eq (decompose_prod_assum [] ct'); intros sign ccl e1.
  case_eq (chop (ind_npars mdecl) (decompose_app ccl).2);
  intros paramrels args0 e2; cbn.
  destruct Hct2 as [cs' Hcs'].
  destruct cs'. simpl in *. subst ct.
  eapply instantiate_params_make_context_subst in Hct'.
  destruct Hct' as [ctx' [ty'' [parinst Hct']]].
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in Hct'.
  rewrite !subst_it_mkProd_or_LetIn in Hct'.
  rewrite -(subst_context_length  (inds (inductive_mind ind) u
     (ind_bodies mdecl)) 0) in Hct'.
  rewrite decompose_prod_n_assum_it_mkProd app_nil_r in Hct'.
  destruct Hct' as [[= eqs eqs'] [eqpars ->]].
  subst ctx' ty''.
  rewrite !subst_it_mkProd_or_LetIn in e1.
  eapply inversion_Ind_app in cty as [inds [Hsp [argapp [indannot Hu]]]]; eauto.
  rewrite decompose_prod_assum_it_mkProd in e1.
  rewrite !subst_context_length !subst_instance_context_length !Nat.add_0_r.
  rewrite subst_cstr_concl_head.
   intuition auto. 
  rewrite subst_mkApps. simpl. apply is_ind_app_head_mkApps.
  noconf e1. simpl in e2. 
  rewrite !subst_context_length app_nil_r !subst_instance_context_length.
  rewrite !subst_context_length.
  rewrite Nat.add_0_r !subst_context_length !subst_instance_context_length in e2.
  rewrite subst_instance_constr_mkApps !subst_mkApps /cshape_concl_head in e2.
  rewrite decompose_app_mkApps in e2.
  rewrite !Nat.add_0_r.
  rewrite subst_inds_concl_head. auto. simpl. trivial.
  simpl in e2. 
  rewrite !map_map_compose in e2.
  apply make_context_subst_spec in eqpars.
  rewrite List.rev_involutive in eqpars.
  assert(type_local_ctx (lift_typing typing) Σ Γ
  (subst_context parinst 0
     (subst_context
        (PCUICTyping.inds (inductive_mind ind) u (ind_bodies mdecl))
        (#|ind_params mdecl| + 0) (subst_instance_context u cshape_args)))
  (subst_instance_univ u cs)).
  { eapply typing_wf_local in X.
    destruct oc.
    clear -X Hu eqpars isdecl wfΣ Hcs' ind_sorts.
    eapply type_local_ctx_instantiate in Hcs'; eauto.
    2:{ eapply isdecl. }
    rewrite PCUICUnivSubstitution.subst_instance_context_app in Hcs'.
    eapply weaken_type_local_ctx in Hcs'. 3:eapply X. all:auto.
    eapply subst_type_local_ctx in Hcs'. all:auto.
    revert Hcs'. instantiate (1:= (parinst ++ (inds (inductive_mind ind) u (ind_bodies mdecl)))%list).
    rewrite subst_app_context.
    rewrite Nat.add_0_r. assert (#|parinst| = #|ind_params mdecl|).
    eapply context_subst_length in eqpars. now rewrite subst_instance_context_length in eqpars.
    now rewrite H.
    clear -wfΣ X isdecl Hu.
    pose proof isdecl as [declm _].
    eapply on_declared_inductive in isdecl as [onm oni]; auto.
    destruct onm.
    eapply (weaken_wf_local Γ); auto.
    pose proof (wf_arities_context _ _ _ wfΣ declm).
    eapply weaken_wf_local; auto.
    eapply wf_local_instantiate; eauto.
    red in onParams.
    eapply wf_local_instantiate; eauto.
    eapply subslet_app. admit.
    eapply (weaken_subslet ), subslet_inds; eauto.
    eapply on_declared_inductive in isdecl as [onm oni]; auto.
    destruct onm. red in onParams.
    eapply closed_wf_local in onParams; auto.
    now rewrite closedn_subst_instance_context. }
  eapply type_Cumul with (tSort (Universe.sort_of_product (subst_instance_univ u cs) ps)).
  eapply type_it_mkProd_or_LetIn; eauto.
  2:{ left. exists [], ps; intuition eauto using typing_wf_local. }
  2:{ repeat constructor. apply eq_universe_leq_universe. admit. }
      (* apply sort_of_product_idem. } *)
  red in oc'.
  rewrite !subst_instance_context_length Nat.add_0_r.
  rewrite map_app in e2.
  rewrite chop_n_app in e2.
  { rewrite !map_length to_extended_list_k_length.
    destruct oind. auto. }
  noconf e2.
  rewrite Nat.add_0_r in X0.
  pose proof (typing_wf_local X).
  eapply type_mkApps. all:eauto.
  red in car.
  assert(Σ ;;; Γ |- p : it_mkProd_or_LetIn ({|
  decl_name := nNamed (ind_name idecl);
  decl_body := None;
  decl_type := mkApps (tInd ind u)
                 (map (lift0 #|indctx|) pars ++ to_extended_list indctx) |}
  :: indctx) (tSort ps)).
  { eapply type_Cumul. eauto. left; eexists _, _; intuition eauto.
    rewrite destArity_it_mkProd_or_LetIn. reflexivity.
    rewrite app_context_nil_l /=. constructor.
  }

  eapply weakening_gen; eauto.
  - now rewrite !subst_context_length !subst_instance_context_length.
  - eapply typing_wf_local in X.
    subst pars.
    eapply type_local_ctx_wf_local in X0; auto.
  - red in car.
    depelim car. depelim e.
    destruct y as [na [b|] ty]; simpl in *. intuition auto.
    destruct e as [_ e]. rewrite /mkProd_or_LetIn /=.
    rewrite lift_it_mkProd_or_LetIn /= Nat.add_0_r.
    eapply typing_spine_it_mkProd_or_LetIn; eauto.
    
                  
    admit.
  

    induction l'. simpl. depelim car. simpl in *.
    destruct cshape_indices. simpl.
    * econstructor. 2:eauto.
      left. eexists _, _; intuition eauto.
      simpl. constructor.
      eapply type_local_ctx_wf_local in X0. apply X0. eauto using typing_wf_local.
      simpl in X. rewrite /mkProd_or_LetIn in X. simpl in X.
      rewrite app_nil_r in e0.
      eapply validity in X as [_ X]; auto.
      eapply isWAT_tProd in X as [dom _]; auto.
      destruct dom as [s'' Hs']. exists s''.
      eapply (weakening_gen _ _ _ _ _ _ #|cshape_args|) in Hs'. simpl in Hs'.
      eapply Hs'. now rewrite !subst_context_length subst_instance_context_length. all:auto.
      now eapply type_local_ctx_wf_local in X0.
      eapply type_mkApps. econstructor; eauto.
      now eapply type_local_ctx_wf_local in X0.
      split. eauto. intuition eauto.
      unfold type_of_constructor. simpl.
      rewrite app_nil_r !subst_instance_constr_it_mkProd_or_LetIn.
      rewrite /subst1 !subst_it_mkProd_or_LetIn !subst_instance_context_length Nat.add_0_r.
      eapply typing_spine_it_mkProd_or_LetIn; eauto.
      pose proof (context_subst_length _ _ _ eqpars).
      rewrite subst_instance_context_length in H. rewrite H.
      rewrite -map_map_compose.
      rewrite subst_instance_to_extended_list_k.
      rewrite -map_map_compose.
      rewrite -to_extended_list_k_map_subst. rewrite subst_instance_context_length; lia.
      rewrite (subst_to_extended_list_k _ _ pars). 
      apply make_context_subst_spec_inv. now rewrite List.rev_involutive.
      eapply make_context_subst_spec_inv.
      instantiate (1 := map (lift0 #|cshape_args|) parinst).
      rewrite List.rev_involutive.
      assert(closed_ctx (subst_instance_context u (ind_params mdecl)) = true).
      { eapply closed_wf_local; eauto.
        eapply (on_minductive_wf_params _ mdecl); intuition eauto.
        eapply isdecl. }
      rewrite closed_ctx_subst //.
      eapply (context_subst_lift _ _ _ #|cshape_args|) in eqpars => //.
      rewrite closed_ctx_lift // in eqpars.
      rewrite subst_it_mkProd_or_LetIn !subst_context_length !subst_instance_context_length !Nat.add_0_r /=.
      eapply typing_spine_weaken_concl. auto.
      eapply typing_spine_it_mkProd_or_LetIn_close; eauto.
      2:{ rewrite to_extended_list_k_length.
          now rewrite !context_assumptions_subst. }
      apply make_context_subst_spec_inv.
      rewrite /to_extended_list !to_extended_list_k_subst.
      rewrite -subst_instance_to_extended_list_k.
      rewrite List.rev_involutive.
      eapply make_context_subst_spec. shelve. shelve.
      assert (#|ind_params mdecl| = #|parinst|).
      { eapply context_subst_length in eqpars. 
        now rewrite subst_instance_context_length in eqpars. }
      rewrite subst_instance_constr_mkApps.
      rewrite !subst_mkApps.
      rewrite subst_cstr_concl_head.
      rewrite -subst_app_simpl'. now rewrite map_length.

      eapply isWAT_it_mkProd_or_LetIn_app.
      instantiate (1:=mapi (fun i x => tRel i) cshape_args).
      rewrite PCUICUnivSubst.map_subst_instance_constr_to_extended_list_k.

      pose (unfold_nat cshape_args).
      rewrite (subst_to_extended_list_k _ _ pars). 
      rewrite -to_extended_list_k_map_subst. rewrite subst_instance_context_length; lia.

      rewrite -map_map_compose.
      rewrite -to_extended_list_k_map_subst. lia. 
      shelve.
      
      rewrite -map_map_compose.

      admit. admit.
      now rewrite map_length context_assumptions_subst subst_instance_context_assumptions
        to_extended_list_k_length.
      rewrite /subst1 /=. constructor.
      left; exists [], ps; intuition auto.
      now apply type_local_ctx_wf_local in X0.
      reflexivity.

Admitted.
*)

(** The subject reduction property of the system: *)

Definition SR_red1 {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u (Hu : red1 Σ Γ t u), Σ ;;; Γ |- u : T.

Hint Resolve conv_ctx_refl : pcuic.

Definition branch_type ind mdecl (idecl : one_inductive_body) params u p i (br : ident * term * nat) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let '(id, t, ar) := br in
  let ty := subst0 inds (subst_instance_constr u t) in
  match instantiate_params (subst_instance_context u mdecl.(ind_params)) params ty with
  | Some ty =>
  let '(sign, ccl) := decompose_prod_assum [] ty in
  let nargs := List.length sign in
  let allargs := snd (decompose_app ccl) in
  let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
  let cstr := tConstruct ind i u in
  let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)])%list in
  Some (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args))
| None => None
end.

Lemma nth_map_option_out {A B} (f : nat -> A -> option B) l l' i t : map_option_out (mapi f l) = Some l' ->
  nth_error l' i = Some t -> 
  (∑ x, (nth_error l i = Some x) * (f i x = Some t)).
Proof.
  unfold mapi.
  rewrite -{3}(Nat.add_0_r i).
  generalize 0.
  induction l in i, l' |- *; intros n; simpl. intros [= <-]. rewrite nth_error_nil; discriminate.
  simpl. destruct (f n a) eqn:Heq => //.
  destruct (map_option_out (mapi_rec f l (S n))) eqn:Heq' => //.
  intros [= <-].
  destruct i; simpl. intros [= ->]. now exists a.
  specialize (IHl _ i _ Heq').
  now rewrite plus_n_Sm.
Qed.

Lemma nth_branches_type ind mdecl idecl args u p i t btys : map_option_out (build_branches_type ind mdecl idecl args u p) = Some btys ->
  nth_error btys i = Some t -> 
  (∑ br, (nth_error idecl.(ind_ctors) i = Some br) *
    (branch_type ind mdecl idecl args u p i br = Some t)).
Proof.
  intros Htys Hnth.
  eapply nth_map_option_out in Htys; eauto.
Qed.

Lemma map_option_out_length {A} (l : list (option A)) l' : map_option_out l = Some l' -> #|l| = #|l'|.
Proof.
  induction l in l' |- * => /=.
  now move=> [=] <-.
  simpl. destruct a; try discriminate.
  destruct map_option_out eqn:Heq; try discriminate.
  move=> [=] <-. by rewrite (IHl l0 eq_refl).
Qed.

Lemma build_branches_type_lookup {cf:checker_flags} Σ Γ ind mdecl idecl cdecl pars u p (brs :  list (nat * term)) btys : 
  declared_inductive Σ.1 mdecl ind idecl ->
  map_option_out (build_branches_type ind mdecl idecl pars u p) = Some btys ->
  All2 (fun br bty => (br.1 = bty.1) * (Σ ;;; Γ |- br.2 : bty.2))%type brs btys ->
  forall c, nth_error (ind_ctors idecl) c = Some cdecl ->
  ∑ nargs br bty, 
    (nth_error brs c = Some (nargs, br)) *
    (nth_error btys c = Some (nargs, bty)) *
    (Σ ;;; Γ |- br : bty) * (branch_type ind mdecl idecl pars u p c cdecl = Some (nargs, bty)).
Proof.
  intros decli Hbrs Hbrtys c Hc.
  destruct decli as [declmi decli].
  pose proof (map_option_out_length _ _ Hbrs) as hlen. 
  rewrite mapi_length in hlen.
  assert (H:∑ t', nth_error btys c = Some t').
  pose proof (All2_length _ _ Hbrtys) as e. eapply nth_error_Some_length in Hc.
  destruct (nth_error_spec btys c). eexists; eauto. elimtype False; lia.
  destruct H as [[argty bty] Hbty].
  assert (H:∑ t', nth_error brs c = Some t').
  pose proof (All2_length _ _ Hbrtys) as e. eapply nth_error_Some_length in Hc.
  destruct (nth_error_spec brs c). eexists; eauto. elimtype False; lia.
  destruct H as [[argbr br] Hbr].
  eapply All2_nth_error in Hbrtys; eauto.
  destruct Hbrtys as [Harg tybr]. simpl in *. subst.
  eapply nth_branches_type in Hbrs; eauto.
  destruct Hbrs as [[[id brty] nargs] [Hnth' Hbrty]].
  exists argty, br, bty.
  intuition auto. rewrite -Hbrty. f_equal.
  congruence.
Qed.

Arguments cshape_indices {mdecl i idecl ctype cargs}.
Import PCUICEnvironment.

From MetaCoq.PCUIC Require Import PCUICCtxShape.

Lemma branch_type_spec {cf:checker_flags} Σ ind mdecl idecl cdecl pars u p c nargs bty : 
  declared_inductive Σ mdecl ind idecl ->
  forall (omib : on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl),
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl),
  forall csort (cs : on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind ind) idecl cdecl csort),
  branch_type ind mdecl idecl pars u p c cdecl = Some (nargs, bty) ->
  forall parsubst, 
  context_subst (subst_instance_context u (PCUICAst.ind_params mdecl)) pars parsubst ->
  let cshape := projT1 cs.2 in
  let indsubst := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  let nargs' := #|cshape.(cshape_args)| in
  let npars := #|ind_params mdecl| in
  let substargs := (subst_context parsubst 0 
    (subst_context indsubst npars (map_context (subst_instance_constr u) cshape.(cshape_args)))) in
  nargs = context_assumptions cshape.(cshape_args) /\
  bty = 
  it_mkProd_or_LetIn substargs
    (mkApps (lift0 nargs' p)
      (map (subst parsubst nargs' ∘ subst indsubst (nargs' + npars) ∘ subst_instance_constr u) cshape.(cshape_indices) ++ 
       [mkApps (tConstruct ind c u)
         (map (lift0 nargs') pars ++         
          to_extended_list substargs)])).
Proof.
  move=> decli onmib [] indices ps aeq onAr indsorts onC _ inds.
  intros cs onc brty parsubst Hpars cshape' indsubst nargs' na.
  assert(lenbodies: inductive_ind ind < #|ind_bodies mdecl|).
  { destruct decli as [_ Hnth]. now apply nth_error_Some_length in Hnth. }
  clear decli.
  destruct onc=> /=.
  destruct s as [cshape _args] => /=. simpl in cshape'. subst cshape'.
  destruct cshape as [args argslen head indi eqdecl] => /=. 
  rewrite eqdecl in o.
  unfold branch_type in brty.
  destruct cdecl as [[id ty] nargs'']. simpl in *.
  destruct instantiate_params eqn:Heq => //.
  eapply instantiate_params_make_context_subst in Heq.
  destruct Heq as [ctx' [ty'' [s' [? [? ?]]]]].
  subst t. move: H.
  rewrite eqdecl subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
  rewrite -(subst_context_length (PCUICTyping.inds (inductive_mind ind) u (ind_bodies mdecl)) 0).
  rewrite decompose_prod_n_assum_it_mkProd.
  move=> H;noconf H.
  move: brty.
  rewrite !subst_context_length !subst_instance_context_length
    subst_instance_constr_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite subst_context_length subst_instance_context_length Nat.add_0_r.
  rewrite subst_instance_constr_mkApps !subst_mkApps.
  rewrite Nat.add_0_r.
  assert((subst s' #|args|
  (subst
     (PCUICTyping.inds (inductive_mind ind) u
        (PCUICAst.ind_bodies mdecl))
     (#|args| + #|PCUICAst.ind_params mdecl|)
     (subst_instance_constr u head))) = tInd ind u).
  rewrite /head. simpl subst_instance_constr.
  erewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| -  S (inductive_ind ind))); try lia.
  2:{ rewrite inds_spec nth_error_rev.
      rewrite List.rev_length mapi_length; try lia.
      rewrite List.rev_involutive List.rev_length mapi_length; try lia.
      rewrite nth_error_mapi. simpl.
      elim: (nth_error_spec _ _). simpl. reflexivity.
      lia. }
  simpl. f_equal. destruct ind as [mind k]=> /=.
  f_equal. simpl in lenbodies. lia.
  rewrite H.
  rewrite decompose_prod_assum_it_mkProd ?is_ind_app_head_mkApps //.
  rewrite decompose_app_mkApps //.
  simpl.
  rewrite !map_map_compose map_app.
  rewrite chop_n_app.
  rewrite map_length to_extended_list_k_length.
  by rewrite (onmib.(onNpars _ _ _ _)).
  move=> [=] Hargs Hbty. subst nargs. split;auto. rewrite -Hbty.
  clear Hbty bty.
  rewrite app_nil_r.
  pose proof (make_context_subst_spec _ _ _ H0) as csubst.
  rewrite rev_involutive in csubst.
  pose proof (context_subst_fun csubst Hpars). subst s'. clear csubst.
  f_equal.
  rewrite !subst_context_length subst_instance_context_length.
  f_equal. f_equal. f_equal. f_equal.
  f_equal. rewrite -map_map_compose.
  rewrite subst_instance_to_extended_list_k.
  rewrite -map_map_compose.
  rewrite -to_extended_list_k_map_subst. rewrite subst_instance_context_length; lia.
  now rewrite (subst_to_extended_list_k _ _ pars).
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
      eapply invert_red_sort in reds. discriminate.
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


Lemma subst_inds_concl_head ind u mdecl (arity : context) :
  let head := tRel (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| + #|arity|) in
  let s := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  inductive_ind ind < #|ind_bodies mdecl| ->
  subst s (#|arity| + #|ind_params mdecl|)
        (subst_instance_constr u head)
  = tInd ind u.
Proof.
  intros.
  subst head. simpl subst_instance_constr.
  rewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| - S (inductive_ind ind)) (tInd ind u)) //; try lia.
  subst s. rewrite inds_spec rev_mapi nth_error_mapi /=.
  elim nth_error_spec. 
  + intros. simpl.
    f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
  + rewrite List.rev_length. lia.
Qed.

Lemma declared_constructor_valid_ty {cf:checker_flags} Σ Γ mdecl idecl i n cdecl u :
  wf Σ.1 ->
  wf_local Σ Γ ->
  declared_constructor Σ.1 mdecl idecl (i, n) cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isType Σ Γ (type_of_constructor mdecl cdecl (i, n) u).
Proof.
  move=> wfΣ wfΓ declc Hu.
  epose proof (validity Σ wfΣ Γ wfΓ (tConstruct i n u)
    (type_of_constructor mdecl cdecl (i, n) u)).
  forward X by eapply type_Construct; eauto.
  destruct X.
  destruct i0.
  2:eauto.
  destruct i0 as [ctx [s [Hs ?]]].
  unfold type_of_constructor in Hs.
  destruct (on_declared_constructor _ declc); eauto.
  destruct s0 as [csort [Hsorc Hc]].
  destruct Hc as [onctype [cs Hcs]].
  destruct cs.
  rewrite cshape_eq in Hs. clear -declc Hs.
  rewrite /subst1 !subst_instance_constr_it_mkProd_or_LetIn
  !subst_it_mkProd_or_LetIn in Hs.
  rewrite !subst_instance_constr_mkApps !subst_mkApps in Hs.
  rewrite !subst_instance_context_length Nat.add_0_r in Hs.
  rewrite subst_inds_concl_head in Hs.
  + simpl. destruct declc as [[onm oni] ?].
    now eapply nth_error_Some_length in oni.
  + now rewrite !destArity_it_mkProd_or_LetIn destArity_app /= destArity_tInd in Hs.
Qed.

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

Lemma declared_inductive_unique {Σ ind mdecl mdecl' idecl idecl'} : 
  declared_inductive Σ mdecl ind idecl ->
  declared_inductive Σ mdecl' ind idecl' ->
  (mdecl = mdecl') * (idecl = idecl').
Proof.
  unfold declared_inductive, declared_minductive.
  intros [-> ?] [eq ?].
  noconf eq. split; congruence.
Qed.

Lemma declared_constructor_unique {Σ c mdecl mdecl' idecl idecl' cdecl cdecl'} : 
  declared_constructor Σ mdecl idecl c cdecl ->
  declared_constructor Σ mdecl' idecl' c cdecl' ->
  (mdecl = mdecl') * (idecl = idecl') * (cdecl = cdecl').
Proof.
  unfold declared_constructor.
  intros [? ?] [eq ?]. destruct (declared_inductive_unique H eq).
  subst mdecl' idecl'. rewrite H0 in H1. intuition congruence.
Qed.

Lemma subst_context_nil s n : subst_context s n [] = [].
Proof. reflexivity. Qed.

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

Lemma mkApps_ind_typing_spine {cf:checker_flags} Σ Γ Γ' ind i
  inst ind' i' args args' : 
  wf Σ.1 ->
  wf_local Σ Γ ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) ->
  typing_spine Σ Γ (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) inst 
    (mkApps (tInd ind' i') args') ->
  ∑ instsubst, (make_context_subst (List.rev Γ') inst [] = Some instsubst) *
  (#|inst| = context_assumptions Γ' /\ ind = ind' /\ 
  R_universe_instance (eq_universe (global_ext_constraints Σ)) i i') *
  All2 (fun par par' => Σ ;;; Γ |- par = par') (map (subst0 instsubst) args) args' *
  (subslet Σ Γ instsubst Γ').
Proof.
  intros wfΣ wfΓ; revert args args' ind i ind' i' inst.
  revert Γ'. refine (ctx_length_rev_ind _ _ _); simpl.
  - intros args args' ind i ind' i' inst wat Hsp.
    depelim Hsp.
    eapply invert_cumul_ind_l in c as [i'' [args'' [? ?]]]; auto.
    eapply invert_red_ind in r as [? [eq ?]]. solve_discr. exists nil.
    intuition auto. clear i0.
    revert args' a. clear -b wfΣ wfΓ. induction b; intros args' H; depelim H; constructor.
    rewrite subst_empty.
    transitivity y; auto. symmetry.
    now eapply red_conv. now eauto.
    eapply invert_cumul_prod_r in c as [? [? [? [[? ?] ?]]]]; auto.
    eapply invert_red_ind in r as [? [eq ?]]. now solve_discr.
  - intros d Γ' IH args args' ind i ind' i' inst wat Hsp.
    rewrite it_mkProd_or_LetIn_app in Hsp.
    destruct d as [na [b|] ty]; simpl in *; rewrite /mkProd_or_LetIn /= in Hsp.
    + rewrite context_assumptions_app /= Nat.add_0_r.
      eapply typing_spine_letin_inv in Hsp; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn /= in Hsp.
      specialize (IH (subst_context [b] 0 Γ')).
      forward IH by rewrite subst_context_length; lia.
      rewrite subst_mkApps Nat.add_0_r in Hsp.
      specialize (IH (map (subst [b] #|Γ'|) args) args' ind i ind' i' inst).
      forward IH. {
        move: wat; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => wat.
        eapply isWAT_tLetIn_red in wat; auto.
        now rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps Nat.add_0_r
        in wat. }
      rewrite context_assumptions_subst in IH.
      intuition auto.
      destruct X as [isub [[[Hisub Hinst] Hargs] Hs]].
      eexists. intuition auto.
      eapply make_context_subst_spec in Hisub.
      eapply make_context_subst_spec_inv.
      rewrite List.rev_app_distr. simpl.
      rewrite List.rev_involutive.
      eapply (context_subst_subst [{| decl_name := na; decl_body := Some b;  decl_type := ty |}] [] [b] Γ').
      rewrite -{2}  (subst_empty 0 b). eapply context_subst_def. constructor.
      now rewrite List.rev_involutive in Hisub.
      rewrite map_map_compose in Hargs.
      assert (map (subst0 isub ∘ subst [b] #|Γ'|) args = map (subst0 (isub ++ [b])) args) as <-.
      { eapply map_ext => x. simpl.
        assert(#|Γ'| = #|isub|).
        { apply make_context_subst_spec in Hisub.
          apply context_subst_length in Hisub.
          now rewrite List.rev_involutive subst_context_length in Hisub. }
        rewrite H0.
        now rewrite -(subst_app_simpl isub [b] 0). }
      exact Hargs. 
      eapply subslet_app; eauto. rewrite -{1}(subst_empty 0 b). repeat constructor.
      rewrite !subst_empty.
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in wat.
      now eapply isWAT_tLetIn_dom in wat.
    + rewrite context_assumptions_app /=.
      pose proof (typing_spine_WAT_concl Hsp).
      depelim Hsp.
      eapply invert_cumul_prod_l in c as [? [? [? [[? ?] ?]]]]; auto.
      eapply invert_red_ind in r as [? [eq ?]]. now solve_discr.
      eapply cumul_Prod_inv in c as [conva cumulB].
      eapply (substitution_cumul0 _ _ _ _ _ _ hd) in cumulB; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn /= in cumulB.
      specialize (IH (subst_context [hd] 0 Γ')).
      forward IH by rewrite subst_context_length; lia.
      specialize (IH (map (subst [hd] #|Γ'|) args) args' ind i ind' i' tl). all:auto.
      have isWATs: isWfArity_or_Type Σ Γ
      (it_mkProd_or_LetIn (subst_context [hd] 0 Γ')
          (mkApps (tInd ind i) (map (subst [hd] #|Γ'|) args))). {
        move: wat; rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= => wat.
        eapply isWAT_tProd in wat; auto. destruct wat as [isty wat].
        epose proof (isWAT_subst wfΣ (Γ:=Γ) (Δ:=[vass na ty])).
        forward X0. constructor; auto.
        specialize (X0 (it_mkProd_or_LetIn Γ' (mkApps (tInd ind i) args)) [hd]).
        forward X0. constructor. constructor. rewrite subst_empty; auto.
        eapply isWAT_tProd in i0; auto. destruct i0. 
        eapply type_Cumul with A; auto. now eapply conv_cumul.
        now rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps Nat.add_0_r
        in X0. }
      rewrite subst_mkApps Nat.add_0_r in cumulB. simpl in *. 
      rewrite context_assumptions_subst in IH.
      eapply typing_spine_strengthen in Hsp.
      3:eapply cumulB. all:eauto.
      intuition auto.
      destruct X1 as [isub [[[Hisub [Htl [Hind Hu]]] Hargs] Hs]].
      exists (isub ++ [hd]). rewrite List.rev_app_distr.
      intuition auto. 2:lia.
      * apply make_context_subst_spec_inv.
        apply make_context_subst_spec in Hisub.
        rewrite List.rev_app_distr !List.rev_involutive in Hisub |- *.
        eapply (context_subst_subst [{| decl_name := na; decl_body := None; decl_type := ty |}] [hd] [hd] Γ'); auto.
        eapply (context_subst_ass _ [] []). constructor.
      * assert (map (subst0 isub ∘ subst [hd] #|Γ'|) args = map (subst0 (isub ++ [hd])) args) as <-.
      { eapply map_ext => x. simpl.
        assert(#|Γ'| = #|isub|).
        { apply make_context_subst_spec in Hisub.
          apply context_subst_length in Hisub.
          now rewrite List.rev_involutive subst_context_length in Hisub. }
        rewrite H.
        now rewrite -(subst_app_simpl isub [hd] 0). }
        now rewrite map_map_compose in Hargs.
      * eapply subslet_app; auto.
        constructor. constructor. rewrite subst_empty.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in wat.
        eapply isWAT_tProd in wat as [Hty _]; auto.
        eapply type_Cumul; eauto. now eapply conv_cumul.
Qed.

Lemma firstn_app_left (A : Type) (n : nat) (l1 l2 : list A) k :
  k = #|l1| + n ->
  firstn k (l1 ++ l2) = l1 ++ firstn n l2.
Proof. intros ->; apply firstn_app_2.  Qed.

Lemma map_subst_app_to_extended_list_k s s' ctx k  :
  k = #|s| ->
  map (subst0 (s ++ s')) (to_extended_list_k ctx k) = 
  map (subst0 s') (to_extended_list_k ctx 0).
Proof.
  intros ->.
  induction ctx in s, s' |- *; simpl; auto.
  destruct a as [na [b|] ty]. simpl.
Admitted.  

Lemma map_lift0 l : map (lift0 0) l = l.
Proof. induction l; simpl; auto. now rewrite lift0_id. Qed.

Lemma map_context_length f l : #|map_context f l| = #|l|.
Proof. now rewrite /map_context map_length. Qed.

Lemma skipn_all_app_eq {A} n (l l' : list A) : n = #|l| -> skipn n (l ++ l') = l'.
Proof.
  move->. apply skipn_all_app.
Qed.

Lemma firstn_length_le_inv {A} n (l : list A) : #|firstn n l| = n -> n <= #|l|.
Proof.
  induction l in n |- *; simpl; auto with arith;
  destruct n; simpl; auto with arith. discriminate.
Qed.

Hint Rewrite subst_context_length subst_instance_context_assumptions subst_instance_context_length 
  app_context_length map_context_length map_length : len.

Lemma Construct_Ind_ind_eq {cf:checker_flags} {Σ} (wfΣ : wf Σ.1):
  forall {Γ n i args u i' args' u' mdecl idecl cdecl},
  Σ ;;; Γ |- mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
  declared_constructor Σ.1 mdecl idecl (i, n) cdecl ->
  ∑ cs (oc : on_constructor (lift_typing typing) (Σ.1, ind_universes mdecl) mdecl (inductive_ind i) idecl cdecl cs),
  (i = i') * 
  (* Universe instances match *)
  R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' *
    
  (#|args| = (ind_npars mdecl + context_assumptions oc.2.π1.(cshape_args))%nat) *
  ∑ parsubst argsubst, 
    let parctx := (subst_instance_context u (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0
    ((subst_context (inds (inductive_mind i) u mdecl.(ind_bodies)) #|ind_params mdecl|
    (subst_instance_context u oc.2.π1.(cshape_args))))) in
    
    context_subst parctx (firstn (ind_npars mdecl) args) parsubst *
    context_subst argctx (skipn (ind_npars mdecl) args) argsubst *
    subslet Σ Γ parsubst parctx * 
    subslet Σ Γ argsubst argctx * 
    ∑ s, type_local_ctx (lift_typing typing) Σ Γ argctx s *
    (** Parameters match *)
    (All2 (fun par par' => Σ ;;; Γ |- par = par') 
      (firstn mdecl.(ind_npars) args) 
      (firstn mdecl.(ind_npars) args') * 

    (** Indices match *)
    All2 (fun par par' => Σ ;;; Γ |- par = par') 
      (map (subst0 argsubst ∘ subst0 (inds (inductive_mind i) u mdecl.(ind_bodies)) ∘ (subst_instance_constr u)) 
        oc.2.π1.(cshape_indices))
      (skipn mdecl.(ind_npars) args')).

Proof.
  intros Γ n i args u i' args' u' mdecl idecl cdecl h declc.
  destruct (on_declared_constructor _ declc). destruct s as [? [_ onc]].
  exists x, onc.
  unshelve epose proof (validity _ _ _ _ _ _ h) as [_ vi']; eauto using typing_wf_local.
  eapply type_mkApps_inv in h; auto.
  destruct h as [T [U [[hC hs] hc]]].
  apply inversion_Construct in hC
    as [mdecl' [idecl' [cdecl' [hΓ [isdecl [const htc]]]]]]; auto.
  assert (vty:=declared_constructor_valid_ty _ _ _ _ _ _ _ _ wfΣ hΓ isdecl const). 
  eapply typing_spine_strengthen in hs. 3:eapply htc. all:eauto.
  eapply typing_spine_weaken_concl in hs.
  3:{ eapply cumul_trans; eauto with pcuic. } all:auto.
  clear hc htc.
  destruct (declared_constructor_unique isdecl declc) as [[? ?] ?].
  subst mdecl' idecl' cdecl'. clear declc.
  destruct p as [onmind onind].
  case: onc => [p [cs' t]]  /=.
  simpl in *. destruct cs'. simpl in *.
  unfold type_of_constructor in hs. simpl in hs.
  rewrite cshape_eq in hs.  
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in hs.
  rewrite !subst_it_mkProd_or_LetIn subst_instance_context_length Nat.add_0_r in hs.
  rewrite subst_instance_constr_mkApps subst_mkApps subst_instance_context_length in hs.
  assert (Hind : inductive_ind i < #|ind_bodies mdecl|).
  { red in isdecl. destruct isdecl.
    destruct H as [_ H]. now eapply nth_error_Some_length in H. }
  rewrite (subst_inds_concl_head i) in hs => //.
  destruct isdecl as [[? oni] onc'].
  rewrite -it_mkProd_or_LetIn_app in hs.
  assert(ind_npars mdecl = PCUICAst.context_assumptions (ind_params mdecl)).
  { now pose (onNpars _ _ _ _ onmind). }
  assert (closed_ctx (ind_params mdecl)).
  { destruct onmind.
    red in onParams. now apply closed_wf_local in onParams. }
  eapply mkApps_ind_typing_spine in hs as [isubst [[[Hisubst [Hargslen [Hi Hu]]] Hargs] Hs]]; auto.
  split=> //. split=> //.
  now rewrite Hargslen context_assumptions_app !context_assumptions_subst !subst_instance_context_assumptions H0.
  exists (skipn #|cshape_args| isubst), (firstn #|cshape_args| isubst).
  apply make_context_subst_spec in Hisubst.
  move: Hisubst.
  rewrite List.rev_involutive.
  move/context_subst_app.
  rewrite !subst_context_length !subst_instance_context_length.
  rewrite context_assumptions_subst subst_instance_context_assumptions -H0.
  move=>  [argsub parsub].
  rewrite closed_ctx_subst in parsub.
  now rewrite closedn_subst_instance_context.
  eapply subslet_app_inv in Hs.
  move: Hs. autorewrite with len. intuition auto.
  rewrite closed_ctx_subst in a => //.
  now rewrite closedn_subst_instance_context.
  exists x.
  split.
  eapply subst_type_local_ctx; eauto.
  rewrite closed_ctx_subst => //.
  now rewrite closedn_subst_instance_context.
  move/onParams: onmind. rewrite /on_context.
  pose proof (wf_local_instantiate Σ (InductiveDecl mdecl) (ind_params mdecl) u).
  move=> H'. eapply X in H'; eauto.
  now eapply weaken_wf_local.
  admit.

  move: (All2_firstn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
  move: (All2_skipn  _ _ _ _ _ mdecl.(ind_npars) Hargs).
  clear Hargs.
  rewrite !map_map_compose !map_app.
  rewrite -map_map_compose.
  rewrite (firstn_app_left _ 0).
  rewrite PCUICUnivSubst.map_subst_instance_constr_to_extended_list_k.
  rewrite -map_map_compose.
  rewrite -to_extended_list_k_map_subst; first lia.
  now rewrite map_length to_extended_list_k_length.
  rewrite /= app_nil_r.
  rewrite skipn_all_app_eq.
  autorewrite with len. 
  rewrite to_extended_list_k_length. lia.
  rewrite !map_map_compose.

  rewrite -(firstn_skipn #|cshape_args| isubst).
  rewrite -[map _ (to_extended_list_k _ _)]map_map_compose.
  rewrite subst_instance_to_extended_list_k.
  rewrite -[map _ (to_extended_list_k _ _)]map_map_compose. 
  rewrite -to_extended_list_k_map_subst.
  rewrite subst_instance_context_length. lia.
  rewrite map_subst_app_to_extended_list_k.
  rewrite firstn_length_le => //.
  apply context_subst_length in argsub.
  autorewrite with len in argsub.
  now apply firstn_length_le_inv.

  erewrite subst_to_extended_list_k.
  rewrite map_lift0. split. eauto.
Admitted.  
  (*rewrite closed_ctx_subst in Hasubst.
  now rewrite closedn_subst_instance_context.
  apply make_context_subst_spec_inv. rewrite List.rev_involutive.
  rewrite subst_instance_context_assumptions in Hasubst.
  now rewrite -H0 in Hasubst.


  rewrite it_mkProd_or_LetIn_app.
  right. unfold type_of_constructor in vty.
  rewrite cshape_eq in vty. move: vty.
  rewrite !subst_instance_constr_it_mkProd_or_LetIn.
  rewrite !subst_it_mkProd_or_LetIn subst_instance_context_length Nat.add_0_r.
  rewrite subst_instance_constr_mkApps subst_mkApps subst_instance_context_length.
  rewrite subst_inds_concl_head. all:simpl; auto.
Admitted.*)

Lemma map_subst_lift_id s l : map (subst0 s ∘ lift0 #|s|) l = l.
Proof.
  induction l; simpl; auto.
  rewrite -{1}(Nat.add_0_r #|s|) simpl_subst'; auto.
  now rewrite lift0_id IHl.  
Qed.

Lemma subslet_wf_local {cf:checker_flags} Σ Γ Δ :
  wf_local Σ (Γ ,,, Δ) ->
  ∑ s, type_local_ctx (lift_typing typing) Σ Γ Δ s.
Proof.
  induction Δ. simpl. 
  intros _. exists Universe.type0m. exact I.
  intros H; depelim H. red in l.
  destruct l as [u Hu].
  destruct (IHΔ H) as [s Hs].
  exists (Universe.sup u s).
  constructor.
Admitted.

Lemma mkApps_conv_args `{checker_flags} Σ Γ f f' u v :
  wf Σ.1 ->
  Σ ;;; Γ |- f = f' ->
  All2 (fun x y => Σ ;;; Γ |- x = y) u v ->
  Σ ;;; Γ |- mkApps f u = mkApps f' v.
Proof.
  move=> wfΣ cf cuv. induction cuv in f, f', cf |- *.
  - auto.
  - simpl. apply IHcuv.
    now apply App_conv.
Qed.

Lemma sr_red1 {cf:checker_flags} : env_prop SR_red1.
Proof.
  apply typing_ind_env; intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps;
    match goal with
    | [H : (_ ;;; _ |- _ <= _) |- _ ] => idtac
    | _ =>
      depelim Hu; try solve [apply mkApps_Fix_spec in x; noconf x];
      try solve [econstructor; eauto] ;
      try solve [
        match goal with
        | h : _ = mkApps _ ?args |- _ =>
          let e := fresh "e" in
          apply (f_equal nApp) in h as e ; simpl in e ;
          rewrite nApp_mkApps in e ; simpl in e ;
          destruct args ; discriminate
        end
      ]
    end.

  - (* Rel *)
    rewrite heq_nth_error in e. destruct decl as [na b ty]; noconf e.
    simpl.
    pose proof (nth_error_All_local_env_over heq_nth_error X); eauto.
    destruct lookup_wf_local_decl; cbn in *.
    rewrite <- (firstn_skipn (S n) Γ).
    eapply weakening_length; auto.
    { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
    now unfold app_context; rewrite firstn_skipn.
    apply o.

  - (* Prod *)
    constructor; eauto.
    eapply (context_conversion _ wf _ _ _ _ typeb).
    constructor; auto with pcuic.
    constructor; auto. exists s1; auto.

  - (* Lambda *)
    eapply type_Cumul. eapply type_Lambda; eauto.
    eapply (context_conversion _ wf _ _ _ _ typeb).
    constructor; auto with pcuic.
    constructor; auto. exists s1; auto.
    assert (Σ ;;; Γ |- tLambda n t b : tProd n t bty). econstructor; eauto.
    edestruct (validity _ wf _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor. apply Hu.

  - (* LetIn body *)
    eapply type_Cumul.
    apply (substitution_let _ Γ n b b_ty b' b'_ty wf typeb').
    specialize (typing_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. constructor.

  - (* LetIn value *)
    eapply type_Cumul.
    econstructor; eauto.
    eapply (context_conversion _ wf _ _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto. constructor; auto.
    now exists s1. red. auto.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* LetIn type annotation *)
    specialize (forall_u _ Hu).
    eapply type_Cumul.
    econstructor; eauto.
    eapply type_Cumul. eauto. right; exists s1; auto.
    apply red_cumul; eauto.
    eapply (context_conversion _ wf _ _ _ _ typeb').
    constructor. auto with pcuic. constructor; eauto. constructor; auto.
    exists s1; auto. red; eauto.
    eapply type_Cumul. eauto. right. exists s1; auto. eapply red_cumul. now eapply red1_red.
    assert (Σ ;;; Γ |- tLetIn n b b_ty b' : tLetIn n b b_ty b'_ty). econstructor; eauto.
    edestruct (validity _ wf _ wfΓ _ _ X0). apply i.
    eapply cumul_red_r.
    apply cumul_refl'. now constructor.

  - (* Application *)
    eapply substitution0; eauto.
    pose proof typet as typet'.
    eapply inversion_Lambda in typet' as [s1 [B' [Ht [Hb HU]]]]=>//.
    apply cumul_Prod_inv in HU as [eqA leqB] => //.
    destruct (validity _ wf _ wfΓ _ _ typet).

    eapply type_Cumul; eauto.
    unshelve eapply (context_conversion _ wf _ _ _ _ Hb); eauto with wf.
    constructor. auto with pcuic. constructor ; eauto.
    constructor; auto with pcuic. red; eauto.
    eapply isWAT_tProd in i as [Hs _]; auto.
    eapply isWAT_tProd in i as [_ Hs]; intuition auto.

  - (* Fixpoint unfolding *)
    assert (args <> []) by (destruct args; simpl in *; congruence).
    apply mkApps_inj in H as [-> Hu]; auto.
    rewrite mkApps_nonempty; auto.
    epose (last_nonempty_eq H0). rewrite <- Hu in e1. rewrite <- e1.
    clear e1.
    specialize (type_mkApps_inv _ _ _ _ _ wf typet) as [T' [U' [[appty spty] Hcumul]]].
    specialize (validity _ wf _ wfΓ _ _ appty) as [_ vT'].
    eapply type_tFix_inv in appty as [T [arg [fn' [[Hnth Hty]]]]]; auto.
    rewrite e in Hnth. noconf Hnth.
    eapply type_App.
    eapply type_Cumul.
    eapply type_mkApps. eapply type_Cumul; eauto. eapply spty.
    eapply validity; eauto.
    eauto. eauto.

  - (* Congruence *)
    eapply type_Cumul; [eapply type_App| |]; eauto with wf.
    eapply validity. eauto. eauto.
    eapply type_App; eauto. eapply red_cumul_inv.
    eapply (red_red Σ Γ [vass na A] [] [u] [N2]); auto.
    constructor. constructor.

  - (* Constant unfolding *)
    unshelve epose proof (declared_constant_inj decl decl0 _ _); tea; subst decl.
    destruct decl0 as [ty body' univs]; simpl in *; subst body'.
    eapply on_declared_constant in H; tas; cbn in H.
    rewrite <- (app_context_nil_l Γ).
    apply typecheck_closed in H as H'; tas; [|constructor].
    destruct H' as [_ H']. apply andb_and in H'.
    replace (subst_instance_constr u body)
      with (lift0 #|Γ| (subst_instance_constr u body)).
    replace (subst_instance_constr u ty)
      with (lift0 #|Γ| (subst_instance_constr u ty)).
    2-3: rewrite lift_subst_instance_constr lift_closed; cbnr; apply H'.
    eapply weakening; tea.
    now rewrite app_context_nil_l.
    eapply typing_subst_instance_decl with (Γ0:=[]); tea.

  - (* iota reduction *)
    subst npar.
    clear forall_u forall_u0 X X0.
    unfold iota_red. rename args into iargs. rename args0 into cargs.
    pose proof typec as typec'.
    eapply inversion_mkApps in typec as [A [U [tyc [tyargs tycum]]]]; auto.
    eapply (inversion_Construct Σ wf) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
    eapply Construct_Ind_ind_eq in typec'; eauto.
    destruct typec' as [cs [onc cty]].
    destruct (on_declared_constructor wf declc) as [[onmind onind] [csort [_ _]]].
    destruct declc as [[declmi decli] declc].
    destruct isdecl as [declmi' decli'].
    red in declmi', declmi. rewrite declmi' in declmi. noconf declmi.
    rewrite decli' in decli. noconf decli. simpl in declc.
    eapply (build_branches_type_lookup _  Γ ind mdecl idecl cdecl' _ _ _ brs) in heq_map_option_out; eauto.
    2:split; eauto.
    2:{ eapply All2_impl; eauto. simpl; intuition eauto. }
    unshelve eapply build_case_predicate_type_spec in heq_build_case_predicate_type as 
      [parsubst [csubst ptyeq]]. 2:eauto. subst pty.
    destruct heq_map_option_out as [nargs [br [brty [[[Hbr Hbrty] brbrty] brtys]]]].
    unshelve eapply (branch_type_spec Σ.1) in brtys. 2:exact onc. 6:eauto.
    2:split; auto. all:eauto.
    destruct (PCUICParallelReductionConfluence.nth_nth_error (@eq_refl _ (nth c0 brs (0, tDummy)))).
    assert (H : ∑ t', nth_error btys c0 = Some t').
    pose proof (All2_length _ _ X5). eapply nth_error_Some_length in e. rewrite H in e.
    destruct (nth_error_spec btys c0). eexists; eauto. elimtype False; lia.
    destruct H as [t' Ht'].
    rewrite Hbr in e. noconf e. simpl in H. rewrite <- H. simpl.  
    2:{ destruct a. congruence. } clear H.
    destruct brtys as [-> ->].
    eapply type_mkApps. eauto.
    set iargs' := @cshape_args _ _  _  _  _ onc.2.π1.
    destruct cty as [[[_ equ] eqargs] [parsubst' [argsubst' [[[[Hpars Hargs] subpars] subargs] ?]]]].
    assert(leq:Σ ;;; Γ |- (it_mkProd_or_LetIn
    (subst_context parsubst 0
       (subst_context (inds (inductive_mind ind) u (ind_bodies mdecl))
          #|ind_params mdecl| (map_context (subst_instance_constr u) iargs')))
    (mkApps ((lift0 #|iargs'|) p)
       (map
          (fun x : term =>
           subst parsubst #|iargs'|
             (subst (inds (inductive_mind ind) u (ind_bodies mdecl))
                (#|iargs'| + #|ind_params mdecl|) (subst_instance_constr u x)))
          (cshape_indices onc.2.π1) ++
        [mkApps (tConstruct ind c0 u)
           (map (lift0 #|iargs'|) (firstn (PCUICAst.ind_npars mdecl) iargs) ++
            to_extended_list 
              (subst_context parsubst 0
              (subst_context (inds (inductive_mind ind) u (ind_bodies mdecl))
                 #|ind_params mdecl| (map_context (subst_instance_constr u) iargs'))))])))
           <=
    (it_mkProd_or_LetIn
     (subst_context parsubst' 0
        (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
           #|ind_params mdecl| (map_context (subst_instance_constr u1) iargs')))
     (mkApps ((lift0 #|iargs'|) p)
        (map
           (fun x : term =>
            subst parsubst' #|iargs'|
              (subst (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                 (#|iargs'| + #|ind_params mdecl|) (subst_instance_constr u1 x)))
           (cshape_indices onc.2.π1) ++
         [mkApps (tConstruct ind c0 u1) (* wrong *)
            (map (lift0 #|iargs'|) (firstn (PCUICAst.ind_npars mdecl) cargs) ++
             to_extended_list 
             (subst_context parsubst' 0
             (subst_context (inds (inductive_mind ind) u1 (ind_bodies mdecl))
                #|ind_params mdecl| (map_context (subst_instance_constr u1) iargs'))))])))).
    constructor. admit.
    unshelve eapply typing_spine_strengthen. 4:eapply leq. all:auto.
    clear leq.
    set(cindices := map
    (fun x : term =>
     subst parsubst #|cshape_args onc.2.π1|
       (subst (inds (inductive_mind ind) u (ind_bodies mdecl))
          (#|cshape_args onc.2.π1| + #|ind_params mdecl|)
          (subst_instance_constr u x)))
    (cshape_indices onc.2.π1)) in *.
    destruct s as [s [argss [Hpars' Hargs']]].
    eapply (typing_spine_weaken_concl (S:=
      (mkApps p (map (subst0 argsubst') cindices ++ [mkApps (tConstruct ind c0 u1) cargs])))).
    auto.
    2:{ eapply conv_cumul; auto.
        eapply mkApps_conv_args; auto with pcuic.
        eapply All2_app; auto with pcuic.
        unfold cindices. rewrite !map_map_compose.
        eapply All2_trans. eapply conv_trans. auto.
        2:eauto.
        admit.  }
    eapply typing_spine_it_mkProd_or_LetIn_close_eq; eauto.
    * eapply make_context_subst_spec_inv. rewrite List.rev_involutive.
      eauto.
    * rewrite skipn_length.
      pose proof (onNpars _ _ _ _ onmind).
      pose proof (context_assumptions_length_bound (ind_params mdecl)).
      lia.
      rewrite !context_assumptions_subst subst_instance_context_assumptions /iargs'. lia.
    * right.
      eexists.
      eapply type_it_mkProd_or_LetIn; eauto. 
      eapply type_mkApps.
      eapply weakening_gen in typep. auto. eapply typep. all:eauto.
      now autorewrite with len. 
      eapply type_local_ctx_wf_local in argss; auto.
      admit.

    * rewrite subst_mkApps.
      pose proof (context_subst_length _ _ _ Hargs).
      rewrite !subst_context_length subst_instance_context_length in H.
      rewrite -{1}(Nat.add_0_r #|iargs'|) (simpl_subst' _ _ 0 _ #|iargs'|) /iargs'; try lia.
      rewrite lift0_id.
      f_equal.
      rewrite map_app /= subst_mkApps. f_equal.
      ** admit.
      ** f_equal. simpl. f_equal.
        rewrite map_app -{1}(firstn_skipn (ind_npars mdecl) cargs).  
        f_equal.
        rewrite map_map_compose.
        now rewrite H map_subst_lift_id.
        unfold to_extended_list.
        erewrite subst_to_extended_list_k. rewrite map_id_f. intros x; apply lift0_id.
        reflexivity.
        apply make_context_subst_spec_inv. rewrite List.rev_involutive. auto.
      * admit. 

  - (* Case congruence *) admit.
  - (* Case congruence *) admit.
  - (* Case congruence *) admit.
  - (* Case congruence *) admit.
  - (* Proj CoFix congruence *) admit.
  - (* Proj Constructor congruence *) admit.
  - (* Proj reduction *) admit.
  - (* Fix congruence *)
    symmetry in H; apply mkApps_Fix_spec in H. simpl in H. subst args.
    simpl. destruct narg; discriminate.
  - (* Fix congruence *)
    admit.
  - (* Fix congruence *)
    admit.
  - (* CoFix congruence *)
    admit.
  - (* CoFix congruence *)
    admit.
  - (* Conversion *)
    specialize (forall_u _ Hu).
    eapply type_Cumul; eauto.
    destruct X2 as [[wf' _]|[s Hs]].
    now left.
    now right.
Admitted.

Definition sr_stmt {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |- u : T.

Theorem subject_reduction {cf:checker_flags} : forall (Σ : global_env_ext) Γ t u T,
  wf Σ -> Σ ;;; Γ |- t : T -> red Σ Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred. auto.
  eapply sr_red1 in IHHred; eauto with wf. now apply IHHred.
Qed.

Lemma subject_reduction1 {cf:checker_flags} {Σ Γ t u T}
  : wf Σ.1 -> Σ ;;; Γ |- t : T -> red1 Σ.1 Γ t u -> Σ ;;; Γ |- u : T.
Proof.
  intros. eapply subject_reduction; try eassumption.
  now apply red1_red.
Defined.

Section SRContext.
  Context {cf:checker_flags}.

  (* todo: rename wf_local_app *)
  Definition wf_local_app' {Σ Γ1 Γ2} :
    wf_local Σ Γ1 -> wf_local_rel Σ Γ1 Γ2
    -> wf_local Σ (Γ1 ,,, Γ2).
  Proof.
    intros H1 H2. apply wf_local_local_rel.
    apply wf_local_rel_local in H1.
    apply wf_local_rel_app_inv; tas.
    now rewrite app_context_nil_l.
  Qed.

  Definition cumul_red_l' `{checker_flags} :
    forall Σ Γ t u,
      wf Σ.1 ->
      red (fst Σ) Γ t u ->
      Σ ;;; Γ |- t <= u.
  Proof.
    intros Σ Γ t u hΣ h.
    induction h.
    - eapply cumul_refl'.
    - eapply PCUICConversion.cumul_trans ; try eassumption.
      eapply cumul_red_l.
      + eassumption.
      + eapply cumul_refl'.
  Defined.

  Hint Constructors OnOne2_local_env : aa.
  Hint Unfold red1_ctx : aa.


  Lemma red1_ctx_app Σ Γ Γ' Δ :
    red1_ctx Σ Γ Γ' ->
    red1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ. trivial.
    intro H. simpl. constructor. now apply IHΔ.
  Qed.

  Lemma red1_red_ctx Σ Γ Γ' :
    red1_ctx Σ Γ Γ' ->
    red_ctx Σ Γ Γ'.
  Proof.
    induction 1; cbn in *.
    - constructor. reflexivity. cbn; eauto using red1_red.
    - constructor. reflexivity.
      destruct p as [[? []]|[? []]]; cbn; eauto using red1_red.
    - destruct d as [na [bo|] ty]; constructor; eauto.
      split; eapply refl_red.
      apply refl_red.
  Qed.

  Lemma nth_error_red1_ctx Σ Γ Γ' n decl :
    wf Σ ->
    nth_error Γ n = Some decl ->
    red1_ctx Σ Γ Γ' ->
    ∑ decl', nth_error Γ' n = Some decl'
              × red Σ Γ' (lift0 (S n) (decl_type decl))
              (lift0 (S n) (decl_type decl')).
  Proof.
    intros wfΣ h1 h2; induction h2 in n, h1 |- *.
    - destruct n.
      + inversion h1; subst. exists (vass na t').
        split; cbnr.
        eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
        apply red1_red; tas.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + inversion h1; subst.
        destruct p as [[? []]|[? []]].
        -- exists (vdef na b' t).
           split; cbnr.
        -- exists (vdef na b t').
           split; cbnr.
           eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
           apply red1_red; tas.
      + exists decl. split; tas. apply refl_red.
    - destruct n.
      + exists d. split; cbnr. inv h1; apply refl_red.
      + cbn in h1. specialize (IHh2 _ h1).
        destruct IHh2 as [decl' [X1 X2]].
        exists decl'. split; tas.
        rewrite !(simpl_lift0 _ (S n)).
        eapply (weakening_red_0 wfΣ _ [_]); tas; cbnr.
  Qed.


  Lemma wf_local_isType_nth Σ Γ n decl :
    wf Σ.1 ->
    wf_local Σ Γ ->
    nth_error Γ n = Some decl ->
    ∑ s, Σ ;;; Γ |- lift0 (S n) (decl_type decl) : tSort s.
  Proof.
    induction n in Γ, decl |- *; intros hΣ hΓ e; destruct Γ;
      cbn; inversion e; inversion hΓ; subst.
    all: try (destruct X0 as [s Ht]; exists s;
              eapply (weakening _ _ [_] _ (tSort s)); tas).
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
    - eapply IHn in H0; tas. destruct H0 as [s Ht]. exists s.
      rewrite simpl_lift0.
      eapply (weakening _ _ [_] _ (tSort s)); tas; cbnr.
  Qed.

  Ltac invs H := inversion H; subst.
  Ltac invc H := inversion H; subst; clear H.

  Lemma subject_reduction_ctx :
    env_prop (fun Σ Γ t A => forall Γ', red1_ctx Σ Γ Γ' -> Σ ;;; Γ' |- t : A).
  Proof.
    assert (X: forall Σ Γ wfΓ, All_local_env_over typing
                          (fun Σ Γ (_ : wf_local Σ Γ)  t T (_ : Σ;;; Γ |- t : T) =>
                             forall Γ', red1_ctx Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Γ wfΓ
                          -> wf Σ -> forall Γ', red1_ctx Σ Γ Γ' -> wf_local Σ Γ'). {
      induction 1.
      - intros hΣ Γ' r. inv r.
      - intros hΣ Γ' r. inv r.
        + constructor; tas.
          destruct tu as [s Ht]. exists s. eapply subject_reduction1; tea.
        + constructor; tas. eapply IHX; tas.
          eexists. now eapply p.
      - intros hΣ Γ' r. inv r.
        + destruct X0 as [[? []]|[? []]]; constructor; cbn; tas.
          eapply subject_reduction1; tea.
          destruct tu as [s Ht]. exists s. eapply subject_reduction1; tea.
          econstructor; tea.
          2: eauto using red_cumul.
          right. destruct tu as [s ?]; exists s; eapply subject_reduction1; tea.
        + constructor; tas. eapply IHX; tas.
          eexists. now eapply p0.
          now eapply p. }
    eapply typing_ind_env; cbn; intros; try solve [econstructor; eauto with aa].
    - assert (X2: ∑ decl', nth_error Γ' n = Some decl'
             × red Σ.1 Γ' (lift0 (S n) (decl_type decl))
             (lift0 (S n) (decl_type decl'))) by now eapply nth_error_red1_ctx.
      destruct X2 as [decl' [H1 H2]].
      eapply type_Cumul. econstructor. eauto. exact H1.
      2: now eapply red_cumul_inv.
      right.
      clear decl' H1 H2.
      induction X1 in wfΓ, n, H, X0 |- *; cbn in *.
      + destruct n; cbn in *.
        * invc H. invs wfΓ. destruct X2 as [s Ht]; exists s.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          constructor; tas. exists s.
          eapply subject_reduction; tea; auto.
        * invc H. invs wfΓ.
          eapply wf_local_isType_nth in H1; tea.
          destruct H1 as [s Ht]. exists s.
          rewrite simpl_lift0.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          constructor; tas. destruct X2 as [s' ?]; exists s'.
          eapply subject_reduction; tea; auto.
      + destruct n; cbn in *.
        * invc H. invs wfΓ. destruct X2 as [s Ht]; exists s.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          destruct p as [[? []]|[? []]]; constructor; cbn; tas.
          now exists s.
          eapply subject_reduction; tea; auto.
          exists s. eapply subject_reduction; tea; auto.
          econstructor; tea.
          2: eauto using red_cumul.
          right. exists s; eapply subject_reduction1; tea.
        * invc H. invs wfΓ.
          eapply wf_local_isType_nth in H1; tea.
          destruct H1 as [s Ht]. exists s.
          rewrite simpl_lift0.
          eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
          destruct p as [[? []]|[? []]]; constructor; cbn; tas.
          eapply subject_reduction; tea; auto.
          destruct X2 as [s' Ht']. exists s'.
          eapply subject_reduction; tea; auto.
          econstructor; tea.
          2: eauto using red_cumul.
          right. destruct X2 as [s' ?]; exists s'; eapply subject_reduction1; tea.
      + destruct n; cbn in *.
        * invc H. clear IHX1. invs wfΓ.
          -- invs X0. destruct tu as [s Ht]; exists s.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             eapply (X _ _ wfΓ); tea. now constructor.
             eauto.
          -- invs X0. destruct tu as [s Ht]; exists s.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             eapply (X _ _ wfΓ); tea. now constructor.
             eauto.
        * invs wfΓ; inv X0.
          -- specialize (IHX1 _ _ H X4).
             destruct IHX1 as [s ?]; exists s.
             rewrite simpl_lift0.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             constructor. eauto.
             exists tu.π1. eauto.
          -- specialize (IHX1 _ _ H X5).
             destruct IHX1 as [s ?]; exists s.
             rewrite simpl_lift0.
             eapply (weakening _ _ [_] _ (tSort _)); tas; cbnr.
             constructor. eauto.
             exists tu.π1. eauto. cbn. eauto.
    - econstructor; tea; eauto.
      eapply All2_impl; tea; cbn.
      intros; rdest; eauto.
    - assert (XX: red1_ctx Σ.1 (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix))
        by now eapply red1_ctx_app.
      econstructor; tea.
      + set (Δ := Γ ,,, fix_context mfix) in *.
        assert (ZZ: ∑ wfΔ, All_local_env_over typing
                            (fun Σ Γ (_ : wf_local Σ Γ)  t T (_ : Σ;;; Γ |- t : T) =>
                               forall Γ', red1_ctx Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Δ wfΔ). {
          clearbody Δ; clear -X0.
          induction X0.
          - eexists; constructor.
          - destruct t0 as [? [? ?]].
            eexists; unshelve econstructor; tea.
            exact IHX0.π1.
            eexists; eassumption.
            exact IHX0.π2. eassumption.
          - destruct IHX0 as [X1 X2].
            destruct t0 as [s [Y1 Y2]], t1 as [Y3 Y4].
            eexists.
            unshelve econstructor; tea. eexists; eassumption.
            eauto. }
        eapply X with (Γ ,,, fix_context mfix) ZZ.π1; tea. exact ZZ.π2.
      + eapply All_impl; tea.
        intros; rdest; eauto.
    - assert (XX: red1_ctx Σ.1 (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix))
        by now eapply red1_ctx_app.
      econstructor; tea.
      + set (Δ := Γ ,,, fix_context mfix) in *.
        assert (ZZ: ∑ wfΔ, All_local_env_over typing
                            (fun Σ Γ (_ : wf_local Σ Γ)  t T (_ : Σ;;; Γ |- t : T) =>
                               forall Γ', red1_ctx Σ Γ Γ' -> Σ;;; Γ' |- t : T) Σ Δ wfΔ). {
          clearbody Δ; clear -X0.
          induction X0.
          - eexists; constructor.
          - destruct t0 as [? [? ?]].
            eexists; unshelve econstructor; tea.
            exact IHX0.π1.
            eexists; eassumption.
            exact IHX0.π2. eassumption.
          - destruct IHX0 as [X1 X2].
            destruct t0 as [s [Y1 Y2]], t1 as [Y3 Y4].
            eexists.
            unshelve econstructor; tea. eexists; eassumption.
            eauto. }
        eapply X with (Γ ,,, fix_context mfix) ZZ.π1; tea. exact ZZ.π2.
      + eapply All_impl; tea.
        intros; rdest; eauto.
    - econstructor.
      + now eapply X2.
      + destruct X3 as [[[ctx [s [H1 H2]]] X3]|X3]; [left|right].
        * cbn in *. exists ctx, s. split; eauto.
          eapply X; tea.
          now apply red1_ctx_app.
        * rdest; eauto.
      + eapply cumul_red_ctx; tea. now apply red1_red_ctx.
  Qed.


  Lemma wf_local_red1 {Σ Γ Γ'} :
    wf Σ.1 ->
    red1_ctx Σ.1 Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intro hΣ. induction 1; cbn in *.
    - intro e. inversion e; subst; cbn in *.
      constructor; tas. destruct X0 as [s Ht]. exists s.
      eapply subject_reduction1; tea.
    - intro e. inversion e; subst; cbn in *.
      destruct p as [[? []]|[? []]]; constructor; cbn; tas.
      + eapply subject_reduction1; tea.
      + destruct X0; eexists; eapply subject_reduction1; tea.
      + econstructor; tea.
        right; destruct X0; eexists; eapply subject_reduction1; tea.
        econstructor 2. eassumption. reflexivity.
    - intro H; inversion H; subst; constructor; cbn in *; auto.
      + destruct X1 as [s Ht]. exists s.
        eapply subject_reduction_ctx; tea.
      + destruct X1 as [s Ht]. exists s.
        eapply subject_reduction_ctx; tea.
      + eapply subject_reduction_ctx; tea.
  Qed.

  Lemma eq_context_upto_names_upto_names Γ Δ :
    eq_context_upto_names Γ Δ -> Γ ≡Γ Δ.
  Proof.
    induction 1; cbnr; try constructor; eauto.
    destruct x as [? [] ?], y as [? [] ?]; cbn in *; subst; inversion e.
    all: constructor; cbnr; eauto.
  Qed.


  Lemma wf_local_red {Σ Γ Γ'} :
    wf Σ.1 ->
    red_ctx Σ.1 Γ Γ' -> wf_local Σ Γ -> wf_local Σ Γ'.
  Proof.
    intros hΣ h. apply red_ctx_clos_rt_red1_ctx in h.
    induction h; eauto using wf_local_red1.
    apply eq_context_upto_names_upto_names in e.
    eauto using wf_local_alpha.
  Qed.


  Lemma wf_local_subst1 Σ (wfΣ : wf Σ.1) Γ na b t Γ' :
      wf_local Σ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_local Σ (Γ ,,, subst_context [b] 0 Γ').
  Proof.
    induction Γ' as [|d Γ']; [now inversion 1|].
    change (d :: Γ') with (Γ' ,, d).
    destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app in X. inversion X; subst; cbn in *; assumption.
      }
      constructor; cbn; auto.
      1: exists s. 1: unfold PCUICTerm.tSort.
      1: change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution_alt; tea.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *. destruct X0 as [s X0].
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subslet Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_def Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_local_app in X. inversion X; subst; cbn in *; assumption. }
      constructor; cbn; auto. exists s.
      unfold PCUICTerm.tSort.
      change (tSort s) with (subst [b] #|Γ'| (tSort s)).
      all: eapply substitution_alt; tea.
  Qed.


  Lemma red_ctx_app_context_l {Σ Γ Γ' Δ}
    : red_ctx Σ Γ Γ' -> red_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ as [|[na [bd|] ty] Δ]; [trivial| |];
      intro H; simpl; constructor; cbn; eauto; now apply IHΔ.
  Qed.


   Lemma isWfArity_red1 {Σ Γ A B} :
     wf Σ.1 ->
       red1 (fst Σ) Γ A B ->
       isWfArity typing Σ Γ A ->
       isWfArity typing Σ Γ B.
   Proof.
     intro wfΣ. induction 1 using red1_ind_all.
     all: intros [ctx [s [H1 H2]]]; cbn in *; try discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         [|rewrite ee in H1; discriminate].
       pose proof (subst_destArity [] b' [b] 0) as H; cbn in H.
       rewrite ee in H. eexists _, s'. split. eassumption.
       rewrite ee in H1. cbn in *. inversion H1; subst.
       rewrite app_context_assoc in H2.
       now eapply wf_local_subst1.
     - rewrite destArity_tFix in H1; discriminate.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. split; auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. split; auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHX. {
         eexists _, s'; split; tea. cbn in H1.
         inversion H1; subst. now rewrite app_context_assoc in H2. }
       destruct IHX as [ctx'' [s'' [ee' ?]]].
       eexists _, s''; split. cbn. rewrite destArity_app ee'. reflexivity.
       now rewrite app_context_assoc.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       eexists _, s'; split. cbn. rewrite destArity_app ee. reflexivity.
       cbn in H1. inversion H1; subst.
       eapply wf_local_red; try exact H2; tas.
       rewrite !app_context_assoc. apply red_ctx_app_context_l.
       constructor; cbn. reflexivity. auto.
     - rewrite destArity_app in H1.
       case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
         rewrite ee in H1; [|discriminate].
       forward IHX. {
         eexists _, s'; split; tea. cbn in H1.
         inversion H1; subst. now rewrite app_context_assoc in H2. }
       destruct IHX as [ctx'' [s'' [ee' ?]]].
       eexists _, s''; split. cbn. rewrite destArity_app ee'. reflexivity.
       now rewrite app_context_assoc.
   Qed.

   Lemma isWfArity_red {Σ Γ A B} :
     wf Σ.1 ->
     red (fst Σ) Γ A B ->
     isWfArity typing Σ Γ A ->
     isWfArity typing Σ Γ B.
   Proof.
     induction 2.
     - easy.
     - intro. now eapply isWfArity_red1.
   Qed.

   Lemma isWfArity_or_Type_red {Σ Γ A B} :
     wf Σ.1 ->
     red (fst Σ) Γ A B ->
     isWfArity_or_Type Σ Γ A ->
     isWfArity_or_Type Σ Γ B.
   Proof.
     intros ? ? [?|[? ?]]; [left|right].
     eapply isWfArity_red; eassumption.
     eexists. eapply subject_reduction; tea.
   Qed.

  Lemma type_reduction {Σ Γ t A B}
    : wf Σ.1 -> wf_local Σ Γ -> Σ ;;; Γ |- t : A -> red (fst Σ) Γ A B -> Σ ;;; Γ |- t : B.
  Proof.
    intros HΣ' HΓ Ht Hr.
    econstructor. eassumption.
    2: now eapply cumul_red_l'.
    destruct (validity_term HΣ' HΓ Ht).
    - left. eapply isWfArity_red; try eassumption.
    - destruct i as [s HA]. right.
      exists s. eapply subject_reduction; eassumption.
  Defined.

End SRContext.
