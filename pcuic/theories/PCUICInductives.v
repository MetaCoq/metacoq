(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSigmaCalculus PCUICInst PCUICContextSubst
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICEquality PCUICConfluence PCUICParallelReductionConfluence
     PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICParallelReduction PCUICWfUniverses PCUICSpine.
     
Require Import ssreflect ssrbool. 
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

Local Set SimplIsCbn.

Arguments subst_context !s _ !Γ.
Arguments it_mkProd_or_LetIn !l _.

Lemma nth_error_rev_map {A B} (f : A -> B) l i : 
  i < #|l| ->
  nth_error (rev_map f l) (#|l| - S i) = 
  option_map f (nth_error l i).
Proof.
  move=> Hi.
  rewrite rev_map_spec. rewrite -(map_length f l) -nth_error_rev ?map_length //.
  now rewrite nth_error_map.
Qed.

Hint Resolve conv_ctx_refl : pcuic.

(* Definition branch_type ind mdecl (idecl : one_inductive_body) params u p i (br : constructor_body) :=
  let inds := inds ind.(inductive_mind) u mdecl.(ind_bodies) in
  let '(id, t, ar) := br in
  let ty := subst0 inds (subst_instance u t) in
  match instantiate_params (subst_instance u mdecl.(ind_params)) params ty with
  | Some ty =>
  let '(sign, ccl) := decompose_prod_assum [] ty in
  let nargs := List.length sign in
  let allargs := snd (decompose_app ccl) in
  let '(paramrels, args) := chop mdecl.(ind_npars) allargs in
  let cstr := tConstruct ind i u in
  let args := (args ++ [mkApps cstr (paramrels ++ to_extended_list sign)]) in
  Some (ar, it_mkProd_or_LetIn sign (mkApps (lift0 nargs p) args))
| None => None
end.

Lemma nth_branches_type ind mdecl idecl args u p i t btys : map_option_out (build_branches_type ind mdecl idecl args u p) = Some btys ->
  nth_error btys i = Some t -> 
  (∑ br, (nth_error idecl.(ind_ctors) i = Some br) /\
    (branch_type ind mdecl idecl args u p i br = Some t)).
Proof.
  intros Htys Hnth.
  eapply nth_map_option_out in Htys; eauto.
Qed.

Lemma build_branches_type_lookup {cf:checker_flags} Σ Γ ind mdecl idecl cdecl pars u p (brs :  list (nat * term)) btys : 
  declared_inductive Σ.1 ind mdecl idecl ->
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

Import PCUICEnvironment.

Lemma branch_type_spec {cf:checker_flags} Σ ind mdecl idecl cdecl pars u p c nargs bty : 
  declared_inductive Σ ind mdecl idecl ->
  forall (omib : on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl),
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl),
  forall cdecl (cs : on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind ind) idecl (ind_indices idecl) cdecl cdecl),
  branch_type ind mdecl idecl pars u p c cdecl = Some (nargs, bty) ->
  nargs = context_assumptions cdecl.(cstr_args) /\
  forall parsubst, 
  context_subst (subst_instance u (PCUICAst.ind_params mdecl)) pars parsubst ->
  let indsubst := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  let nargs' := #|cdecl.(cstr_args)| in
  let npars := #|ind_params mdecl| in
  let substargs := (subst_context parsubst 0 
    (subst_context indsubst npars (map_context (subst_instance u) cdecl.(cstr_args)))) in
  bty = 
  it_mkProd_or_LetIn substargs
    (mkApps (lift0 nargs' p)
      (map (subst parsubst nargs' ∘ subst indsubst (nargs' + npars) ∘ subst_instance u) cdecl.(cstr_indices) ++ 
       [mkApps (tConstruct ind c u)
         (map (lift0 nargs') pars ++         
          to_extended_list substargs)])).
Proof.
  move=> decli onmib [] indices ps aeq onAr indsorts onC onP inds onIndices.
  intros cs onc brty. simpl in *.
  simpl in onc.
  clear onP.
  assert(lenbodies: inductive_ind ind < #|ind_bodies mdecl|).
  { destruct decli as [_ Hnth]. now apply nth_error_Some_length in Hnth. }
  clear decli.
  destruct onc. simpl in *.
  destruct cs as [args indi csort] => /=. simpl in *. 
  rewrite cstr_eq in on_ctype.
  unfold branch_type in brty.
  destruct cdecl as [[id ty] nargs'']. simpl in * |-.
  destruct instantiate_params eqn:Heq => //.
  eapply instantiate_params_make_context_subst in Heq.
  destruct Heq as [ctx' [ty'' [s' [? [? ?]]]]].
  subst t. move: H.
  rewrite {1}cstr_eq subst_instance_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
  rewrite -(subst_context_length (PCUICTyping.inds (inductive_mind ind) u (ind_bodies mdecl)) 0).
  rewrite decompose_prod_n_assum_it_mkProd.
  move=> H;noconf H.
  move: brty.

  rewrite !subst_context_length !subst_instance_length
    subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn.
  rewrite subst_context_length subst_instance_length Nat.add_0_r.
  rewrite subst_instance_mkApps !subst_mkApps.
  rewrite Nat.add_0_r.
  assert((subst s' #|args|
  (subst
     (PCUICTyping.inds (inductive_mind ind) u
        (PCUICAst.ind_bodies mdecl))
     (#|args| + #|PCUICAst.ind_params mdecl|)
     (subst_instance u cstr_concl_head))) = tInd ind u).
  rewrite /head. simpl subst_instance.
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
  move=> Heq; simpl in Heq; move: Heq.
  rewrite !map_map_compose map_app.
  rewrite chop_n_app.
  rewrite map_length to_extended_list_k_length.
  by rewrite (onmib.(onNpars)).

  move=> [=] Hargs Hbty. subst nargs. split;auto. rewrite -Hbty.
  clear Hbty bty.
  rewrite app_nil_r.
  move=>parsubst Hpars.
  pose proof (make_context_subst_spec _ _ _ H0) as csubst.
  rewrite rev_involutive in csubst.
  pose proof (context_subst_fun csubst Hpars). subst s'. clear csubst.
  f_equal.
  rewrite !subst_context_length subst_instance_length.
  f_equal. f_equal. f_equal. f_equal.
  f_equal. rewrite -(map_map_compose _ _ _ _ (subst _ _ ∘ subst _ _)).
  rewrite subst_instance_to_extended_list_k.
  rewrite -map_map_compose.
  rewrite -to_extended_list_k_map_subst. rewrite subst_instance_length; lia.
  now rewrite (subst_to_extended_list_k _ _ pars).
Qed. *)

Lemma instantiate_inds {cf:checker_flags} Σ u mind mdecl :
  wf Σ.1 ->
  declared_minductive Σ.1 mind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  subst_instance u
     (inds mind (PCUICLookup.abstract_instance (PCUICEnvironment.ind_universes mdecl))
        (ind_bodies mdecl)) = 
  inds mind u (ind_bodies mdecl).
Proof.
  intros wfΣ declm cu.
  rewrite subst_instance_inds.  
  f_equal. eapply subst_instance_id_mdecl; eauto.
Qed.

Lemma subst_inds_concl_head ind u mdecl (arity : context) :
  let head := tRel (#|ind_bodies mdecl| - S (inductive_ind ind) + #|ind_params mdecl| + #|arity|) in
  let s := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  inductive_ind ind < #|ind_bodies mdecl| ->
  subst s (#|arity| + #|ind_params mdecl|)
        (subst_instance u head)
  = tInd ind u.
Proof.
  intros.
  subst head. simpl subst_instance.
  rewrite (subst_rel_eq _ _ (#|ind_bodies mdecl| - S (inductive_ind ind)) (tInd ind u)) //; try lia.
  subst s. rewrite inds_spec rev_mapi nth_error_mapi /=.
  elim nth_error_spec. 
  + intros. simpl.
    f_equal. destruct ind; simpl. f_equal. f_equal. simpl in H. lia.
  + rewrite List.rev_length. lia.
Qed.

Section OnInductives.
  Context {cf : checker_flags} {Σ : global_env} {wfΣ : wf Σ} {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).
  
  Lemma on_minductive_wf_params_indices : wf_local (Σ, ind_universes mdecl) (ind_params mdecl ,,, ind_indices idecl).
  Proof.
    eapply on_declared_inductive in decli as [onmind oib].
    pose proof (oib.(onArity)).
    rewrite oib.(ind_arity_eq) in X.
    destruct X as [s Hs].
    rewrite -it_mkProd_or_LetIn_app in Hs.
    eapply it_mkProd_or_LetIn_wf_local in Hs. 
    now rewrite app_context_nil_l in Hs. now simpl.
  Qed.
End OnInductives.

Lemma isType_intro {cf:checker_flags} {Σ Γ T s} : Σ ;;; Γ |- T : tSort s -> isType Σ Γ T.
Proof.
  now intros Hty; exists s.
Qed.
Hint Resolve isType_intro : pcuic.

Section OnInductives.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {mdecl ind idecl}
    (decli : declared_inductive Σ ind mdecl idecl).
  
  Lemma on_minductive_wf_params_indices_inst (u : Instance.t) :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_local Σ (subst_instance u (ind_params mdecl ,,, ind_indices idecl)).
  Proof.
    intros.
    eapply (wf_local_instantiate _ (InductiveDecl mdecl)); eauto. eapply decli.
    now eapply on_minductive_wf_params_indices.
  Qed.
  
  Lemma on_inductive_inst Γ u :
    wf_local Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    isType Σ Γ (it_mkProd_or_LetIn (subst_instance u (ind_params mdecl ,,, idecl.(ind_indices)))
          (tSort (subst_instance_univ u idecl.(ind_sort)))).
  Proof.
    move=> wfΓ cext.
    destruct (on_declared_inductive decli) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    rewrite oib.(ind_arity_eq) in ar. 
    destruct ar as [s ar].
    eapply isType_weaken => //.
    rewrite -(subst_instance_it_mkProd_or_LetIn u _ (tSort _)).
    rewrite -it_mkProd_or_LetIn_app in ar.
    eapply (typing_subst_instance_decl Σ [] _ _ _ (InductiveDecl mdecl) u) in ar.
    all:pcuic. eapply decli.
  Qed.
  
  Lemma on_inductive_isType Γ u :
    wf_local Σ Γ ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    isType Σ Γ (subst_instance u idecl.(ind_type)).
  Proof.
    move=> wfΓ cext.
    destruct (on_declared_inductive decli) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    destruct ar as [s ar].
    eapply isType_weaken => //.
    eapply (typing_subst_instance_decl Σ [] _ _ _ (InductiveDecl mdecl) u) in ar.
    all:pcuic. eapply decli.
  Qed.
  
  Local Definition oi := (on_declared_inductive decli).1. 
  Local Definition oib := (on_declared_inductive decli).2. 

  Lemma on_inductive_sort : wf_universe (Σ.1, ind_universes mdecl) (ind_sort idecl).
  Proof.
    pose proof (oib.(onArity)) as ar.
    rewrite oib.(ind_arity_eq) in ar.
    destruct ar as [s ar].
    eapply typing_wf_universes in ar; auto.
    move/andP: ar => [].
    rewrite wf_universes_it_mkProd_or_LetIn => /andP [] _.
    now rewrite wf_universes_it_mkProd_or_LetIn => /andP [] _ /= /wf_universe_reflect.
  Qed.

  Lemma on_inductive_sort_inst u :
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_universe Σ (subst_instance u (ind_sort idecl)).
  Proof.
    generalize on_inductive_sort => wf.
    destruct Σ. intros cu.
    eapply wf_universe_instantiate; eauto.
    now eapply consistent_instance_ext_wf.
    eapply sub_context_set_trans.
    eapply (weaken_lookup_on_global_env'' _ _ (InductiveDecl mdecl)); eauto.
    eapply decli.
    eapply global_context_set_sub_ext.
  Qed.

  Lemma nth_errror_arities_context decl : 
    nth_error (arities_context (ind_bodies mdecl)) (#|ind_bodies mdecl| - S (inductive_ind ind)) = Some decl ->
    decl.(decl_type) = idecl.(ind_type).
  Proof.
    unfold arities_context.
    rewrite nth_error_rev_map.
    destruct decli as [declm decli'].
    now apply nth_error_Some_length in decli'.
    destruct nth_error eqn:Heq; try discriminate.
    destruct decli. rewrite H0 in Heq. noconf Heq.
    simpl. move=> [] <-. now simpl.
  Qed.
End OnInductives.

(** * Projections *)

Fixpoint projs_inst ind npars k x : list term :=
  match k with
  | 0 => []
  | S k' => tProj (ind, npars, k') x :: projs_inst ind npars k' x
  end.

Lemma subst_instance_projs u i p n :
  map (subst_instance u) (projs i p n) = projs i p n.
Proof.
  induction n; simpl; auto. f_equal; auto.
Qed.

Lemma projs_inst_subst s k i pars arg t :
  map (subst s k) (projs_inst i pars arg t)  =
  projs_inst i pars arg (subst s k t).
Proof.
  induction arg; simpl; auto.
  f_equal; auto.
Qed.

Lemma projs_inst_skipn {i pars arg t} n :
  skipn n (projs_inst i pars arg t) = projs_inst i pars (arg - n) t.
Proof.
  induction arg in n |- *; simpl; auto.
  - now rewrite skipn_nil.
  - destruct n as [|n']; [rewrite skipn_0|rewrite skipn_S] => //.
    rewrite IHarg /= //.
Qed.

Lemma subslet_projs {cf:checker_flags} (Σ : global_env_ext) i mdecl idecl :
  forall (wfΣ : wf Σ.1) 
  (Hdecl : declared_inductive Σ.1 i mdecl idecl),
  match ind_ctors idecl return Type with
  | [cs] => 
    on_projections mdecl (inductive_mind i) (inductive_ind i) 
     idecl (ind_indices idecl) cs -> 
     forall Γ t u,
     let indsubst := inds (inductive_mind i) u (ind_bodies mdecl) in
     untyped_subslet Γ
     (projs_inst i (ind_npars mdecl) (context_assumptions (cstr_args cs)) t)
     (smash_context []
        (subst_context (inds (inductive_mind i) u (ind_bodies mdecl))
           #|ind_params mdecl| (subst_instance u (cstr_args cs))))
  | _ => True
  end.
Proof.
  intros wfΣ Hdecl.
  destruct ind_ctors as [|cs []] eqn:Heq; trivial.
  intros onp. simpl. intros Γ t u. 
  rewrite (smash_context_subst []).
  destruct onp.
  assert (#|PCUICEnvironment.ind_projs idecl| >=
  PCUICEnvironment.context_assumptions (cstr_args cs)). lia.
  clear on_projs_all.
  induction (cstr_args cs) as [|[? [] ?] ?].
  - simpl. constructor.
  - simpl. apply IHc. now simpl in H.
  - simpl. rewrite smash_context_acc /=.
    rewrite subst_context_snoc.
    rewrite /subst_decl {2}/map_decl /=.
    simpl in H. constructor. apply IHc. lia.
Qed.

Lemma skipn_projs n i npars k : 
  skipn n (projs i npars k) = projs i npars (k - n).
Proof.
  induction k in n |- *; simpl.
  - now rewrite skipn_nil.
  - destruct n. now rewrite skipn_0.
    now  rewrite skipn_S.
Qed.

Lemma subst_projs_inst ind npars k x : map (subst0 [x]) (projs ind npars k) = projs_inst ind npars k x.
Proof.
  induction k; simpl; auto. unfold Nat.sub. simpl.
  rewrite lift0_id. f_equal; auto.
Qed.

Lemma projs_inst_length ind npars k x : #|projs_inst ind npars k x| = k.
Proof. induction k; simpl; auto. lia. Qed.

Hint Rewrite projs_inst_length : len.

Lemma projs_inst_lift ind npars k x n : 
  projs_inst ind npars k (lift0 n x) = 
  map (lift0 n) (projs_inst ind npars k x).
Proof.
  induction k; simpl; auto.
  f_equal; auto.
Qed.

Lemma projs_subst_instance u ind npars k :
  map (subst_instance u) (projs ind npars k) = projs ind npars k.
Proof.
  induction k; simpl; auto. f_equal; auto.
Qed.

Lemma projs_subst_above s (n : nat) ind npars k : n > 0 ->
  map (subst s n) (projs ind npars k) = projs ind npars k.
Proof.
  induction k; simpl; auto. intros.
  f_equal; auto. elim: Nat.leb_spec => //; lia.
Qed.

Lemma nth_error_projs_inst ind npars k x n :
  n < k ->
  nth_error (projs_inst ind npars k x) n = Some (tProj (ind, npars, k - S n) x).
Proof.
  induction k in n |- *; simpl; auto. lia.
  destruct n.
  + simpl. now rewrite Nat.sub_0_r.
  + intros Hlt. simpl. apply IHk; lia.  
Qed.


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

Definition projection_decls_type mdecl ind k ty := 
  let u := PCUICLookup.abstract_instance (PCUICEnvironment.ind_universes mdecl) in
  let indsubst := inds (inductive_mind ind) u (ind_bodies mdecl) in
  let projsubst := projs ind (ind_npars mdecl) k in
  subst indsubst (S (ind_npars mdecl))
      (subst0 projsubst (lift 1 k ty)).

Lemma on_projections_decl {cf:checker_flags} {mdecl ind idecl cs} :
  let u := PCUICLookup.abstract_instance (ind_universes mdecl) in
  on_projections mdecl (inductive_mind ind) (inductive_ind ind) idecl (idecl.(ind_indices)) cs ->
  Alli (fun i decl => 
    ∑ pdecl, 
      (nth_error (ind_projs idecl) (context_assumptions (cstr_args cs) - S i) = Some pdecl))
    0 (smash_context [] cs.(cstr_args)).
Proof.
  intros.
  destruct X as [_ _ _ on_projs_all on_projs].
  eapply forall_nth_error_Alli.
  intros.
  pose proof (snd (nth_error_Some' (ind_projs idecl) (context_assumptions (cstr_args cs) - S i))).
  apply X. eapply nth_error_Some_length in H. 
    autorewrite with len in H. simpl in H; lia.
Qed.

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
  destruct (snd (nth_error_Some' s x) H). rewrite e.
  subst s.
  rewrite /to_extended_list /to_extended_list_k in e.
  rewrite List.rev_length in cl, H. autorewrite with len in *.
  rewrite reln_alt_eq in e.
  rewrite app_nil_r List.rev_involutive in e.
  clear -ass e. revert e.
  rewrite -{2}(Nat.add_0_r x).
  generalize 0.
  induction Γ in x, ass, x0 |- * => n. 
  - simpl in *. rewrite nth_error_nil => //.
  - depelim ass; simpl.
    destruct x; simpl in *; try congruence.
    move=> e; specialize (IHΓ ass); simpl in e.
    specialize (IHΓ _ _ _ e). subst x0. f_equal. lia.
Qed.


(* Well, it's a smash_context mess! *)
Lemma declared_projections {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl} : 
  forall (wfΣ : wf Σ.1) (Hdecl : declared_inductive Σ ind mdecl idecl),
  let u := PCUICLookup.abstract_instance (ind_universes mdecl) in
  match ind_ctors idecl return Type with
  | [cs] => 
    on_projections mdecl (inductive_mind ind) (inductive_ind ind) 
      idecl (ind_indices idecl) cs -> 
    Alli (fun i pdecl => 
    isType (Σ.1, ind_universes mdecl)
      ((vass {| binder_name := nAnon; binder_relevance := idecl.(ind_relevance) |}
         (mkApps (tInd ind u) 
            (to_extended_list (smash_context [] (ind_params mdecl)))))::
          smash_context [] (ind_params mdecl)) pdecl.2 * 
      ∑ decl, 
        (nth_error (smash_context [] (cstr_args cs)) 
          (context_assumptions (cstr_args cs) - S i) = Some decl) *
        wf_local (Σ.1, ind_universes mdecl) 
          (arities_context (ind_bodies mdecl) ,,, 
            ind_params mdecl ,,, smash_context [] (cstr_args cs)) *
        (projection_type mdecl ind i decl.(decl_type) = pdecl.2) *
        (projection_type mdecl ind i decl.(decl_type) = 
            projection_type' mdecl ind  i decl.(decl_type)))%type
      0 (ind_projs idecl)
  | _ => True
  end.
Proof.
  intros wfΣ decli u.
  set oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ decli.
  set indb := {| binder_name := _ |}.
  destruct (ind_ctors idecl) as [|? []] eqn:Heq; try contradiction; auto.
  intros onps.
  eapply forall_nth_error_Alli.
  set (eos := CoreTactics.the_end_of_the_section).
  intros i. Subterm.rec_wf_rel IH i lt. clear eos.
  rename pr1 into i. simpl; clear H0.
  set (p := ((ind, ind_npars mdecl), i)).
  intros pdecl Hp. simpl.
  set(isdecl := (conj decli (conj Hp eq_refl)) :
      declared_projection Σ.1 p mdecl idecl pdecl).
  destruct (on_declared_projection isdecl) as [oni onp].
  set (declared_inductive_inv _ _ _ _) as oib' in onp.
  rewrite Heq in onp.
  change oib' with oib in *. clear oib'.
  simpl in onp.
  have onpars := onParams (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ decli.p1).
  have parslen := onNpars (declared_minductive_inv weaken_env_prop_typing wfΣ wfΣ decli.p1).
  simpl in onp.
  destruct onp as [[[wfargs onProjs] Hp2] onp].
  red in onp.
  destruct (nth_error (smash_context [] _) _) eqn:Heq'; try contradiction.
  destruct onp as [onna onp].
  rewrite {}onp.
  apply on_projections_decl in onps.
  assert(projslen : #|ind_projs idecl| = (context_assumptions (cstr_args c))).
  { now destruct onProjs. }
  assert (some_proj :#|ind_projs idecl| > 0).
  { destruct isdecl as [ [] []]. now apply nth_error_Some_length in H1. }
  simpl.
  assert (wfarities : wf_local (Σ.1, ind_universes mdecl)
      (arities_context (ind_bodies mdecl))).
  { eapply wf_arities_context; eauto. }
  destruct (ind_cunivs oib) as [|? []] eqn:hequ => //.
  eapply PCUICClosed.sorts_local_ctx_All_local_env in wfargs.
  2:{ eapply All_local_env_app. split; auto.
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
  assert (parsu : subst_instance u (ind_params mdecl) = ind_params mdecl). 
  { red in onpars. eapply (subst_instance_id (Σ.1, ind_universes mdecl)). eauto.
    eapply declared_inductive_wf_ext_wk; eauto with pcuic. auto. }
  assert (sortu : subst_instance u (ind_sort idecl) = ind_sort idecl).
  { apply (subst_instance_ind_sort_id Σ mdecl ind idecl); eauto. }
  pose proof (spine_subst_to_extended_list_k (Σ.1, ind_universes mdecl)
    (ind_params mdecl) []).
  forward X; auto.
  forward X. rewrite app_context_nil_l; auto.
  rewrite app_context_nil_l in X.
  rewrite closed_ctx_lift in X.
  red in onpars. eapply closed_wf_local; [|eauto]. auto.
  assert(wf_local (Σ.1, ind_universes mdecl) (ind_params mdecl ,,
      vass {| binder_name := nAnon; binder_relevance := idecl.(ind_relevance) |}  (mkApps (tInd ind u) (to_extended_list (ind_params mdecl))))).
  { constructor. auto. red. exists (ind_sort idecl).
    eapply type_mkApps. econstructor; eauto.
    destruct isdecl as []; eauto. subst u.
    eapply consistent_instance_ext_abstract_instance; eauto with pcuic.
    eapply declared_inductive_wf_global_ext; eauto with pcuic.
    rewrite (ind_arity_eq oib).
    rewrite subst_instance_it_mkProd_or_LetIn.
    rewrite -(app_nil_r (to_extended_list _)).
    eapply typing_spine_it_mkProd_or_LetIn'; auto.
    rewrite parsu. eapply X.
    constructor. pose proof (onArity oib).
    eapply isType_Sort. 2:pcuic.
    eapply on_inductive_sort; eauto.
    simpl in oib.
    pose proof (onProjs.(on_projs_noidx _ _ _ _ _ _)).
    destruct (ind_indices idecl); simpl in H; try discriminate.
    simpl. rewrite [subst_instance_univ _ _]sortu. reflexivity.
    rewrite -subst_instance_it_mkProd_or_LetIn.
    pose proof (onArity oib). rewrite -(oib.(ind_arity_eq)).
    destruct X0 as [s Hs]. exists s.
    eapply (weaken_ctx (Γ:=[])); auto.
    rewrite (subst_instance_ind_type_id Σ.1 _ ind); auto. }
  intros wf.
  generalize (weakening_wf_local (Γ'':=[_]) wf X0).
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
  rewrite lift_context_length /=.
  simpl. unfold app_context. simpl.
  rewrite lift_context_snoc /= /lift_decl /map_decl /=.
  simpl. rewrite lift_mkApps. simpl.
  rewrite {3}/subst_context /fold_context_k /= /map_decl /= subst_mkApps /=.
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
    eapply declared_minductive_closed_inds. eauto. }
  rewrite -app_assoc in wfl.
  apply All_local_env_app_inv in wfl as [wfctx wfsargs].
  rewrite smash_context_app in Heq'.
  rewrite smash_context_acc in Heq'. 
  rewrite nth_error_app_lt in Heq'.
  autorewrite with len. lia.
  set (idx := context_assumptions (cstr_args c) - S i) in *.
  unshelve epose proof (nth_error_All_local_env (n:=idx) _ wfsargs).
  autorewrite with len. simpl. lia. 
  destruct (nth_error (subst_context _ 1 _) idx) as [c2|] eqn:hidx.
  simpl in X0. red in X0. cbn in X0.
  assert(decl_body c2 = None).
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
  rewrite (nth_error_lift_context_eq _ [vass indb (mkApps (tInd ind u) [])]) in hidx.
  simpl in hidx. autorewrite with len in hidx.
  rewrite nth_error_subst_context in hidx. autorewrite with len in hidx.
  simpl in hidx.
  rewrite !option_map_two in hidx.
  assert(clarg : closedn (i + #|ind_params mdecl| + #|ind_bodies mdecl|) (decl_type arg)).
  { assert(wf_local (Σ.1, ind_universes mdecl)
      (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, 
      smash_context [] (cstr_args c))).
    apply All_local_env_app; split; auto.
    now apply All_local_env_app_inv in wfargs as [wfindpars wfargs].
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
  assert(context_assumptions (cstr_args c) - S idx = i) as -> by lia.
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
    replace (context_assumptions (cstr_args c) - S idx + 1) with
    (context_assumptions (cstr_args c) - idx) by lia.
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
    eapply (declared_minductive_closed_inds decli). 
    simpl. eapply subject_closed in Hs.
    now rewrite /indsubst inds_length. auto. }
  split.
  unfold projection_type in H0.
  rewrite H0. exists s; auto. red.
  rewrite -/indb in Hs.
  rewrite /projection_type' -/indb -/indsubst -/projsubst.
  now rewrite Nat.add_1_r in Hs.
  exists arg. intuition auto.

  apply wf_local_smash_end; auto.

  unfold projsubst. clear Hs.
  clear -wfΣ parslen onps projslen some_proj IH Hp2 decli.
  rewrite (smash_context_lift []).
  rewrite (smash_context_subst []).
  rewrite -(firstn_skipn (S idx) (smash_context [] (cstr_args c))).
  rewrite subst_context_app lift_context_app subst_context_app.
  autorewrite with len.
  rewrite skipn_all_app_eq.
  autorewrite with len.
  rewrite firstn_length_le; auto. rewrite smash_context_length.
  simpl. lia.
  induction i. subst idx.
  - assert (S (context_assumptions (cstr_args c) - 1) =
      (context_assumptions (cstr_args c))) as -> by lia.
    rewrite skipn_all2.
    autorewrite with len; simpl; auto.
    constructor.
  - forward IHi.
    intros. eapply (IH i0). lia. auto. 
    forward IHi by lia. simpl in IHi.
    subst idx.
    destruct (skipn (S (context_assumptions (cstr_args c) - S (S i))) 
      (smash_context [] (cstr_args c))) eqn:eqargs.
    apply (f_equal (@length _)) in eqargs.
    autorewrite with len in eqargs.
    rewrite skipn_length in eqargs. autorewrite with len. simpl; lia.
    autorewrite with len in eqargs. simpl in eqargs. lia.
    rewrite subst_context_snoc lift_context_snoc subst_context_snoc.
    simpl.
    destruct c0 as [? [] ?].
    * simpl in eqargs.
      pose proof (@smash_context_assumption_context [] (cstr_args c)).
      forward H by constructor.
      eapply assumption_context_skipn in H.
      rewrite -> eqargs in H. elimtype False; inv H.
    * apply skipn_eq_cons in eqargs as [Hnth eqargs].
      constructor.
      + replace (S (S (context_assumptions (cstr_args c) - S (S i)))) 
          with (S (context_assumptions (cstr_args c) - S i)) in eqargs by lia.
        rewrite eqargs in IHi. apply IHi.
      + rewrite /lift_decl /=.
        autorewrite with len.
        specialize (IH i ltac:(lia)).
        autorewrite with len.
        eapply (f_equal (@length _)) in eqargs.
        rewrite skipn_length in eqargs.
        autorewrite with len. simpl; lia.
        autorewrite with len in eqargs. simpl in eqargs.
        eapply nth_error_alli in onps; eauto. simpl in onps.
        destruct onps as [pdecl Hnth'].
        replace ((context_assumptions (cstr_args c) - 
          S (S (context_assumptions (cstr_args c) - S (S i)))))
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
        assert(subst_instance u pdecl.2 = pdecl.2) as ->.
        { eapply (isType_subst_instance_id (Σ.1, ind_universes mdecl)); eauto with pcuic.
          eapply declared_inductive_wf_ext_wk; eauto with pcuic. }
        destruct IH as [isTy [decl [[[nthdecl _] eqpdecl] ptyeq]]].
        move ptyeq at bottom. 
        replace  (S (context_assumptions (cstr_args c) - S (S i))) with 
          (context_assumptions (cstr_args c) - S i) in Hnth by lia.
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
          decl_name := indb;
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

Lemma declared_projection_type {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p pdecl} : 
  wf Σ.1 ->
  declared_projection Σ p mdecl idecl pdecl ->
  let u := PCUICLookup.abstract_instance (ind_universes mdecl) in    
  isType (Σ.1, ind_universes mdecl)
    ((vass {| binder_name := nAnon; binder_relevance := idecl.(ind_relevance) |} (mkApps (tInd p.1.1 u) 
          (to_extended_list (smash_context [] (ind_params mdecl)))))::
        smash_context [] (ind_params mdecl)) pdecl.2.
Proof.
  intros wfΣ declp.
  destruct (on_declared_projection declp) as [oni onp].
  specialize (declared_projections wfΣ (let (x, _) := declp in x)).
  set(oib := declared_inductive_inv _ _ _ _) in *.
  intros onprojs u.
  clearbody oib.
  simpl in *.
  destruct (ind_ctors idecl) as [|? []] => //.
  destruct onp as [[[? ?] ?] ?].
  destruct (ind_cunivs oib) as [|? []] => //.
  forward onprojs. intuition auto.
  destruct declp as [decli [Hnth Hpars]].
  eapply nth_error_alli in onprojs; eauto.
  simpl in onprojs. intuition auto.
Qed.

Lemma declared_projection_type_and_eq {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p pdecl} : 
  forall (wfΣ : wf Σ.1) (Hdecl : declared_projection Σ p mdecl idecl pdecl),
  let u := PCUICLookup.abstract_instance (ind_universes mdecl) in
  let oib := declared_inductive_inv weaken_env_prop_typing wfΣ wfΣ (let (x, _) := Hdecl in x) in
  match ind_ctors idecl return Type with
  | [cs] => 
    isType (Σ.1, ind_universes mdecl)
      ((vass {| binder_name := nAnon; binder_relevance := idecl.(ind_relevance) |}
       (mkApps (tInd p.1.1 u) 
            (to_extended_list (smash_context [] (ind_params mdecl)))))::
        smash_context [] (ind_params mdecl)) pdecl.2 *
    ∑ decl, 
    (nth_error (smash_context [] (cstr_args cs)) 
      (context_assumptions (cstr_args cs) - S p.2) = Some decl) *
    (wf_local (Σ.1, ind_universes mdecl) 
        (arities_context (ind_bodies mdecl) ,,, 
          ind_params mdecl ,,, smash_context [] (cstr_args cs))) *
    (projection_type mdecl p.1.1 p.2 decl.(decl_type) = pdecl.2) *
    (projection_type mdecl p.1.1 p.2 decl.(decl_type) = 
      projection_type' mdecl p.1.1 p.2 decl.(decl_type))%type
| _ => False
  end.
Proof.
  intros wfΣ declp.
  destruct (on_declared_projection declp) as [oni onp].
  specialize (declared_projections wfΣ (let (x, _) := declp in x)).
  set(oib := declared_inductive_inv _ _ _ _) in *.
  intros onprojs u.
  clearbody oib.
  destruct (ind_ctors idecl) as [|? []] => //.
  destruct onp as [[[? ?] ?] ?].
  set (cu := ind_cunivs _) in y.
  destruct cu as [|? []] in y => //. simpl in *.
  forward onprojs. intuition auto.
  destruct declp as [decli [Hnth Hpars]].
  eapply nth_error_alli in onprojs; eauto.
  simpl in onprojs. intuition auto.
Qed.

Definition projection_context mdecl idecl ind u := 
  smash_context [] (subst_instance u (ind_params mdecl)),,
  vass ({| binder_name := nNamed (ind_name idecl); binder_relevance := idecl.(ind_relevance) |})
      (mkApps (tInd ind u) (to_extended_list (smash_context [] 
        (subst_instance u (ind_params mdecl))))).

Lemma type_local_ctx_cum {cf:checker_flags} {Σ Γ Δ s s'} : 
  wf Σ.1 -> wf_universe Σ s' ->
  leq_universe (global_ext_constraints Σ) s s' ->
  type_local_ctx (lift_typing typing) Σ Γ Δ s ->
  type_local_ctx (lift_typing typing) Σ Γ Δ s'.
Proof.
  intros wfΣ wfs leqs.
  induction Δ as [|[na [b|] ty] Δ]; simpl; auto;
  intros []; split; auto.
  eapply type_Cumul; eauto.
  econstructor; pcuic.
  now do 2 constructor.
Qed.
 
Lemma type_local_ctx_wf {cf:checker_flags} {Σ Γ Δ s} : 
  wf Σ.1 -> 
  type_local_ctx (lift_typing typing) Σ Γ Δ s -> 
  wf_universe Σ s.
Proof.
  intros wfΣ.
  induction Δ as [|[na [b|] ty] Δ]; simpl; intuition auto.
Qed.

Lemma isType_it_mkProd_or_LetIn {cf:checker_flags} Σ Γ Δ s s': 
  wf Σ.1 ->
  wf_local Σ Γ ->
  type_local_ctx (lift_typing typing) Σ Γ Δ s ->
  wf_universe Σ s' ->
  isType Σ Γ (it_mkProd_or_LetIn Δ (tSort s')).
Proof.
  move=> wfΣ wfΓ wfΔ wfs.
  eapply isType_intro.
  eapply type_it_mkProd_or_LetIn. eauto.
  eapply type_local_ctx_wf; eauto. eauto.
  econstructor; pcuic.
  eapply type_local_ctx_All_local_env; eauto.
Qed.

Lemma isType_it_mkProd_or_LetIn_inv {cf:checker_flags} Σ Γ Δ s :
  wf Σ.1 ->
  isType Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) ->
  isType Σ (Γ ,,, Δ) (tSort s).
Proof.
  move=> wfΣ [u Hu].
  exists u. unfold PCUICTypingDef.typing in *.
  now eapply inversion_it_mkProd_or_LetIn in Hu.
Qed.

Lemma subst_lift1 x s : (subst0 (x :: s) ∘ lift0 1) =1 subst0 s.
Proof.
  intros t. erewrite <- subst_skipn'.
  rewrite lift0_id. simpl. now rewrite skipn_S skipn_0.
  lia. simpl. lia.
Qed.

Lemma map_subst_lift1 x s l : map (subst0 (x :: s) ∘ lift0 1) l = map (subst0 s) l.
Proof.
  apply map_ext. apply subst_lift1.
Qed.
 
Lemma context_subst_to_extended_list_k {cf:checker_flags} Σ Δ :
  wf Σ.1 ->
  wf_local Σ Δ ->
  context_subst Δ
    (map (subst0 (extended_subst Δ 0)) (to_extended_list_k Δ 0))
      (extended_subst Δ 0).
Proof.
  move=> wfΣ wfΔ.
  generalize 0 at 1 4.
  induction Δ as [|[na [d|] ?] ?] in wfΔ |- *; simpl; auto;
  depelim wfΔ.
  * intros n. rewrite extended_subst_length. rewrite lift_closed.
    red in l0. autorewrite with len. now eapply subject_closed in l0.
    rewrite (reln_lift 1 0).
    rewrite map_map_compose map_subst_lift1.
    autorewrite with len.
    constructor. apply IHΔ; auto.
  * intros n. rewrite reln_acc.
    simpl.
    rewrite reln_acc /= map_app app_nil_r.
    rewrite (reln_lift 1 0).
    rewrite map_map_compose map_subst_lift1.
    simpl. constructor. now apply IHΔ.
Qed.

Lemma subslet_extended_subst {cf:checker_flags} Σ Δ :
  wf Σ.1 ->
  wf_local Σ Δ ->
  subslet Σ (smash_context [] Δ) (extended_subst Δ 0) Δ.
Proof.
  move=> wfΣ wfΔ.
  induction Δ as [|[na [d|] ?] ?] in wfΔ |- *; simpl; auto; depelim wfΔ.
  * rewrite extended_subst_length. rewrite lift_closed.
    red in l0. autorewrite with len. now eapply subject_closed in l0.
    constructor. auto. specialize (IHΔ wfΔ).
    red in l0.
    eapply weaken_ctx in l0. 3:eapply wf_local_smash_context; eauto. 2:auto.
    eapply (substitution _ _ _ _ []) in l0. eapply l0. all:auto.
  * rewrite smash_context_acc. simpl.
    rewrite /map_decl /= /map_decl /=. simpl.
    destruct l as [s Hs].
    rewrite lift_closed. now eapply subject_closed in Hs.    
    constructor.
    rewrite (lift_extended_subst _ 1).
    rewrite -{4}(closed_ctx_lift 1 0 Δ). now eapply closed_wf_local.
    eapply (subslet_lift _ _ [_]); eauto.
    constructor. eapply wf_local_smash_context; auto.
    exists s.
    eapply weaken_ctx in Hs. 3:eapply wf_local_smash_context; eauto. 2:auto.
    eapply (substitution _ _ _ _ []) in Hs. eapply Hs. all:auto.
    eapply refine_type.
    econstructor. constructor. apply wf_local_smash_context; auto.
    exists s. eapply weaken_ctx in Hs. 3:eapply wf_local_smash_context; eauto. 2:auto.
    eapply (substitution _ _ _ _ []) in Hs. eapply Hs. all:auto.
    reflexivity.
    simpl. rewrite (lift_extended_subst _ 1).
    rewrite distr_lift_subst. f_equal.
    rewrite lift_closed //. autorewrite with len.
    now apply subject_closed in Hs.
Qed.

Lemma spine_subst_smash_inv {cf : checker_flags} {Σ : global_env_ext} (Δ : context) :
  wf Σ.1 ->
  wf_local Σ Δ ->
  spine_subst Σ (smash_context [] Δ) 
    (to_extended_list (smash_context [] Δ)) (extended_subst Δ 0) Δ.
Proof.
  move=> wfΣ wfΔ.
  split; auto.
  - eapply wf_local_smash_context; auto.
  - eapply weaken_wf_local; auto. apply wf_local_smash_context; auto.
  - remember #|Δ| as n.
    rewrite /to_extended_list.
    rewrite -extended_subst_to_extended_list_k.
    eapply context_subst_to_extended_list_k; eauto.
  - now apply subslet_extended_subst.
Qed.
From MetaCoq.PCUIC Require Import PCUICInduction.

Lemma isType_it_mkProd_or_LetIn_smash {cf:checker_flags} Σ Γ Δ s :
  wf Σ.1 ->
  isType Σ Γ (it_mkProd_or_LetIn Δ (tSort s)) ->
  isType Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (tSort s)).
Proof.
  move=> wfΣ [u Hu].
  exists u. unfold PCUICTypingDef.typing in *. revert Γ u Hu.
  induction Δ as [|[na [b|] ty] Δ] using ctx_length_rev_ind; simpl in *; auto;
  rewrite !it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=; rewrite smash_context_app; intros Γ u Hu.
  - simpl.
    assert (wfu := typing_wf_universe wfΣ Hu).
    eapply inversion_LetIn in Hu as [? [? [? [? [? ?]]]]]; auto.
    eapply substitution_let in t1; auto.
    rewrite /subst1 subst_it_mkProd_or_LetIn /= in t1.
    specialize (X (subst_context [b] 0 Δ) ltac:(autorewrite with len; lia)).
    eapply invert_cumul_letin_l in c; eauto.
    eapply type_Cumul' in t1. 3:eauto.
    2:{ pcuic. eexists; econstructor; pcuic. }
    specialize (X _ _ t1).
    now rewrite -smash_context_subst /= subst_context_nil.
  - simpl. rewrite it_mkProd_or_LetIn_app. simpl.
    assert (wfu := typing_wf_universe wfΣ Hu).
    eapply inversion_Prod in Hu as [? [? [? [? ?]]]]; auto.
    specialize (X Δ ltac:(reflexivity)).
    specialize (X _ _ t0).
    eapply type_Cumul'; eauto.
    econstructor; pcuic.
    eapply isType_intro. econstructor; pcuic.
Qed.


Lemma typing_spine_to_extended_list {cf:checker_flags} Σ Δ u s :
  wf Σ.1 ->
  isType Σ [] (subst_instance u (it_mkProd_or_LetIn Δ (tSort s))) ->
  typing_spine Σ (smash_context [] (subst_instance u Δ))
    (subst_instance u (it_mkProd_or_LetIn Δ (tSort s)))
    (to_extended_list (smash_context [] (subst_instance u Δ)))
    (tSort (subst_instance_univ u s)).
Proof.
  move=> wfΣ wfΔ.
  apply wf_arity_spine_typing_spine; auto.
  rewrite subst_instance_it_mkProd_or_LetIn in wfΔ |- *.
  split.
  eapply isType_weaken; auto.
  eapply wf_local_smash_context; pcuic.
  now eapply isType_it_mkProd_or_LetIn_wf_local in wfΔ; auto; rewrite app_context_nil_l in wfΔ.
  rewrite -(app_nil_r (to_extended_list (smash_context [] (subst_instance u Δ)))).
  eapply arity_spine_it_mkProd_or_LetIn; auto.
  2:{ simpl; constructor; [|reflexivity].
      eapply isType_it_mkProd_or_LetIn_smash in wfΔ; auto.
      eapply isType_it_mkProd_or_LetIn_inv in wfΔ. now rewrite app_context_nil_l in wfΔ.
      auto. }
  eapply spine_subst_smash_inv; eauto.
  eapply isType_it_mkProd_or_LetIn_inv in wfΔ; pcuic.
  rewrite app_context_nil_l in wfΔ.
  now eapply isType_wf_local.
Qed.

Lemma wf_projection_context {cf:checker_flags} (Σ : global_env_ext) {mdecl idecl p pdecl u} : 
  wf Σ.1 ->
  declared_projection Σ p mdecl idecl pdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (projection_context mdecl idecl p.1.1 u).
Proof.
  move=> wfΣ decli.
  pose proof (on_declared_projection decli) as [onmind onind].
  set (oib := declared_inductive_inv _ _ _ _) in *. clearbody oib.
  simpl in onind; destruct ind_ctors as [|? []] => //.
  destruct onind as [[[_ onps] Hpe] onp].
  move=> cu.
  assert(wfparams : wf_local Σ (subst_instance u (ind_params mdecl))).
  { eapply on_minductive_wf_params; eauto. eapply decli. }
  assert(wfsmash : wf_local Σ (smash_context [] (subst_instance u (ind_params mdecl)))).
  { eapply wf_local_smash_context; auto. }
  constructor; auto. red.
  exists (subst_instance_univ u (ind_sort idecl)).
  eapply type_mkApps. econstructor; eauto. eapply decli.p1.
  rewrite (ind_arity_eq oib).
  pose proof (on_projs_noidx _ _ _ _ _ _ onps).
  destruct (ind_indices idecl) eqn:eqind; try discriminate.
  simpl.
  eapply typing_spine_to_extended_list; eauto.
  pose proof (on_inductive_inst decli _ u localenv_nil).
  rewrite eqind in X. simpl in X.
  now rewrite subst_instance_it_mkProd_or_LetIn.
Qed.

Lemma invert_type_mkApps_ind {cf:checker_flags} Σ Γ ind u args T mdecl idecl :
  wf Σ.1 ->
  declared_inductive Σ.1 ind mdecl idecl ->
  Σ ;;; Γ |- mkApps (tInd ind u) args : T ->
  (typing_spine Σ Γ (subst_instance u (ind_type idecl)) args T)
  * consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  intros wfΣ decli.
  intros H; dependent induction H; solve_discr.
  - destruct args using rev_case; solve_discr. noconf H2.
    rewrite -PCUICAstUtils.mkApps_nested in H2. simpl in H2.
    noconf H2. clear IHtyping1 IHtyping3.
    specialize (IHtyping2 _ _ _ _ _ _ _ wfΣ decli eq_refl) as [IH cu];
      split; auto.
    destruct (on_declared_inductive decli) as [onmind oib].
    eapply typing_spine_app; eauto.
  - invs H0. destruct (declared_inductive_inj d decli) as [-> ->].
    clear decli. split; auto.
    constructor; [|reflexivity].
    destruct (on_declared_inductive d) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    eapply isType_weaken; eauto.
    eapply (isType_subst_instance_decl _ []); eauto.
    destruct d; eauto.
    eapply oib.(onArity). auto.
  - specialize (IHtyping1 _ _ wfΣ decli) as [IH cu]; split; auto.
    eapply typing_spine_weaken_concl; pcuic.
Qed.

Lemma isType_mkApps_Ind {cf:checker_flags} {Σ Γ ind u args} (wfΣ : wf Σ.1)
  {mdecl idecl} (declm : declared_inductive Σ.1 ind mdecl idecl) :
  wf_local Σ Γ ->
  isType Σ Γ (mkApps (tInd ind u) args) ->
  ∑ parsubst argsubst,
    let parctx := (subst_instance u (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0 (subst_instance u (idecl.(ind_indices)))) in
    spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx *
    spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx *
    consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  move=> wfΓ isType.
  destruct isType as [s Hs].
  eapply invert_type_mkApps_ind in Hs as [tyargs cu]; eauto.
  set (decli' := on_declared_inductive declm).
  rename declm into decli.
  destruct decli' as [declm decli'].
  pose proof (decli'.(onArity)) as ar. 
  rewrite decli'.(ind_arity_eq) in tyargs, ar.
  hnf in ar. destruct ar as [s' ar].
  rewrite !subst_instance_it_mkProd_or_LetIn in tyargs.
  simpl in tyargs. rewrite -it_mkProd_or_LetIn_app in tyargs.
  eapply arity_typing_spine in tyargs as [[argslen leqs] [instsubst [wfdom wfcodom cs subs]]] => //.
  apply context_subst_app in cs as [parsubst argsubst].
  eexists _, _. move=> parctx argctx. 
  rewrite subst_instance_assumptions in argsubst, parsubst.
  rewrite declm.(onNpars) in argsubst, parsubst.
  eapply subslet_app_inv in subs as [subp suba].
  rewrite subst_instance_length in subp, suba.
  subst parctx argctx.
  repeat split; eauto; rewrite ?subst_instance_length => //.
  rewrite app_context_assoc in wfcodom. now apply All_local_env_app_inv in wfcodom as [? ?].
  simpl.
  eapply substitution_wf_local; eauto. now rewrite app_context_assoc in wfcodom.
  eapply (on_inductive_inst decli) in cu; eauto.
  rewrite subst_instance_app in cu.
  now eapply isType_it_mkProd_or_LetIn_wf_local in cu.
Qed.

Lemma projection_subslet {cf:checker_flags} Σ Γ mdecl idecl u c p pdecl args :
  declared_projection Σ.1 p mdecl idecl pdecl ->
  wf Σ.1 ->
  Σ ;;; Γ |- c : mkApps (tInd p.1.1 u) args ->
  isType Σ Γ (mkApps (tInd p.1.1 u) args) ->
  subslet Σ Γ (c :: List.rev args) (projection_context mdecl idecl p.1.1 u). 
Proof.
  intros declp wfΣ Hc Ha.
  destruct (on_declared_projection declp).
  destruct (isType_mkApps_Ind wfΣ (let (x, _) := declp in x) (typing_wf_local Hc) Ha) as 
    [parsubst [argsubst [[sppars spargs] cu]]].
  unfold projection_context.
  set (oib := declared_inductive_inv _ _ _ _) in *. clearbody oib.
  simpl in y.
  destruct (ind_ctors idecl) as [|ctors []]; try contradiction.
  destruct y as [[[_ onps] ?] ?].
  pose proof (on_projs_noidx _ _ _ _ _ _ onps).
  pose proof (onNpars o).
  pose proof (context_subst_length2 spargs).
  rewrite context_assumptions_fold in H1.
  autorewrite with len in H1.
  destruct (ind_indices idecl); try discriminate.
  simpl in H1. rewrite List.skipn_length in H1.
  assert(#|args| = ind_npars mdecl).
  { pose proof (context_subst_length2 sppars).
    autorewrite with len in H2.
    rewrite H0 in H2.
    apply firstn_length_le_inv in H2. lia. }
  rewrite -H2 in sppars.
  rewrite firstn_all in sppars.
  eapply spine_subst_smash in sppars; auto.
  constructor. apply sppars.
  rewrite subst_mkApps /=.
  rewrite /argsubst in H1.
  now rewrite (spine_subst_subst_to_extended_list_k sppars).
Qed.


Lemma invert_red1_letin {cf:checker_flags} (Σ : global_env_ext) Γ C na d ty b :
  red1 Σ.1 Γ (tLetIn na d ty b) C ->
  (∑ d', (C = tLetIn na d' ty b) *
    red1 Σ.1 Γ d d') +
  (∑ ty', (C = tLetIn na d ty' b) *
    red1 Σ.1 Γ ty ty') +
  (∑ b', (C = tLetIn na d ty b') *
    red1 Σ.1 (Γ ,, vdef na d ty) b b') +
  (C = subst10 d b)%type.
Proof.
  intros H; depelim H; try solve_discr; pcuicfo auto.
  - left. left. left. eexists; eauto.
  - left. left. right. eexists; eauto.
  - left. right. eexists; eauto.
Qed.

Lemma decompose_prod_assum_it_mkProd_or_LetIn' ctx Γ t :
  decompose_prod_assum ctx (it_mkProd_or_LetIn Γ t) =
  let (ctx', t') := decompose_prod_assum [] t in
  (ctx ,,, Γ ,,, ctx', t').
Proof.
  generalize ctx.
  induction Γ using rev_ind; simpl; intros.
  - now rewrite decompose_prod_assum_ctx.
  - rewrite it_mkProd_or_LetIn_app.
    destruct x as [na [b|] ty]; simpl.
    rewrite IHΓ.
    destruct (decompose_prod_assum [] t).
    now rewrite app_context_assoc.
    rewrite IHΓ.
    destruct (decompose_prod_assum [] t).
    now rewrite app_context_assoc.
Qed.

Definition head x := (decompose_app x).1.
Definition arguments x := (decompose_app x).2.

Lemma head_arguments x : mkApps (head x) (arguments x) = x.
Proof.
  unfold head, arguments, decompose_app.
  remember (decompose_app_rec x []).
  destruct p as [f l].
  symmetry in Heqp.
  eapply decompose_app_rec_inv in Heqp.
  now simpl in *.
Qed.

Lemma fst_decompose_app_rec t l : fst (decompose_app_rec t l) = fst (decompose_app t).
Proof.
  induction t in l |- *; simpl; auto. rewrite IHt1.
  unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
Qed.

Lemma decompose_app_rec_head t l f : fst (decompose_app_rec t l) = f ->
  negb (isApp f).
Proof.
  induction t; unfold isApp; simpl; try intros [= <-]; auto.
  intros. apply IHt1. now rewrite !fst_decompose_app_rec.
Qed.

Lemma head_nApp x : negb (isApp (head x)).
Proof.
  unfold head.
  eapply decompose_app_rec_head. reflexivity.
Qed.

Lemma head_tapp t1 t2 : head (tApp t1 t2) = head t1.
Proof. rewrite /head /decompose_app /= fst_decompose_app_rec //. Qed.

Lemma destInd_head_subst s k t f : destInd (head (subst s k t)) = Some f ->
  (destInd (head t) = Some f) +  
  (∑ n u, (head t = tRel n) /\ k <= n /\ (nth_error s (n - k) = Some u /\ destInd (head  (lift0 k u)) = Some f)).
Proof.
  induction t in s, k, f |- *; simpl; try solve [pcuicfo auto].
  elim: leb_spec_Set => le; intros destI.
   right.
  destruct nth_error eqn:Heq.
  - exists n, t; intuition auto.
  - simpl in destI => //.
  - simpl => //.
  - intros destI. rewrite head_tapp in destI.
    rewrite head_tapp.
    specialize (IHt1 _ _ _ destI).
    destruct IHt1 as [?|[n [u [headt1 [hnth hind]]]]].
    * left; auto.
    * right. exists n, u; intuition auto.
Qed.

Lemma destInd_head_lift n b ind u : destInd (head (lift0 n b)) = Some (ind, u) ->
  destInd (head b) = Some (ind, u).
Proof.
  induction b; simpl; try discriminate.
  rewrite !head_tapp. apply IHb1.
  congruence.
Qed.

Lemma destInd_head_lift_inv n b ind u : destInd (head b) = Some (ind, u) ->
  destInd (head (lift0 n b)) = Some (ind, u).
Proof.
  induction b; simpl; try discriminate.
  rewrite !head_tapp. apply IHb1.
  congruence.
Qed.

Lemma head_subst s k t : head (subst s k t) = head (subst s k (head t)).
Proof.
  induction t; simpl; auto.
  now rewrite !head_tapp.
Qed.

Hint Rewrite context_assumptions_app context_assumptions_subst : len.

Lemma red1_destInd (Σ : global_env_ext) Γ t t' ind u : 
  red1 Σ.1 Γ t t' -> destInd (head t) = Some (ind, u) -> 
  destInd (head t') = Some (ind, u).
Proof.
  induction 1; simpl in *; try discriminate.
  unfold head.
  remember (mkApps (tFix mfix idx) args) eqn:decapp.
  symmetry in decapp. pose proof (mkApps_Fix_spec _ _ _ _ decapp).
  destruct (decompose_app t); simpl in *; try discriminate.
  destruct t0; try discriminate.
  elim H.
  rewrite !head_tapp. auto.
  rewrite !head_tapp. auto.
Qed.

Lemma red_destInd (Σ : global_env_ext) Γ t t' ind u : 
  red Σ.1 Γ t t' -> destInd (head t) = Some (ind, u) -> 
  destInd (head t') = Some (ind, u).
Proof.
  intros r%Relation_Properties.clos_rt_rt1n_iff.
  induction r.
  auto.
  intros.
  eapply red1_destInd in H. apply IHr. eauto.
  eauto.
Qed.

Lemma destInd_Some_eq t ind u : destInd t = Some (ind, u) -> t = tInd ind u.
Proof.
  destruct t; simpl; congruence.
Qed.

Lemma red_it_mkProd_or_LetIn_smash {cf:checker_flags} (Σ : global_env_ext) Γ ctx t u n c :
  wf Σ.1 ->  
  red Σ.1 Γ (it_mkProd_or_LetIn ctx t) u ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  ∑ ctx' t',
    (decompose_prod_assum [] u = (ctx', t')) *
    ∑ d, (nth_error (List.rev (smash_context [] ctx')) n = Some d) *
      red Σ.1 (Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx)) (decl_type c) (decl_type d).
Proof.
  intros wfΣ.
  rename Γ into Δ.
  revert Δ t u n c.
  induction ctx using ctx_length_rev_ind; simpl; intros Δ t u n c r.
  rewrite nth_error_nil => //.
  destruct d as [na [b|] ty].
  rewrite it_mkProd_or_LetIn_app in r.
  simpl in *.
  eapply invert_red_letin in r as [[d' [ty' [b' [[[-> redb] redty] redbody]]]]|]; auto.
  - intros Hnth.
    rewrite !smash_context_app smash_context_acc in Hnth |- *; simpl in *.
    pose proof (nth_error_Some_length Hnth).
    autorewrite with len in H. simpl in H.
    rewrite nth_error_rev_inv in Hnth.
    now autorewrite with len.
    autorewrite with len in Hnth. simpl in Hnth.
    rewrite subst_empty lift0_id lift0_context in Hnth.
    rewrite app_nil_r in Hnth.
    rewrite nth_error_subst_context in Hnth.
    unfold snoc; simpl.
    rewrite decompose_prod_assum_ctx.
    specialize (X Γ ltac:(lia)).
    destruct nth_error eqn:hnth.
    specialize (X _ _ _ n c0 redbody).
    rewrite nth_error_rev_inv in X; autorewrite with len. auto.
    autorewrite with len in X |- *. simpl in *.
    specialize (X hnth).
    destruct X as [ctx' [t' [decompb X]]].
    rewrite decompb. eexists _, _; intuition eauto.
    destruct X as [decl [hnth' hred]].
    have hlen := nth_error_Some_length hnth'.
    autorewrite with len in hlen.
    rewrite nth_error_rev_inv in hnth'; autorewrite with len. auto.
    rewrite nth_error_rev_inv; autorewrite with len.
    rewrite context_assumptions_app /=. simpl in hlen. lia.
    rewrite smash_context_app smash_context_acc /= app_nil_r.
    rewrite subst_empty lift0_id lift0_context.
    rewrite app_nil_r.
    rewrite nth_error_subst_context /=.
    autorewrite with len. simpl in *.
    rewrite context_assumptions_app /=. simpl.
    rewrite Nat.add_0_r. autorewrite with len in hnth'. rewrite hnth'.
    simpl. eexists; split; eauto. simpl.
    autorewrite with len in Hnth. simpl in Hnth. move: Hnth.
    assert (context_assumptions ctx' -
    S (context_assumptions ctx' - S n) = n) as -> by lia.
    assert (context_assumptions Γ -
    S (context_assumptions Γ  - S n) = n) as -> by lia.
    move=> [= <-]. simpl.
    transitivity (subst [b] n (decl_type decl)).
    rewrite subst_empty lift0_id lift0_context.
    epose proof (substitution_untyped_red _ Δ [vdef na b ty] (skipn (context_assumptions Γ - n) (smash_context [] Γ)) [b]
      (decl_type c0) (decl_type decl) wfΣ).
    forward X. rewrite -{1}(subst_empty 0 b). repeat constructor.
    specialize (X hred).
    rewrite skipn_subst_context.
    rewrite !skipn_length in X; autorewrite with len. lia.
    autorewrite with len in X. simpl in X.
    assert(context_assumptions Γ - (context_assumptions Γ - n) = n) by lia.
    rewrite H0 in X. apply X.
    epose proof (red_red Σ Δ [vdef na b ty] (skipn (context_assumptions Γ - n) (subst_context [b] 0 (smash_context [] Γ)))).
    rewrite subst_empty lift0_id lift0_context.
    rewrite !skipn_length in X; autorewrite with len. lia.
    autorewrite with len in X. simpl in X.
    assert(context_assumptions Γ - (context_assumptions Γ - n) = n) by lia.
    rewrite H0 in X.
    eapply X; auto. rewrite -{1}(subst_empty 0 b); repeat constructor.
    simpl in Hnth; discriminate.

  - rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in r.
    intros hnth.
    rewrite smash_context_app smash_context_acc /= app_nil_r in hnth.
    rewrite subst_empty lift0_id lift0_context in hnth.
    specialize (X (subst_context [b] 0 Γ) ltac:(autorewrite with len; lia)).
    specialize (X _ _ _ n c r). 
    rewrite (smash_context_subst []) in X.
    specialize (X hnth). 
    autorewrite with len. simpl.
    autorewrite with len in X. simpl in X.
    rewrite smash_context_app smash_context_acc /=.
    rewrite subst_empty lift0_id lift0_context app_nil_r.
    apply X.

  - rewrite smash_context_app /= List.rev_app_distr /=.
    move=> hnth.
    rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= in r.
    eapply invert_red_prod in r as [A' [B' [[-> redty] redB']]]; auto.
    simpl. rewrite decompose_prod_assum_ctx.
    destruct n. 
    * simpl in hnth. noconf hnth; simpl in *.
      destruct (decompose_prod_assum [] B') eqn:decomp.
      eexists _, _; intuition eauto.
      unfold snoc; simpl. rewrite smash_context_app /= List.rev_app_distr /=.
      eexists _; split; eauto.
      autorewrite with len. simpl.
      rewrite skipn_all2. autorewrite with len. simpl. lia. auto.
    * simpl in hnth.
      specialize (X Γ ltac:(lia) (vass na ty :: Δ) t B' n c redB' hnth).
      destruct X as [ctx' [t' [decomp [d [hnth' red]]]]].
      rewrite decomp. simpl. eexists _, _; intuition eauto.
      unfold snoc; simpl. rewrite smash_context_app /= List.rev_app_distr /= hnth'.
      eexists _; split; eauto.
      rewrite app_length. simpl.
      autorewrite with len. simpl.
      assert (context_assumptions Γ + 1 - S n = context_assumptions Γ - n) by lia.
      rewrite H. rewrite skipn_app.
      autorewrite with len. simpl.
      rewrite [skipn _ [_]]skipn_0_eq. lia.
      rewrite app_context_assoc. unfold app_context in red |- *.
      simpl. autorewrite with len in red. simpl in red.
      apply red.
Qed.

Lemma red1_it_mkProd_or_LetIn_smash {cf:checker_flags} (Σ : global_env_ext) Γ ctx t u n c :
  wf Σ.1 ->  
  red1 Σ.1 Γ (it_mkProd_or_LetIn ctx t) u ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  ∑ ctx' t',
    (decompose_prod_assum [] u = (ctx', t')) *
    ∑ d, (nth_error (List.rev (smash_context [] ctx')) n = Some d) *
      (match destInd (head (decl_type c)) with 
      | Some ind => destInd (head (decl_type d)) = Some ind
      | None => True
      end).
Proof.      
  intros wfΣ r nth.
  apply red1_red in r.
  eapply red_it_mkProd_or_LetIn_smash in nth; eauto.
  destruct nth as [ctx' [t' [decomp [d [hnth r']]]]].
  exists ctx', t'; intuition auto.
  exists d; intuition auto.
  destruct destInd as [[ind u']|] eqn:di; auto.
  now eapply (red_destInd _ _ _ _ _ _ r').
Qed.

Lemma red_it_mkProd_or_LetIn_mkApps_Ind {cf:checker_flags} (Σ : global_env_ext) Γ ctx ind u args v :
  wf Σ.1 ->  
  red Σ.1 Γ (it_mkProd_or_LetIn ctx (mkApps (tInd ind u) args)) v ->
  ∑ ctx' args', v = it_mkProd_or_LetIn ctx' (mkApps (tInd ind u) args').
Proof.
  intros wfΣ.
  rename Γ into Δ.
  revert Δ v args.
  induction ctx using ctx_length_rev_ind; simpl; intros Δ v args r.
  - eapply red_mkApps_tInd in r  as [args' [-> conv]];  auto.
    now exists [], args'.
  - rewrite it_mkProd_or_LetIn_app in r.
    destruct d as [na [b|] ty].
    simpl in *.
    eapply invert_red_letin in r as [[d' [ty' [b' [[[-> redb] redty] redbody]]]]|]; auto.
    * specialize (X Γ ltac:(lia) _ _ _ redbody).
      destruct X as [ctx' [args' ->]].
      exists (ctx' ++ [vdef na d' ty']).
      exists args'. now rewrite it_mkProd_or_LetIn_app /=.
    * rewrite /subst1 subst_it_mkProd_or_LetIn subst_mkApps /= in r.
      specialize (X (subst_context [b] 0 Γ) ltac:(autorewrite with len; lia) _ _ _ r).
      apply X.
    * simpl in r.
      eapply invert_red_prod in r as [A' [B' [[-> redty] redB']]]; auto.
      specialize (X Γ ltac:(lia) _ _ _ redB') as [ctx' [args' ->]].
      exists (ctx' ++ [vass na A']), args'.
      rewrite it_mkProd_or_LetIn_app /= //.
Qed.


(* We show that the derived predicate of a case is always well-typed, for *any*
  instance of the parameters (not just the ones from a well-formed predicate). *)
Lemma isType_case_predicate {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} u params ps :
  wf_local Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_universe Σ ps ->
  spine_subst Σ Γ params (List.rev params) 
    (smash_context [] (subst_instance u (ind_params mdecl))) ->
  isType Σ Γ 
    (it_mkProd_or_LetIn 
      (pre_case_predicate_context_gen ci mdecl idecl params u) 
      (tSort ps)).
Proof.
  move=> wfΓ isdecl cu wfps sp.
  rewrite /pre_case_predicate_context_gen.
  set (iass := {| decl_name := _ |}).
  rewrite subst_instance_expand_lets_ctx.
  unshelve epose proof (on_inductive_inst isdecl _ _ _ cu); tea.
  rewrite -/(subst_context_let_expand _ _ _).
  rewrite subst_instance_app_ctx in X.
  destruct X as [s Hs]. red in Hs.
  eapply isType_it_mkProd_or_LetIn_app in Hs. 2:eapply sp.
  rewrite subst_let_expand_it_mkProd_or_LetIn in Hs.
  eapply type_it_mkProd_or_LetIn_inv in Hs as (idxs & inds & sortsidx & sortind & leq).
  eexists (sort_of_products (subst_instance u (ind_sort idecl) :: idxs)
    (Universe.super ps)); red.
  set (idxctx := subst_context_let_expand _ _ _) in *.
  have tyass : Σ ;;; Γ ,,, idxctx |- decl_type iass : 
    tSort (subst_instance u (ind_sort idecl)).
  { pose proof (on_inductive_sort_inst isdecl _ cu).
    rewrite /iass /=.
    have wfidxctx : wf_local Σ (Γ ,,, idxctx) by pcuic.
    eapply pre_type_mkApps_arity. econstructor; tea. pcuic.
    eapply on_inductive_isType; tea. pcuic.
    pose proof (on_declared_inductive isdecl) as [onmind oib].
    rewrite oib.(ind_arity_eq) subst_instance_it_mkProd_or_LetIn.
    eapply arity_spine_it_mkProd_or_LetIn_smash; tea.
    rewrite -[smash_context [] _](closed_ctx_lift #|idecl.(ind_indices)| 0).
    { eapply closedn_smash_context.
      rewrite closedn_subst_instance_context.
      eapply (declared_inductive_closed_params isdecl). }
    relativize #|ind_indices idecl|.
    rewrite -map_rev. eapply subslet_lift; tea.
    eapply sp. now rewrite /idxctx; len.
    rewrite subst_instance_it_mkProd_or_LetIn subst_let_expand_it_mkProd_or_LetIn /=.
    eapply arity_spine_it_mkProd_or_LetIn_Sort => //. reflexivity.
    relativize (subst_context_let_expand (List.rev (map _ _)) _ _).
    relativize (to_extended_list _).
    eapply spine_subst_to_extended_list_k; tea.
    rewrite [reln [] _ _]to_extended_list_subst_context_let_expand.
    apply PCUICLiftSubst.map_subst_instance_to_extended_list_k.
    rewrite subst_context_let_expand_length subst_instance_length.
    rewrite /subst_context_let_expand.
    rewrite distr_lift_subst_context map_rev. f_equal.
    rewrite List.rev_length Nat.add_0_r.
    rewrite PCUICClosed.closed_ctx_lift //.
    pose proof (PCUICContextSubst.context_subst_length2 sp).
    rewrite context_assumptions_smash_context /= in H0. len in H0.
    rewrite H0.
    relativize (context_assumptions _).
    eapply closedn_ctx_expand_lets.
    rewrite -subst_instance_app_ctx closedn_subst_instance_context.
    eapply (declared_inductive_closed_pars_indices _ isdecl). now len. }  
  eapply type_it_mkProd_or_LetIn_sorts; tea.
  constructor => //.
  constructor => //. simpl.
  constructor => //.
  now eapply sorts_local_ctx_wf_local; tea. red.
  eexists; tea. 
Qed.

Lemma arity_spine_case_predicate {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} {u params indices ps} {c} :
  wf_local Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_universe Σ ps ->
  spine_subst Σ Γ params (List.rev params) 
    (smash_context [] (subst_instance u (ind_params mdecl))) ->
  spine_subst Σ Γ indices (List.rev indices) 
    (subst_context_let_expand (List.rev params)
        (subst_instance u (ind_params mdecl))
        (smash_context [] (subst_instance u (ind_indices idecl)))) ->
  Σ ;;; Γ |- c : mkApps (tInd ci u) (params ++ indices) ->
  arity_spine Σ Γ
    (it_mkProd_or_LetIn
      (pre_case_predicate_context_gen ci mdecl idecl params u) 
      (tSort ps)) 
    (indices ++ [c]) (tSort ps).
Proof.
  move=> wfΓ isdecl cu wfps sppars spidx Hc.
  rewrite /pre_case_predicate_context_gen.
  simpl.
  rewrite subst_instance_expand_lets_ctx.
  eapply arity_spine_it_mkProd_or_LetIn_smash; tea.
  rewrite (smash_context_subst []).
  rewrite /subst_context_let_expand (expand_lets_smash_context _ []) 
    expand_lets_k_ctx_nil /= in spidx.
  apply spidx. rewrite subst_let_expand_tProd.
  constructor.
  2:econstructor.
  set (ictx := subst_instance u _).
  eapply meta_conv; tea.
  rewrite subst_let_expand_mkApps subst_let_expand_tInd map_app.
  f_equal. f_equal.
  rewrite -{1}[params](map_id params).
  rewrite map_map_compose; eapply map_ext => x.
  setoid_rewrite subst_let_expand_lift_id; auto.
  now rewrite /ictx; len.
  rewrite /ictx /expand_lets_ctx /expand_lets_k_ctx; len.
  pose proof (PCUICContextSubst.context_subst_length2 spidx).
  rewrite /subst_context_let_expand in H. len in H.
  now rewrite context_assumptions_smash_context /= in H; len in H.
  (* Should be a lemma *)
  rewrite -subst_context_map_subst_expand_lets.
  rewrite /ictx; len.
  pose proof (PCUICContextSubst.context_subst_length2 sppars).
  now rewrite context_assumptions_smash_context /= in H; len in H.
  rewrite /subst_let_expand /expand_lets /expand_lets_k.
  rewrite -map_map_compose.
  rewrite -{1}(spine_subst_subst_to_extended_list_k spidx).
  f_equal.
  rewrite to_extended_list_k_subst /expand_lets_ctx /expand_lets_k_ctx.
  rewrite !to_extended_list_k_subst to_extended_list_k_lift_context.
  rewrite -map_map_compose. simpl. len.
  rewrite lift_to_extended_list_k.
  set (ctx := subst_context _ _ _).
  assert (to_extended_list_k (ind_indices idecl) 0 = to_extended_list_k ctx 0) as ->.
  { rewrite /ctx to_extended_list_k_subst.
    now rewrite PCUICLiftSubst.map_subst_instance_to_extended_list_k. }
  rewrite extended_subst_to_extended_list_k /ctx.
  now rewrite (smash_context_subst []) to_extended_list_k_subst.
Qed.
