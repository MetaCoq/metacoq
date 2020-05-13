(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

Require Import Equations.Prop.DepElim.
From Coq Require Import Bool String List Lia Arith.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICWeakeningEnv PCUICWeakening
     PCUICSubstitution PCUICClosed PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICEquality PCUICConfluence PCUICParallelReductionConfluence
     PCUICContextConversion PCUICUnivSubstitution
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICParallelReduction PCUICSpine.
     
Close Scope string_scope.

Require Import ssreflect. 

Set Asymmetric Patterns.
Set SimplIsCbn.

From Equations Require Import Equations.

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

Lemma nth_branches_type ind mdecl idecl args u p i t btys : map_option_out (build_branches_type ind mdecl idecl args u p) = Some btys ->
  nth_error btys i = Some t -> 
  (∑ br, (nth_error idecl.(ind_ctors) i = Some br) /\
    (branch_type ind mdecl idecl args u p i br = Some t)).
Proof.
  intros Htys Hnth.
  eapply nth_map_option_out in Htys; eauto.
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

Import PCUICEnvironment.

From MetaCoq.PCUIC Require Import PCUICCtxShape.

Lemma branch_type_spec {cf:checker_flags} Σ ind mdecl idecl cdecl pars u p c nargs bty : 
  declared_inductive Σ mdecl ind idecl ->
  forall (omib : on_inductive (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl),
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind) mdecl (inductive_ind ind) idecl),
  forall cshape (cs : on_constructor (lift_typing typing) (Σ, ind_universes mdecl) mdecl (inductive_ind ind) idecl (ind_indices oib) cdecl cshape),
  branch_type ind mdecl idecl pars u p c cdecl = Some (nargs, bty) ->
  nargs = context_assumptions cshape.(cshape_args) /\
  forall parsubst, 
  context_subst (subst_instance_context u (PCUICAst.ind_params mdecl)) pars parsubst ->
  let indsubst := (inds (inductive_mind ind) u (ind_bodies mdecl)) in
  let nargs' := #|cshape.(cshape_args)| in
  let npars := #|ind_params mdecl| in
  let substargs := (subst_context parsubst 0 
    (subst_context indsubst npars (map_context (subst_instance_constr u) cshape.(cshape_args)))) in
  bty = 
  it_mkProd_or_LetIn substargs
    (mkApps (lift0 nargs' p)
      (map (subst parsubst nargs' ∘ subst indsubst (nargs' + npars) ∘ subst_instance_constr u) cshape.(cshape_indices) ++ 
       [mkApps (tConstruct ind c u)
         (map (lift0 nargs') pars ++         
          to_extended_list substargs)])).
Proof.
  move=> decli onmib [] indices ps aeq onAr indsorts onC onP inds.
  intros cs onc brty.
  simpl in onc.
  clear onP.
  assert(lenbodies: inductive_ind ind < #|ind_bodies mdecl|).
  { destruct decli as [_ Hnth]. now apply nth_error_Some_length in Hnth. }
  clear decli.
  destruct onc.
  destruct cs as [args indi csort] => /=. simpl in *. 
  rewrite cstr_eq in on_ctype.
  unfold branch_type in brty.
  destruct cdecl as [[id ty] nargs'']. simpl in * |-.
  destruct instantiate_params eqn:Heq => //.
  eapply instantiate_params_make_context_subst in Heq.
  destruct Heq as [ctx' [ty'' [s' [? [? ?]]]]].
  subst t. move: H.
  rewrite {1}cstr_eq subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
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
     (subst_instance_constr u cstr_concl_head))) = tInd ind u).
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
  move=> Heq; simpl in Heq; move: Heq.
  rewrite !map_map_compose map_app.
  rewrite chop_n_app.
  rewrite map_length to_extended_list_k_length.
  by rewrite (onmib.(onNpars _ _ _ _)).

  move=> [=] Hargs Hbty. subst nargs. split;auto. rewrite -Hbty.
  clear Hbty bty.
  rewrite app_nil_r.
  move=>parsubst Hpars.
  pose proof (make_context_subst_spec _ _ _ H0) as csubst.
  rewrite rev_involutive in csubst.
  pose proof (context_subst_fun csubst Hpars). subst s'. clear csubst.
  f_equal.
  rewrite !subst_context_length subst_instance_context_length.
  f_equal. f_equal. f_equal. f_equal.
  f_equal. rewrite -(map_map_compose _ _ _ _ (subst _ _ ∘ subst _ _)).
  rewrite subst_instance_to_extended_list_k.
  rewrite -map_map_compose.
  rewrite -to_extended_list_k_map_subst. rewrite subst_instance_context_length; lia.
  now rewrite (subst_to_extended_list_k _ _ pars).
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


Lemma on_minductive_wf_params_indices {cf : checker_flags} (Σ : global_env) mdecl ind idecl :
  wf Σ ->
  declared_minductive Σ (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ, ind_universes mdecl) (inductive_mind ind)
    mdecl (inductive_ind ind) idecl),
  wf_local (Σ, ind_universes mdecl) (ind_params mdecl ,,, ind_indices oib).
Proof.
  intros.
  eapply on_declared_minductive in H; auto.
  pose proof (oib.(onArity)).
  rewrite oib.(ind_arity_eq) in X0.
  destruct X0 as [s Hs].
  rewrite -it_mkProd_or_LetIn_app in Hs.
  eapply it_mkProd_or_LetIn_wf_local in Hs. 
  now rewrite app_context_nil_l in Hs. now simpl.
Qed.

Lemma on_minductive_wf_params_indices_inst {cf : checker_flags} (Σ : global_env × universes_decl)
    mdecl (u : Instance.t) ind idecl :
   wf Σ.1 ->
   declared_minductive Σ.1 (inductive_mind ind) mdecl ->
   forall (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind)
      mdecl (inductive_ind ind) idecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_local Σ (subst_instance_context u (ind_params mdecl ,,, ind_indices oib)).
Proof.
  intros.
  eapply (wf_local_instantiate _ (InductiveDecl mdecl)); eauto.
  now apply on_minductive_wf_params_indices.
Qed.

Lemma on_inductive_inst {cf:checker_flags} Σ Γ ind u mdecl idecl : 
  wf Σ.1 -> 
  wf_local Σ Γ ->
  declared_minductive Σ.1 (inductive_mind ind) mdecl ->
  on_inductive (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl ->
  forall (oib : on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl) (inductive_mind ind) mdecl 
           (inductive_ind ind) idecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isWfArity_or_Type Σ Γ (it_mkProd_or_LetIn (subst_instance_context u (ind_params mdecl ,,, oib.(ind_indices)))
        (tSort (subst_instance_univ u oib.(ind_sort)))).
Proof.
  move=> wfΣ wfΓ declm oi oib cext.
  pose proof (oib.(onArity)) as ar.
  rewrite oib.(ind_arity_eq) in ar.
  destruct ar as [s ar].
  eapply isWAT_weaken => //.
  rewrite -(subst_instance_constr_it_mkProd_or_LetIn u _ (tSort _)).
  rewrite -it_mkProd_or_LetIn_app in ar.
  eapply (typing_subst_instance_decl Σ [] _ _ _ (InductiveDecl mdecl) u) in ar.
  right. eexists _. eapply ar. all:eauto.
Qed.

Lemma nth_errror_arities_context {cf:checker_flags} (Σ : global_env_ext) mdecl ind idecl decl : 
  wf Σ.1 ->
  declared_inductive Σ mdecl ind idecl ->
  on_inductive (lift_typing typing) (Σ.1, ind_universes mdecl)
    (inductive_mind ind) mdecl ->
  on_ind_body (lift_typing typing) (Σ.1, ind_universes mdecl)
    (inductive_mind ind) mdecl (inductive_ind ind) idecl ->
  nth_error (arities_context (ind_bodies mdecl)) (#|ind_bodies mdecl| - S (inductive_ind ind)) = Some decl ->
  decl.(decl_type) = idecl.(ind_type).
Proof.
  move=> wfΣ decli oni onib.
  unfold arities_context.
  rewrite nth_error_rev_map.
  destruct decli as [declm decli]. now apply nth_error_Some_length in decli.
  destruct nth_error eqn:Heq; try discriminate.
  destruct decli. rewrite H0 in Heq. noconf Heq.
  simpl. move=> [] <-. now simpl.
Qed.

Definition projection_context mdecl idecl ind u := 
  smash_context [] (PCUICEnvironment.ind_params mdecl),,
       PCUICEnvironment.vass (nNamed (PCUICEnvironment.ind_name idecl))
         (mkApps
            (tInd
               {|
               inductive_mind := inductive_mind ind;
               inductive_ind := inductive_ind ind |}
               u)
            (PCUICEnvironment.to_extended_list
               (smash_context [] (PCUICEnvironment.ind_params mdecl)))).

Lemma projection_subslet {cf:checker_flags} Σ Γ mdecl idecl ind u c args : 
  Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
  subslet Σ Γ (c :: List.rev args) (projection_context mdecl idecl ind u). 
Proof.
  todo "Projections"%string.
Qed.

Lemma invert_type_mkApps_ind Σ Γ ind u args T mdecl idecl :
  wf Σ.1 ->
  declared_inductive Σ.1 mdecl ind idecl ->
  Σ ;;; Γ |- mkApps (tInd ind u) args : T ->
  (typing_spine Σ Γ (subst_instance_constr u (ind_type idecl)) args T)
  * consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  intros wfΣ decli.
  intros H; dependent induction H; solve_discr.
  - destruct args using rev_case; solve_discr. noconf H1.
    rewrite -PCUICAstUtils.mkApps_nested in H1. simpl in H1.
    noconf H1.  clear IHtyping2.
    specialize (IHtyping1 _ _ _ _ _ _ _ wfΣ decli eq_refl) as [IH cu];
      split; auto.
    destruct (on_declared_inductive wfΣ decli) as [onmind oib].
    eapply typing_spine_app; eauto.
  - noconf H0. subst.
    destruct (declared_inductive_inj isdecl decli) as [-> ->].
    clear decli. split; auto.
    constructor; [|reflexivity].
    destruct (on_declared_inductive wfΣ isdecl) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    eapply isWAT_weaken; eauto.
    eapply (isWAT_subst_instance_decl _ []); eauto.
    destruct isdecl; eauto.
    now right. simpl; auto.  
  - specialize (IHtyping _ _ wfΣ decli) as [IH cu]; split; auto.
    eapply typing_spine_weaken_concl; eauto.
Qed.

Lemma isWAT_mkApps_Ind {Σ Γ ind u args} (wfΣ : wf Σ.1)
  {mdecl idecl} (declm : declared_inductive Σ.1 mdecl ind idecl) :
  wf_local Σ Γ ->
  isWfArity_or_Type Σ Γ (mkApps (tInd ind u) args) ->
  ∑ parsubst argsubst,
    let oib := (on_declared_inductive wfΣ declm).2 in
    let parctx := (subst_instance_context u (ind_params mdecl)) in
    let argctx := (subst_context parsubst 0 (subst_instance_context u (oib.(ind_indices)))) in
    spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx *
    spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx *
    consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  move=> wfΓ isWAT.
  destruct isWAT.
  destruct i as [ctx [s Hs]].
  destruct Hs. rewrite destArity_tInd in e => //.
  destruct i as [s Hs].
  eapply invert_type_mkApps_ind in Hs as [tyargs cu]; eauto.
  set (decli' := on_declared_inductive _ _). clearbody decli'.
  rename declm into decli.
  destruct decli' as [declm decli'].
  pose proof (decli'.(onArity)) as ar. 
  rewrite decli'.(ind_arity_eq) in tyargs, ar.
  hnf in ar. destruct ar as [s' ar].
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in tyargs.
  simpl in tyargs. rewrite -it_mkProd_or_LetIn_app in tyargs.
  eapply arity_typing_spine in tyargs as [[argslen leqs] [instsubst [wfdom wfcodom cs subs]]] => //.
  apply context_subst_app in cs as [parsubst argsubst].
  eexists _, _. move=> lk parctx argctx. subst lk.
  rewrite subst_instance_context_assumptions in argsubst, parsubst.
  rewrite declm.(onNpars _ _ _ _) in argsubst, parsubst.
  eapply subslet_app_inv in subs as [subp suba].
  rewrite subst_instance_context_length in subp, suba.
  subst parctx argctx.
  repeat split; eauto; rewrite ?subst_instance_context_length => //.
  rewrite app_context_assoc in wfcodom. now apply All_local_env_app in wfcodom as [? ?].
  simpl.
  eapply substitution_wf_local; eauto. now rewrite app_context_assoc in wfcodom.
  unshelve eapply on_inductive_inst in declm; pcuic.
  rewrite subst_instance_context_app in declm.
  now eapply isWAT_it_mkProd_or_LetIn_wf_local in declm.
Qed.

Lemma invert_type_mkApps_ind Σ Γ ind u args T mdecl idecl :
  wf Σ.1 ->
  declared_inductive Σ.1 mdecl ind idecl ->
  Σ ;;; Γ |- mkApps (tInd ind u) args : T ->
  (typing_spine Σ Γ (subst_instance_constr u (ind_type idecl)) args T)
  * consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  intros wfΣ decli.
  intros H; dependent induction H; solve_discr.
  - destruct args using rev_case; solve_discr. noconf H1.
    rewrite -PCUICAstUtils.mkApps_nested in H1. simpl in H1.
    noconf H1.  clear IHtyping2.
    specialize (IHtyping1 _ _ _ _ _ _ _ wfΣ decli eq_refl) as [IH cu];
      split; auto.
    destruct (on_declared_inductive wfΣ decli) as [onmind oib].
    eapply typing_spine_app; eauto.
  - noconf H0. subst.
    destruct (declared_inductive_inj isdecl decli) as [-> ->].
    clear decli. split; auto.
    constructor; [|reflexivity].
    destruct (on_declared_inductive wfΣ isdecl) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    eapply isWAT_weaken; eauto.
    eapply (isWAT_subst_instance_decl _ []); eauto.
    destruct isdecl; eauto.
    now right. simpl; auto.  
  - specialize (IHtyping _ _ wfΣ decli) as [IH cu]; split; auto.
    eapply typing_spine_weaken_concl; eauto.
Qed.

Lemma isWAT_mkApps_Ind {Σ Γ ind u args} (wfΣ : wf Σ.1)
{mdecl idecl} (declm : declared_inductive Σ.1 mdecl ind idecl) :
wf_local Σ Γ ->
isWfArity_or_Type Σ Γ (mkApps (tInd ind u) args) ->
∑ parsubst argsubst,
  let oib := (on_declared_inductive wfΣ declm).2 in
  let parctx := (subst_instance_context u (ind_params mdecl)) in
  let argctx := (subst_context parsubst 0 (subst_instance_context u (oib.(ind_indices)))) in
  spine_subst Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx *
  spine_subst Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx *
  consistent_instance_ext Σ (ind_universes mdecl) u.
Proof.
  move=> wfΓ isWAT.
  destruct isWAT.
  destruct i as [ctx [s Hs]].
  destruct Hs. rewrite destArity_tInd in e => //.
  destruct i as [s Hs].
  eapply invert_type_mkApps_ind in Hs as [tyargs cu]; eauto.
  set (decli' := on_declared_inductive _ _). clearbody decli'.
  rename declm into decli.
  destruct decli' as [declm decli'].
  pose proof (decli'.(onArity)) as ar. 
  rewrite decli'.(ind_arity_eq) in tyargs, ar.
  hnf in ar. destruct ar as [s' ar].
  rewrite !subst_instance_constr_it_mkProd_or_LetIn in tyargs.
  simpl in tyargs. rewrite -it_mkProd_or_LetIn_app in tyargs.
  eapply arity_typing_spine in tyargs as [[argslen leqs] [instsubst [wfdom wfcodom cs subs]]] => //.
  apply context_subst_app in cs as [parsubst argsubst].
  eexists _, _. move=> lk parctx argctx. subst lk.
  rewrite subst_instance_context_assumptions in argsubst, parsubst.
  rewrite declm.(onNpars _ _ _ _) in argsubst, parsubst.
  eapply subslet_app_inv in subs as [subp suba].
  rewrite subst_instance_context_length in subp, suba.
  subst parctx argctx.
  repeat split; eauto; rewrite ?subst_instance_context_length => //.
  rewrite app_context_assoc in wfcodom. now apply All_local_env_app in wfcodom as [? ?].
  simpl.
  eapply substitution_wf_local; eauto. now rewrite app_context_assoc in wfcodom.
  unshelve eapply on_inductive_inst in declm; pcuic.
  rewrite subst_instance_context_app in declm.
  now eapply isWAT_it_mkProd_or_LetIn_wf_local in declm.
Qed.
