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

Section Universes.
  Context {cf:checker_flags}.

  Lemma subst_instance_instance_id u mdecl : 
    subst_instance_instance u (PCUICLookup.abstract_instance (ind_universes mdecl)) = u.
  Proof.
    todo "universes"%string.
  Qed.

  Lemma consistent_instance_ext_abstract_instance Σ mdecl mind :
    wf Σ ->
    declared_minductive Σ mind mdecl ->
    consistent_instance_ext (Σ, ind_universes mdecl) (ind_universes mdecl)
        (PCUICLookup.abstract_instance (ind_universes mdecl)).
  Proof.
    todo "universes"%string.
  Defined.

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

End Universes.

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

Lemma on_projections_decl {cf:checker_flags} {Σ mdecl ind idecl cs} :
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

(* Well, it's a smash_context mess! *)
Lemma declared_projections {cf:checker_flags} {Σ : global_env_ext} {mdecl ind idecl} : 
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
  red in X0.
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
        rewrite (PCUICSigmaCalculus.subst_id _ (({|
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

Lemma declared_projection_type {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p pdecl} : 
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

Lemma declared_projection_type_and_eq {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p pdecl} : 
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

Lemma invert_type_mkApps_ind {cf:checker_flags} Σ Γ ind u args T mdecl idecl :
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
  - destruct (declared_inductive_inj isdecl decli) as [-> ->].
    clear decli. split; auto.
    constructor; [|reflexivity].
    destruct (on_declared_inductive wfΣ isdecl) as [onmind oib].
    pose proof (oib.(onArity)) as ar.
    eapply isWAT_weaken; eauto.
    eapply (isWAT_subst_instance_decl (Γ:=[])); eauto.
    destruct isdecl; eauto.
    now right. simpl; auto.  
  - specialize (IHtyping _ _ wfΣ decli) as [IH cu]; split; auto.
    eapply typing_spine_weaken_concl; eauto.
Qed.

Lemma isWAT_mkApps_Ind {cf:checker_flags} {Σ Γ ind u args} (wfΣ : wf Σ.1)
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
  apply decli.
Qed.
