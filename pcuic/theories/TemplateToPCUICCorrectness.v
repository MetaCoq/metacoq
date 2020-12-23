(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils Ast TypingWf WfInv.
From MetaCoq.Template Require TermEquality.
Set Warnings "-notation-overridden".
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCumulativity
     PCUICLiftSubst PCUICEquality PCUICUnivSubst PCUICTyping TemplateToPCUIC
     PCUICWeakening PCUICSubstitution PCUICGeneration PCUICValidity.
Set Warnings "+notation-overridden".

From Equations.Prop Require Import DepElim.
Implicit Types cf : checker_flags.

(* Source = Template, Target (unqualified) = Coq *)
Module S := Template.Ast.
Module SEq := Template.TermEquality.
Module ST := Template.Typing.
Module SL := Template.LiftSubst.

Lemma mkApps_morphism (f : term -> term) u v :
  (forall x y, f (tApp x y) = tApp (f x) (f y)) ->
  f (mkApps u v) = mkApps (f u) (List.map f v).
Proof.
  intros H.
  revert u; induction v; simpl; trivial.
  intros.
  now rewrite IHv, H.
Qed.

Ltac solve_list :=
  rewrite !map_map_compose, ?compose_on_snd, ?compose_map_def;
  try rewrite !map_length;
  try solve_all; try typeclasses eauto with core.

Lemma trans_lift n k t :
  trans (SL.lift n k t) = lift n k (trans t).
Proof.
  revert k. induction t using Template.Induction.term_forall_list_ind; simpl; intros; try congruence.
  - f_equal. rewrite !map_map_compose. solve_all.
  - rewrite lift_mkApps, IHt, map_map.
    f_equal. rewrite map_map; solve_all.

  - f_equal; auto. solve_list.
  - f_equal; auto; solve_list.
  - f_equal; auto; solve_list.
Qed.

Lemma mkApps_app f l l' : mkApps f (l ++ l') = mkApps (mkApps f l) l'.
Proof.
  revert f l'; induction l; simpl; trivial.
Qed.

Lemma trans_mkApp u a : trans (S.mkApp u a) = tApp (trans u) (trans a).
Proof.
  induction u; simpl; try reflexivity.
  rewrite map_app.
  replace (tApp (mkApps (trans u) (map trans args)) (trans a))
    with (mkApps (mkApps (trans u) (map trans args)) [trans a]) by reflexivity.
  rewrite mkApps_app. reflexivity.
Qed.

Lemma trans_mkApps u v : 
  trans (S.mkApps u v) = mkApps (trans u) (List.map trans v).
Proof.
  revert u; induction v.
  simpl; trivial.
  intros.
  rewrite <- Template.LiftSubst.mkApps_mkApp; auto.
  rewrite IHv. simpl. f_equal.
  apply trans_mkApp.
Qed.

Lemma trans_subst t k u : 
  trans (SL.subst t k u) = subst (map trans t) k (trans u).
Proof.
  revert k. induction u using Template.Induction.term_forall_list_ind; simpl; intros; try congruence.

  - repeat nth_leb_simpl; auto.
    rewrite trans_lift.
    rewrite nth_error_map in e0. rewrite e in e0.
    injection e0. congruence.

  - f_equal; solve_list.

  - rewrite subst_mkApps. rewrite <- IHu.
    rewrite trans_mkApps. f_equal.
    solve_list.

  - f_equal; auto; solve_list.
  - f_equal; auto; solve_list.
  - f_equal; auto; solve_list.
Qed.

Notation Tterm := Template.Ast.term.
Notation Tcontext := Template.Ast.context.

Lemma trans_subst_instance_constr u t : trans (Template.UnivSubst.subst_instance_constr u t) =
                                        subst_instance_constr u (trans t).
Proof.
  induction t using Template.Induction.term_forall_list_ind; simpl; try congruence.
  { f_equal. rewrite !map_map_compose. solve_all. }
  { rewrite IHt. rewrite map_map_compose.
    rewrite mkApps_morphism; auto. f_equal.
    rewrite !map_map_compose. solve_all. }
  1-3:f_equal; auto; unfold BasicAst.tFixProp, BasicAst.tCaseBrsProp in *;
    repeat toAll; solve_list.
Qed.

Require Import ssreflect.

Lemma forall_decls_declared_constant Σ cst decl :
  ST.declared_constant Σ cst decl ->
  declared_constant (trans_global_decls Σ) cst (trans_constant_body decl).
Proof.
  unfold declared_constant, ST.declared_constant.
  induction Σ => //; try discriminate.
  case: a => // /= k b.
  unfold eq_kername; destruct kername_eq_dec; subst; auto.
  - by move => [=] ->.
Qed.

Lemma forall_decls_declared_minductive Σ cst decl :
  ST.declared_minductive Σ cst decl ->
  declared_minductive (trans_global_decls Σ) cst (trans_minductive_body decl).
Proof.
  unfold declared_minductive, ST.declared_minductive.
  induction Σ => //; try discriminate.
  case: a => // /= k b.
  unfold eq_kername; destruct kername_eq_dec; subst; auto.
  - by move => [=] ->.
Qed.

Lemma forall_decls_declared_inductive Σ ind mdecl decl :
  ST.declared_inductive Σ ind mdecl decl ->
  declared_inductive (trans_global_decls Σ) (trans_minductive_body mdecl) (trans_one_ind_body ind decl).
Proof.
  unfold declared_inductive, ST.declared_inductive.
  move=> [decl' Hnth].
  pose proof (forall_decls_declared_minductive _ _ _ decl').
  eexists. eauto. destruct decl'; simpl in *.
  red in H. destruct mdecl; simpl.
  by rewrite nth_error_map Hnth.
Qed.

Lemma forall_decls_declared_constructor Σ cst mdecl idecl decl :
  ST.declared_constructor Σ cst mdecl idecl decl ->
  declared_constructor (trans_global_decls Σ) cst (trans_minductive_body mdecl) (trans_one_ind_body idecl)
                    (fun '(x, y, z) => (x, trans y, z)) decl).
Proof.
  unfold declared_constructor, ST.declared_constructor.
  move=> [decl' Hnth].
  pose proof (forall_decls_declared_inductive _ _ _ _ decl'). split; auto.
  destruct idecl; simpl.
  by rewrite nth_error_map Hnth.
Qed.

Lemma forall_decls_declared_projection Σ cst mdecl idecl decl :
  ST.declared_projection Σ cst mdecl idecl decl ->
  declared_projection (trans_global_decls Σ) cst (trans_minductive_body mdecl) (trans_one_ind_body idecl)
                    ((fun '(x, y) => (x, trans y)) decl).
Proof.
  unfold declared_constructor, ST.declared_constructor.
  move=> [decl' [Hnth Hnpar]].
  pose proof (forall_decls_declared_inductive _ _ _ _ decl'). split; auto.
  destruct idecl; simpl.
  by rewrite nth_error_map Hnth.
Qed.

Lemma destArity_mkApps ctx t l : l <> [] -> destArity ctx (mkApps t l) = None.
Proof.
  destruct l as [|a l]. congruence.
  intros _. simpl.
  revert t a; induction l; intros; simpl; try congruence.
Qed.

Lemma trans_destArity ctx t :
  S.wf t ->
  match AstUtils.destArity ctx t with
  | Some (args, s) =>
    destArity (trans_local ctx) (trans t) =
    Some (trans_local args, s)
  | None => destArity (trans_local ctx) (trans t) = None
  end.
Proof.
  intros wf; revert ctx.
  induction wf using Template.Induction.term_wf_forall_list_ind; intros ctx; simpl; trivial.
  apply (IHwf0 (S.vass n t :: ctx)).
  apply (IHwf1 (S.vdef n t t0 :: ctx)).
  destruct l. congruence.
  now apply destArity_mkApps.
Qed.

(* TODO Duplicate? *)
Lemma Alli_map_option_out_mapi_Some_spec {A B B'} (f : nat -> A -> option B) (g' : B -> B')
      (g : nat -> A -> option B') P l t :
  Alli P 0 l ->
  (forall i x t, P i x -> f i x = Some t -> g i x = Some (g' t)) ->
  map_option_out (mapi f l) = Some t ->
  map_option_out (mapi g l) = Some (map g' t).
Proof.
  unfold mapi. generalize 0.
  move => n Hl Hfg. move: n Hl t.
  induction 1; try constructor; auto.
  simpl. move=> t [= <-] //.
  move=> /=.
  case E: (f n hd) => [b|]; try congruence.
  rewrite (Hfg n _ _ p E).
  case E' : map_option_out => [b'|]; try congruence.
  move=> t [= <-]. now rewrite (IHHl _ E').
Qed.

Lemma All2_map_option_out_mapi_Some_spec :
  forall {A B B' S} (f : nat -> A -> option B) (g' : B -> B')
    (g : nat -> A -> option B') P l (ls : list S) t,
    All2 P l ls ->
    (forall i x t s, P x s -> f i x = Some t -> g i x = Some (g' t)) ->
    map_option_out (mapi f l) = Some t ->
    map_option_out (mapi g l) = Some (map g' t).
Proof.
  intros A B B' S f g' g P l ls t.
  unfold mapi. generalize 0.
  intros n hall h e.
  induction hall in t, n, h, e |- *.
  - simpl in *. apply some_inj in e. subst. reflexivity.
  - simpl in *.
    destruct (f n x) eqn:e'. 2: discriminate.
    eapply h in e' as h'. 2: eassumption.
    rewrite h'.
    match type of e with
    | context [ map_option_out ?t ] =>
      destruct (map_option_out t) eqn:e''
    end. 2: discriminate.
    eapply IHhall in e'' as h''. 2: assumption.
    rewrite h''. apply some_inj in e. subst.
    simpl. reflexivity.
Qed.

Definition on_pair {A B C D} (f : A -> B) (g : C -> D) (x : A * C) :=
  (f (fst x), g (snd x)).

Lemma trans_inds kn u bodies : map trans (ST.inds kn u bodies) = inds kn u (map trans_one_ind_body bodies).
Proof.
  unfold inds, ST.inds. rewrite map_length.
  induction bodies. simpl. reflexivity. simpl; f_equal. auto.
Qed.

Lemma trans_instantiate_params_subst params args s t :
  All TypingWf.wf_decl params -> All Ast.wf s ->
  All Ast.wf args ->
  forall s' t',
    ST.instantiate_params_subst params args s t = Some (s', t') ->
    instantiate_params_subst (map trans_decl params)
                             (map trans args) (map trans s) (trans t) =
    Some (map trans s', trans t').
Proof.
  induction params in args, t, s |- *.
  - destruct args; simpl; rewrite ?Nat.add_0_r; intros Hparams Hs Hargs s' t' [= -> ->]; auto.
  - simpl. intros Hparams Hs Hargs s' t'.
    destruct a as [na [body|] ty]; simpl; try congruence.
    destruct t; simpl; try congruence.
    -- intros Ht' .
       erewrite <- IHparams. f_equal. 5:eauto.
       simpl. rewrite trans_subst; auto.
       inv Hparams. red in H. simpl in H. intuition auto.
       constructor; auto.
       inv Hparams; red in H; simpl in H; intuition auto.
       apply Template.LiftSubst.wf_subst; auto. solve_all.
       auto.
    -- intros Ht'. destruct t; try congruence.
       destruct args; try congruence; simpl.
       erewrite <- IHparams. 5:eauto. simpl. reflexivity.
       now inv Hparams.
       constructor; auto.
       now inv Hargs. now inv Hargs.
Qed.

Lemma trans_instantiate_params params args t :
  S.wf t ->
  All TypingWf.wf_decl params ->
  All Ast.wf args ->
  forall t',
    ST.instantiate_params params args t = Some t' ->
    instantiate_params (map trans_decl params) (map trans args) (trans t) =
    Some (trans t').
Proof.
  intros wft wfpars wfargs t' eq.
  revert eq.
  unfold ST.instantiate_params.
  case_eq (ST.instantiate_params_subst (List.rev params) args [] t).
  all: try discriminate.
  intros [ctx u] e eq. inversion eq. subst. clear eq.
  assert (wfargs' : Forall Ast.wf args) by (apply All_Forall ; assumption).
  assert (wfpars' : Forall wf_decl (List.rev params)).
  { apply rev_Forall. apply All_Forall. assumption. }
  assert (wfpars'' : All wf_decl (List.rev params)).
  { apply Forall_All. assumption. }
  apply wf_instantiate_params_subst_ctx in e as wfctx ; trivial.
  apply wf_instantiate_params_subst_term in e as wfu ; trivial.
  apply trans_instantiate_params_subst in e ; trivial.
  cbn in e. unfold instantiate_params.
  rewrite map_rev in e.
  rewrite e. f_equal. symmetry.
  apply trans_subst.
Qed.

Lemma trans_it_mkProd_or_LetIn ctx t :
  trans (Template.Ast.it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (map trans_decl ctx) (trans t).
Proof.
  induction ctx in t |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl; auto.
  now rewrite IHctx.
  now rewrite IHctx.
Qed.

Lemma trans_local_subst_instance_context :
  forall u Γ,
    trans_local (UnivSubst.subst_instance_context u Γ) =
    subst_instance_context u (trans_local Γ).
Proof.
  intros u Γ.
  induction Γ as [| [na [b|] A] Γ ih ] in u |- *.
  - reflexivity.
  - simpl. f_equal. 2: eapply ih.
    unfold map_decl. simpl.
    rewrite 2!trans_subst_instance_constr.
    reflexivity.
  - simpl. f_equal. 2: eapply ih.
    unfold map_decl. simpl.
    rewrite trans_subst_instance_constr.
    reflexivity.
Qed.

Lemma decompose_prod_assum_mkApps_nonnil ctx f args :
  args <> [] ->
  decompose_prod_assum ctx (mkApps f args) = (ctx, mkApps f args).
Proof.
  induction args => //.
  intros.
  rewrite mkApps_nonempty //.
Qed.

(* This is if Template's decompose_prod_assum handled casts. This does not work unless the specs 
  use a stronger decompose_prod_assum in PCUIC, as decompose_prod_assum is used to check fixpoints types. 
  Would be fixed having contexts instead of lambda abstractions in the Ast for fixpoints, where casts 
  cannot be introduced.
*)
(*Lemma trans_decompose_prod_assum :
  forall Γ t,
    let '(Δ, c) := AstUtils.decompose_prod_assum (S.map_context AstUtils.strip_casts Γ) (AstUtils.strip_casts t) in
    decompose_prod_assum (trans_local (S.map_context AstUtils.strip_casts Γ)) (trans (AstUtils.strip_casts t)) = 
      (trans_local Δ, trans c).
Proof.
  intros Γ t.
  destruct AstUtils.decompose_prod_assum as [Δ c] eqn:e.
  induction t in Γ, Δ, c, e |- *.
  (* all: simpl in *. *)
  all: try solve [ inversion e ; subst ; reflexivity ].
  - eapply IHt1 in e as e'. now simpl.
  - simpl. simpl in e. eapply (IHt2 (Γ ,, Ast.vass na t1)) in e as e'. assumption.
  - simpl. simpl in e. eapply (IHt3 (Γ ,, Ast.vdef na t1 t2)) in e as e'. assumption.
  - simpl in *. rewrite trans_mkApps.
    destruct args.
    * simpl. now apply IHt.
    * move: e. cbn [map].
      destruct (SL.mkApps_ex (AstUtils.strip_casts t) (AstUtils.strip_casts t0) (map AstUtils.strip_casts args)) as [f [? eq]].
      rewrite eq. intros [= <- <-]. rewrite -eq.
      rewrite decompose_prod_assum_mkApps_nonnil //.
      f_equal.
      now rewrite trans_mkApps.
Qed.
*)

Lemma trans_decompose_prod_assum :
  forall Γ t,
    S.wf t ->
    let '(Δ, c) := AstUtils.decompose_prod_assum Γ t in
    decompose_prod_assum (trans_local Γ) (trans t) = (trans_local Δ, trans c).
Proof.
  intros Γ t wf.
  destruct AstUtils.decompose_prod_assum as [Δ c] eqn:e.
  revert Γ Δ c e.
  induction wf using Template.Induction.term_wf_forall_list_ind; intros.
  all: try solve [ inversion e ; subst ; reflexivity ].
  - simpl in e. eapply IHwf0 in e as e'. now simpl.
  - simpl. simpl in e. eapply (IHwf1 (Γ ,, Ast.vdef n t t0)) in e as e'. assumption.
  - simpl in *. noconf e. simpl.
    destruct l => //.
    cbn [map].
    rewrite decompose_prod_assum_mkApps_nonnil //.
Qed.

(* Lemma trans_isApp t : Ast.isApp t = false -> PCUICAst.isApp (trans t) = false.
Proof.
  destruct t => //. simpl.
  now destruct prim as [? []].
Qed. *)
(* 
Lemma trans_decompose_app_args t f l : 
  Ast.wf t ->
  AstUtils.decompose_app t = (f, l) ->
  (decompose_app (trans t)).2 = map trans l.
Proof.
  induction 1 using Template.Induction.term_wf_forall_list_ind; simpl;
   intros [= <- <-]; auto. admit.
  rewrite decompose_app_mkApps. 
  destruct (AstUtils.decompose_app t).
Admitted. *)

Lemma trans_ind_params mdecl : trans_local (Ast.ind_params mdecl) = ind_params (trans_minductive_body mdecl).
Proof. reflexivity. Qed.

Lemma trans_ind_bodies mdecl : map trans_one_ind_body (Ast.ind_bodies mdecl) = ind_bodies (trans_minductive_body mdecl).
Proof. reflexivity. Qed.
From MetaCoq.PCUIC Require Import PCUICClosed PCUICInductiveInversion.

Lemma instantiate_params_spec params paramsi concl ty :
  instantiate_params params paramsi (it_mkProd_or_LetIn params concl) = Some ty ->
  ty = (subst (List.rev paramsi) 0 (expand_lets params concl)).
Proof.
  intros h. eapply instantiate_params_make_context_subst in h as [ctx'' [ms [s' [da [dp ->]]]]].
  eapply make_context_subst_spec in dp.
  rewrite List.rev_involutive in dp.
  pose proof (PCUICContexts.context_subst_length2 dp).
  rewrite decompose_prod_n_assum_it_mkProd app_nil_r in da. noconf da.
  apply context_subst_subst_extended_subst in dp as ->.
  rewrite map_subst_expand_lets ?List.rev_length //.
Qed.

Lemma trans_ind_bodies_length mdecl : #|TemplateEnvironment.ind_bodies mdecl| = #|ind_bodies (trans_minductive_body mdecl)|.
Proof. simpl. now rewrite map_length. Qed.

Lemma trans_ind_params_length mdecl : #|TemplateEnvironment.ind_params mdecl| = #|ind_params (trans_minductive_body mdecl)|.
Proof. simpl. now rewrite map_length. Qed.

Lemma trans_ind_npars mdecl : Ast.ind_npars mdecl = ind_npars (trans_minductive_body mdecl).
Proof. simpl. reflexivity. Qed.

Lemma trans_reln l p Γ : map trans (Ast.reln l p Γ) = 
  reln (map trans l) p (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ] in l, p |- *; simpl; auto.
  now rewrite IHΓ.
Qed.

Lemma trans_to_extended_list Γ n : map trans (Ast.to_extended_list_k Γ n) = to_extended_list_k (trans_local Γ) n.
Proof.
  now rewrite /to_extended_list_k trans_reln.
Qed.

Definition trans_constructor_shape (t : ST.constructor_shape) : constructor_shape :=
  {| cstr_args := trans_local t.(ST.cstr_args);
     cstr_indices := map trans t.(ST.cstr_indices); 
     cdecl_sorts := t.(ST.cdecl_sorts) |}.

Lemma trans_cstr_args cs : trans_local (ST.cstr_args cs) = cstr_args (trans_constructor_shape cs).
Proof. reflexivity. Qed.

Lemma trans_cstr_args_length cs : #|ST.cstr_args cs| = #|cstr_args (trans_constructor_shape cs)|.
Proof. now rewrite -trans_cstr_args map_length. Qed.

Lemma context_assumptions_map ctx : context_assumptions (map trans_decl ctx) = Ast.context_assumptions ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx]; simpl; auto.
Qed.

(* Lemma decompose_prod_assum_mkApps ctx t f l : 
  decompose_prod_assum ctx t = (ctx', l) ->
  it_mkProd_or_LetIn ctx t = it_mkProd_or_LetIn ctx' (mkApps t' -> 
  () *)
(* 
Lemma decompose_app_trans_inv t ind u l :
  Ast.wf t ->
  decompose_app (trans t) = (tInd ind u, l) -> 
  ∑ l', l = map trans l' /\ AstUtils.decompose_app t = (Ast.tInd ind u, l').
Proof.
  destruct t => //. simpl.
  intros wf.
  destruct decompose_app eqn:da.
  pose proof (decompose_app_notApp _ _ _ da).
  rewrite decompose_app_mkApps in da. depelim wf. destruct t => //.
  destruct t0 => //.
  intros [= -> -> ->].
  exists args. noconf da. split; auto. f_equal. rewrite -H0 in H.
  depelim wf.
  destruct t => //. simpl in H2. noconf H2. reflexivity.
  intros. simpl in H0. noconf H0.
  exists []. split; auto.
Qed. *)
Lemma trans_build_branches_type ind mdecl idecl args u p brtys :
  (* (ST.on_inductive (ST.lift_typing ST.typing) Σ (inductive_mind ind) mdecl) ->
  (ST.on_ind_body (ST.lift_typing ST.typing) Σ (inductive_mind ind) mdecl (inductive_ind ind) idecl) ->
  inductive_ind ind < #|ind_bodies (trans_minductive_body mdecl)| -> *)
  map_option_out (ST.build_branches_type ind mdecl idecl args u p)
  = Some brtys ->
  map_option_out
    (build_branches_type ind (trans_minductive_body mdecl)
      (trans_one_ind_body idecl) (map trans args) u
      (trans p))
  = Some (map (on_snd trans) brtys).
Proof.
Admitted.
(* Will likely change with the change of representation of cases *)
(*
  intros onmind onind indlt.
  pose proof (ST.onConstructors onind) as onc.
  unfold ST.build_branches_type.
  unfold build_branches_type.
  rewrite mapi_map.
  eapply All2_map_option_out_mapi_Some_spec. eapply onc.
  intros i [[id ty] argn] [nargs br] s oncs.
  simpl.
  destruct ST.instantiate_params eqn:ipars => //.
  pose proof ipars as ipars'.
  apply trans_instantiate_params in ipars.
  rewrite trans_subst trans_inds trans_subst_instance_constr in ipars.
  rewrite [map _ _]trans_local_subst_instance_context trans_ind_params
    trans_ind_bodies in ipars.
  
  rewrite trans_ind_params trans_ind_bodies.
  rewrite ipars.
  assert (wft : S.wf t). eapply wf_instantiate_params. 4:eapply ipars'. 1-3:admit.
  pose proof (trans_decompose_prod_assum [] t wft).
  destruct (AstUtils.decompose_prod_assum [] t) eqn:da'.
  rewrite H.
  destruct chop eqn:eqchop.
  intros [= -> <-].
  destruct (chop _ (decompose_app (trans t0)).2) eqn:c'.
  f_equal. f_equal.
  rewrite [ty]oncs.(ST.cstr_eq) in ipars.
  rewrite trans_it_mkProd_or_LetIn subst_instance_constr_it_mkProd_or_LetIn 
    subst_it_mkProd_or_LetIn in ipars. len in ipars.
  rewrite closed_ctx_subst in ipars.
  rewrite [map _ _]trans_ind_params. admit.
  apply instantiate_params_spec in ipars.
  rewrite trans_it_mkProd_or_LetIn. f_equal.
  rewrite trans_mkApps map_length trans_lift. f_equal.
  rewrite map_app /= trans_mkApps /= map_app trans_to_extended_list.
  assert (l1 = map trans l /\ l2 = map trans l0) as [-> ->].
  { simpl in H.
    move: ipars.
    rewrite trans_it_mkProd_or_LetIn subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
    rewrite /expand_lets expand_lets_it_mkProd_or_LetIn. len.
    rewrite subst_it_mkProd_or_LetIn.
    rewrite trans_mkApps.
    rewrite /ST.cstr_concl_head. cbn -[subst].
    rewrite trans_ind_bodies. len.
    rewrite trans_ind_bodies_length trans_ind_params_length.
    rewrite map_app trans_to_extended_list trans_ind_params trans_cstr_args_length.
    rewrite (subst_cstr_concl_head ind u (trans_minductive_body mdecl)) //.
    rewrite expand_lets_k_mkApps subst_mkApps /=.
    intros eqit.
    rewrite eqit in H.
    rewrite decompose_prod_assum_it_mkProd // in H.
    apply is_ind_app_head_mkApps.
    injection H. clear H. rewrite app_nil_r.
    intros eqind _.
    apply (f_equal decompose_app) in eqind.
    destruct (decompose_app (trans t0)) eqn:dt0.
    simpl in *.
    rewrite decompose_app_mkApps // in eqind. noconf eqind.

    noconf H.
    move: H.
    
    rewrite !map_app map_map_compose chop_n_app. len.
    rewrite context_assumptions_map. now rewrite onmind.(ST.onNpars).
    destruct AstUtils.decompose_prod_assum eqn:da'.
    rewrite trans_it_mkProd_or_LetIn trans_mkApps. len.
    simpl in H. rewrite H.
  


  reflexivity.





  f_equal. f_equal. rewrite map_app.
  rewrite trans_to_extended_list. f_equal.



  len.


  apply instantiate_params_make_context_subst in ipars as [ctx' [ty'' [s' [dass [makes eq]]]]].
  rewrite eq.
  eapply make_context_subst_spec in makes.
  rewrite List.rev_involutive in makes.



  move: (trans_decompose_prod_assum [] t wft).
  destruct oncs. simpl in cstr_eq.
  rewrite trans_inds in ipars.
  rewrite trans_subst_instance_constr in ipars.   
  intros [= -> <-].

  destruct AstUtils.decompose_prod_assum eqn:dp => -> /=.
  destruct (AstUtils.decompose_app t0) eqn:da'. simpl.
  destruct chop as [params argsl] eqn:ceq.
  
  rewrite (chop_map _ _ _ _ _ ceq).
  intros [= ->]. f_equal. unfold on_snd. simpl. f_equal. subst br.
  rewrite trans_it_mkProd_or_LetIn trans_mkApps map_app /= trans_mkApps /= map_app.
  now rewrite trans_to_extended_list trans_lift map_length.
Qed.
*)

Lemma trans_build_case_predicate_type ind mdecl idecl params u ps :
  build_case_predicate_type ind (trans_minductive_body mdecl)
                            (trans_one_ind_body idecl) (map trans params) u ps
  = option_map trans (ST.build_case_predicate_type ind mdecl idecl params u ps).
Admitted.

(* Lemma trans_types_of_case (Σ : S.global_env) ind mdecl idecl args p u pty indctx pctx ps btys : *)
(*   S.wf p -> S.wf pty -> S.wf (S.ind_type idecl) -> *)
(*   All S.wf args -> *)
(*   ST.wf Σ -> *)
(*   ST.declared_inductive Σ ind mdecl idecl -> *)
(*   ST.types_of_case ind mdecl idecl args u p pty = Some (indctx, pctx, ps, btys) -> *)
(*   types_of_case ind (trans_minductive_body mdecl) (trans_one_ind_body idecl) *)
(*   (map trans args) u (trans p) (trans pty) = *)
(*   Some (trans_local indctx, trans_local pctx, ps, map (on_snd trans) btys). *)
(* Proof. *)
(*   intros wfp wfpty wfdecl wfargs wfΣ Hidecl. *)
(*   pose proof (on_declared_inductive wfΣ as Hidecl) [onmind onind]. *)
(*   apply ST.onParams in onmind as Hparams. *)
(*   (* Maybe have a lemma for this we do it all the time *) *)
(*   assert (wc : Forall wf_decl (UnivSubst.subst_instance_context u (S.ind_params mdecl))). *)
(*   { assert (h : Forall wf_decl (S.ind_params mdecl)). *)
(*     { eapply typing_all_wf_decl ; revgoals. *)
(*       - apply ST.onParams in onmind. *)
(*         unfold ST.on_context in onmind. *)
(*         eassumption. *)
(*       - simpl. assumption. *)
(*     } *)
(*     clear - h. induction h. 1: constructor. *)
(*     simpl. constructor. 2: assumption. *)
(*     destruct x as [na [bo|] ty]. *)
(*     all: unfold map_decl. all: unfold wf_decl in *. all: simpl in *. *)
(*     all: intuition eauto with wf. *)
(*   } *)
(*   assert (closedparams : Closed.closed_ctx (Ast.ind_params mdecl)). *)
(*   { eapply closed_wf_local ; eauto. eauto. } *)
(*   assert (wfparams : All wf_decl (Ast.ind_params mdecl)). *)
(*   { apply Forall_All. eapply typing_all_wf_decl ; eauto. simpl. eauto. } *)
(*   unfold ST.types_of_case, types_of_case. simpl. *)
(*   match goal with *)
(*   | |- context [ ST.instantiate_params ?p ?a ?t ] => *)
(*     pose proof (trans_instantiate_params p a t) as ht ; *)
(*     case_eq (ST.instantiate_params p a t) *)
(*   end. *)
(*   2: discriminate. *)
(*   intros ity e. *)
(*   rewrite e in ht. specialize ht with (4 := eq_refl). *)
(*   change (map trans_decl) with trans_local in ht. *)
(*   rewrite trans_subst_instance_constr in ht. *)
(*   rewrite trans_local_subst_instance_context in ht. *)
(*   rewrite ht. *)
(*   all: auto using Forall_All with wf. *)
(*   apply wf_instantiate_params in e as wfity. *)
(*   all: auto with wf. *)
(*   pose proof (trans_destArity [] ity wfity) as e'. *)
(*   destruct ST.destArity as [[ctx s] | ]. 2: discriminate. *)
(*   rewrite e'. *)
(*   pose proof (trans_destArity [] pty wfpty) as e''. *)
(*   destruct ST.destArity as [[ctx' s'] | ]. 2: discriminate. *)
(*   simpl in e''. rewrite e''. *)
(*   pose proof (ST.onConstructors onind) as onc. *)
(*   assert ( *)
(*     hb : *)
(*       forall brtys, *)
(*         map_option_out (ST.build_branches_type ind mdecl idecl args u p) *)
(*         = Some brtys -> *)
(*         map_option_out *)
(*           (build_branches_type ind (trans_minductive_body mdecl) *)
(*             (trans_one_ind_body idecl) (map trans args) u *)
(*             (trans p)) *)
(*         = Some (map (on_snd trans) brtys) *)
(*   ). *)
(*   { intro brtys. *)
(*     unfold ST.build_branches_type, build_branches_type. *)
(*     unfold trans_one_ind_body. simpl. rewrite -> mapi_map. *)
(*     unfold ST.on_constructors in onc. *)
(*     eapply All2_map_option_out_mapi_Some_spec. *)
(*     - eapply onc. *)
(*     - intros i [[id t] n] [t0 ar] z. *)
(*       unfold on_snd. simpl. *)
(*       intros [ont [cs ?]]. simpl in *. *)
(*       unfold ST.on_type in ont. simpl in ont. *)
(*       destruct ont. *)
(*       unfold ST.instantiate_params, instantiate_params. *)
(*       destruct ST.instantiate_params_subst eqn:he. 2: discriminate. *)
(*       destruct p0 as [s0 ty]. *)
(*       apply instantiate_params_subst_make_context_subst in he as he'. *)
(*       destruct he' as [ctx'' hctx'']. *)
(*       eapply trans_instantiate_params_subst in he. *)
(*       2: eapply All_rev. *)
(*       all: auto using Forall_All with wf. *)
(*       simpl in he. *)
(*       rewrite map_rev in he. *)
(*       rewrite trans_subst in he. *)
(*       + auto using Forall_All with wf. *)
(*       + apply wf_subst_instance_constr. *)
(*         now eapply typing_wf in t2. *)
(*       + rewrite trans_subst_instance_constr trans_inds in he. *)
(*         change (map trans_decl) with trans_local in he. *)
(*         rewrite trans_local_subst_instance_context in he. *)
(*         rewrite he. *)

(*         rewrite List.rev_length map_length in hctx''. *)

(*         (* apply PCUICSubstitution.instantiate_params_subst_make_context_subst *)
(*           in he as [ctx''' [hs0 hdecomp]]. *)
(*         rewrite List.rev_length map_length in hdecomp. *)
(*         unfold trans_local in hdecomp. *)
(*         rewrite map_length in hdecomp. *) *)
(*         (* rewrite !Template.UnivSubst.subst_instance_constr_it_mkProd_or_LetIn *)
(*           in hdecomp. *) *)


(*   (* apply PCUICSubstitution.instantiate_params_subst_make_context_subst in Heq. *) *)
(*   (* destruct Heq as [ctx''' [Hs0 Hdecomp]]. *) *)
(*   (* rewrite List.rev_length map_length in Hdecomp. *) *)
(*   (* rewrite <- trans_subst_instance_constr in Hdecomp. *) *)
(*   (* rewrite !Template.UnivSubst.subst_instance_constr_it_mkProd_or_LetIn in Hdecomp. *) *)
(*   (* rewrite !trans_it_mkProd_or_LetIn in Hdecomp. *) *)
(*   (* assert (#|Template.Ast.ind_params mdecl| = *) *)
(*   (*   #|PCUICTyping.subst_context *) *)
(*   (*     (inds (inductive_mind ind) u (map trans_one_ind_body (Template.Ast.ind_bodies mdecl))) 0 *) *)
(*   (*     (map trans_decl (Template.UnivSubst.subst_instance_context u (Template.Ast.ind_params mdecl)))|). *) *)
(*   (* now rewrite PCUICSubstitution.subst_context_length map_length Template.UnivSubst.subst_instance_context_length. *) *)
(*   (* rewrite H1 in Hdecomp. *) *)
(*   (* rewrite PCUICSubstitution.subst_it_mkProd_or_LetIn in Hdecomp. *) *)
(*   (* rewrite decompose_prod_n_assum_it_mkProd in Hdecomp. *) *)
(*   (* injection Hdecomp. intros <- <-. clear Hdecomp. *) *)

(*   (* subst cdecl_concl_head. destruct Hctx''. *) *)

(*   (* admit. admit. admit. admit. congruence. *) *)
(*   (* revert H1. destruct map_option_out. intros. *) *)
(*   (* specialize (H1 _ eq_refl). rewrite H1. *) *)
(*   (* congruence. *) *)
(*   (* intros. discriminate. *) *)

(*         admit. *)
(*   } *)
(*   match goal with *)
(*   | |- context [ map_option_out ?t ] => *)
(*     destruct (map_option_out t) eqn: e1 *)
(*   end. 2: discriminate. *)
(*   specialize hb with (1 := eq_refl). *)
(*   rewrite hb. *)
(*   intro h. apply some_inj in h. *)
(*   inversion h. subst. *)
(*   reflexivity. *)
(* Admitted. *)

Hint Constructors S.wf : wf.

Hint Resolve Template.TypingWf.typing_wf : wf.

Lemma mkApps_trans_wf U l : S.wf (S.tApp U l) -> exists U' V', trans (S.tApp U l) = tApp U' V'.
Proof.
  simpl. induction l using rev_ind. intros. inv H. congruence.
  intros. rewrite map_app. simpl. exists (mkApps (trans U) (map trans l)), (trans x).
  clear. revert U x ; induction l. simpl. reflexivity.
  simpl. intros.
  rewrite mkApps_app. simpl. reflexivity.
Qed.

Derive Signature for SEq.eq_term_upto_univ_napp.

Lemma leq_term_mkApps {cf} Σ ϕ t u t' u' :
  eq_term Σ ϕ t t' -> All2 (eq_term Σ ϕ) u u' ->
  leq_term Σ ϕ (mkApps t u) (mkApps t' u').
Proof.
  intros Hn Ht.
  revert t t' Ht Hn; induction u in u' |- *; intros.

  inversion_clear Ht.
  simpl. apply eq_term_leq_term. assumption.

  inversion_clear Ht.
  simpl in *. apply IHu. assumption. constructor; auto.
  now apply eq_term_eq_term_napp.
Qed.

Lemma eq_term_upto_univ_App `{checker_flags} Σ Re Rle f f' napp :
  eq_term_upto_univ_napp Σ Re Rle napp f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps `{checker_flags} Σ Re Rle f l f' l' :
  eq_term_upto_univ_napp Σ Re Rle #|l| f f' ->
  All2 (eq_term_upto_univ Σ Re Re) l l' ->
  eq_term_upto_univ Σ Re Rle (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f', l' |- *; intro e; inversion_clear 1.
  - assumption.
  - pose proof (eq_term_upto_univ_App _ _ _ _ _ _ e).
    case_eq (isApp f).
    + intro X; rewrite X in H0.
      destruct f; try discriminate.
      destruct f'; try discriminate.
      cbn. inversion_clear e. eapply IHl.
      * repeat constructor ; eauto.
      * assumption.
    + intro X; rewrite X in H0. simpl.
      eapply IHl.
      * constructor. all: eauto.
      * assumption.
Qed.

Lemma trans_lookup Σ cst :
  lookup_env (trans_global_decls Σ) cst = option_map trans_global_decl (Ast.lookup_env Σ cst).
Proof.
  cbn in *.
  induction Σ.
  - reflexivity.
  - cbn.
    unfold eq_kername in *; destruct kername_eq_dec; subst.
    + destruct a; auto.
    + now rewrite IHΣ.
Qed.

Lemma on_global_env_impl `{checker_flags} Σ P Q :
  (forall Σ Γ t T, ST.on_global_env P Σ.1 -> P Σ Γ t T -> Q Σ Γ t T) ->
  ST.on_global_env P Σ -> ST.on_global_env Q Σ.
Proof.
  intros X X0.
  simpl in *. induction X0; constructor; auto.
  clear IHX0. destruct d; simpl.
  - destruct c; simpl. destruct cst_body; simpl in *.
    red in o |- *. simpl in *. now eapply X.
    red in o |- *. simpl in *. now eapply X.
  - red in o. simpl in *.
    destruct o0 as [onI onP onNP].
    constructor; auto.
    -- eapply Alli_impl. exact onI. eauto. intros.
       refine {| ST.ind_indices := X1.(ST.ind_indices);
                 ST.ind_arity_eq := X1.(ST.ind_arity_eq);
                 ST.ind_cunivs := X1.(ST.ind_cunivs) |}.
       --- apply ST.onArity in X1. unfold on_type in *; simpl in *.
           now eapply X.
       --- pose proof X1.(ST.onConstructors) as X11. red in X11.
          eapply All2_impl; eauto.
          simpl. intros. destruct X2 as [? ? ? ?]; unshelve econstructor; eauto.
          * apply X; eauto.
          * clear -X0 X on_cargs. revert on_cargs.
            generalize (ST.cstr_args y), (ST.cdecl_sorts y).
            induction c; destruct l; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
          split; intuition eauto.
          * clear -X0 X on_cindices.
            revert on_cindices.
            generalize (List.rev (SL.lift_context #|ST.cstr_args y| 0 (ST.ind_indices X1))).
            generalize (ST.cstr_indices y).
            induction 1; simpl; constructor; auto.
       --- simpl; intros. pose (ST.onProjections X1 H0). simpl in *; auto.
       --- destruct X1. simpl. unfold ST.check_ind_sorts in *.
           destruct Universe.is_prop, Universe.is_sprop; auto.
           split.
           * apply ind_sorts.
           * destruct indices_matter; auto.
             eapply ST.type_local_ctx_impl. eapply ind_sorts. auto.
      --- eapply X1.(ST.onIndices).
    -- red in onP. red.
       eapply ST.All_local_env_impl. eauto.
       intros. now apply X.
Qed.

Lemma typing_wf_wf {cf}:
  forall (Σ : Template.Ast.global_env),
    ST.wf Σ ->
    ST.Forall_decls_typing
      (fun (_ : Template.Ast.global_env_ext) (_ : Tcontext) (t T : Tterm) => Ast.wf t /\ Ast.wf T) Σ.
Proof.
  intros Σ.
  eapply on_global_env_impl. clear.
  intros Σ Γ t S.
  red. unfold ST.lift_typing.
  intros ong. destruct S.
  * intros ty. now eapply typing_wf.
  * intros [s ty]. exists s.
    now eapply typing_wf in ty.
Qed.

Lemma trans_R_global_instance {cf} Σ Re Rle gref napp u u' :
  ST.wf Σ ->
  SEq.R_global_instance Σ Re Rle gref napp u u' ->
  R_global_instance (trans_global_decls Σ) Re Rle gref napp u u'.
Proof.
  intros wfe.
  unfold PCUICEquality.R_global_instance, PCUICEquality.global_variance.
  unfold SEq.R_global_instance, SEq.global_variance.
  destruct gref; simpl; auto.
  - unfold PCUICEquality.lookup_inductive, PCUICEquality.lookup_minductive.
    unfold SEq.lookup_inductive, SEq.lookup_minductive.
    rewrite trans_lookup. destruct Ast.lookup_env eqn:look => //; simpl.
    destruct g => /= //.
    rewrite nth_error_map.
    destruct nth_error eqn:hnth => /= //.
    assert (wfty : Ast.wf (Ast.ind_type o)).
    { eapply declared_inductive_wf; eauto. eapply typing_wf_wf; eauto. split; eauto. }
    move: (trans_destArity [] (Ast.ind_type o) wfty).
    destruct AstUtils.destArity as [[ctx ps]|] eqn:eq => /= // -> //.
    now rewrite context_assumptions_map.
  - unfold PCUICEquality.lookup_constructor, PCUICEquality.lookup_inductive, PCUICEquality.lookup_minductive.
    unfold SEq.lookup_constructor, SEq.lookup_inductive, SEq.lookup_minductive.
    rewrite trans_lookup. destruct Ast.lookup_env => //; simpl.
    destruct g => /= //. rewrite nth_error_map.
    destruct nth_error => /= //.
    rewrite nth_error_map.
    destruct nth_error => /= //.
    destruct p as [[id t] nargs]; simpl.
    destruct Nat.leb => //.
Qed.

Ltac tc := typeclasses eauto.

(* TODO update Template Coq's eq_term to reflect PCUIC's cumulativity *)
Lemma trans_eq_term_upto_univ {cf} :
  forall Σ Re Rle t u napp,
  RelationClasses.subrelation Re Rle ->
  ST.wf Σ ->
  S.wf t ->
    S.wf u ->
    SEq.eq_term_upto_univ_napp Σ Re Rle napp t u ->
    eq_term_upto_univ_napp (trans_global_decls Σ) Re Rle napp (trans t) (trans u).
Proof.
  intros Σ Re Rle t u napp sub wfΣ wt wu e.
  induction t using Induction.term_forall_list_rect in sub, Rle, napp, wt, u, wu, e |- *.
  all: invs e; cbn.
  all: try solve [ constructor ; auto ].
  all: repeat (match goal with 
    | H : S.wf (_ _) |- _ => apply wf_inv in H; simpl in H
    | H : _ /\ _ |- _ => destruct H
  end).
  all: try solve [
    repeat constructor ; auto ;
    match goal with
    | ih : forall Rle (u : Tterm) (napp : nat), _ |- _ =>
      now eapply ih
    end
  ].
  - constructor.
    apply Forall_All in wt.
    apply Forall_All in wu.
    pose proof (All2_All_mix_left X X0) as h1. simpl in h1.
    pose proof (All2_All_mix_left wt h1) as h2.
    pose proof (All2_All_mix_right wu h2) as h3.
    simpl in h3.
    eapply All2_map.
    eapply All2_impl. 1: exact h3.
    simpl.
    intros ? ? [[? [ih ?]] ?].
    simpl in *.
    eapply ih. all: auto. tc.
  - eapply eq_term_upto_univ_napp_mkApps.
    + rewrite map_length. now eapply IHt.
    + pose proof (All2_All_mix_left X X1) as h.
      simpl in h.
      apply Forall_All in H6.
      apply Forall_All in H2.
      pose proof (All2_All_mix_left H6 h) as h1.
      pose proof (All2_All_mix_right H2 h1) as h2.
      simpl in h2.
      eapply All2_map.
      eapply All2_impl. 1: exact h2.
      simpl.
      intros u v [[? [ih ?]] ?].
      eapply ih. all: auto; tc.
  - constructor. apply trans_R_global_instance; auto.
  - constructor. apply trans_R_global_instance; auto.
  - constructor. all: try solve [
      match goal with
      | ih : forall Rle u, _ |- _ =>
        now eapply ih
      end
    ].
    assert (wl : All (S.wf ∘ snd) l) by solve_all.
    assert (wbrs' : All (S.wf ∘ snd) brs') by solve_all.
    pose proof (All2_All_mix_left X X2) as h1. simpl in h1.
    pose proof (All2_All_mix_left wl h1) as h2.
    pose proof (All2_All_mix_right wbrs' h2) as h3.
    simpl in h3.
    eapply All2_map.
    eapply All2_impl. 1: exact h3.
    simpl.
    intros [n u] [m v] [[? [ih [? ?]]] ?]. simpl in *.
    intuition eauto. now apply ih.
  - constructor.
    assert (
      w1 :
        All (fun def =>
          S.wf (dtype def) /\
          S.wf (dbody def)
        ) m
    ).
    { solve_all. }
    assert (
      w2 :
        All (fun def =>
          S.wf (dtype def) /\
          S.wf (dbody def)) mfix'
    ).
    { solve_all. }
    pose proof (All2_All_mix_left X X0) as h1. simpl in h1.
    pose proof (All2_All_mix_left w1 h1) as h2.
    pose proof (All2_All_mix_right w2 h2) as h3.
    simpl in h3.
    eapply All2_map.
    eapply All2_impl. 1: exact h3.
    simpl.
    intros [? ? ? ?] [? ? ? ?] [[[? ?] [[ih1 ih2] [? ?]]] [? ?]].
    simpl in *.
    intuition eauto. now eapply ih1. now eapply ih2.
  - constructor.
    assert (
      w1 :
        All (fun def => S.wf (dtype def) /\ S.wf (dbody def)) m
    ).
    { by eapply Forall_All. }
    assert (
      w2 :
        All (fun def => S.wf (dtype def) /\ S.wf (dbody def)) mfix'
    ).
    { by eapply Forall_All. }
    pose proof (All2_All_mix_left X X0) as h1. simpl in h1.
    pose proof (All2_All_mix_left w1 h1) as h2.
    pose proof (All2_All_mix_right w2 h2) as h3.
    simpl in h3.
    eapply All2_map.
    eapply All2_impl. 1: exact h3.
    simpl.
    intros [? ? ? ?] [? ? ? ?] [[[? ?] [[ih1 ih2] [? ?]]] [? ?]].
    simpl in *.
    intuition eauto. now eapply ih1. now eapply ih2.
Qed.

Lemma trans_leq_term {cf} Σ ϕ T U :
  ST.wf Σ ->
  S.wf T -> S.wf U -> SEq.leq_term Σ ϕ T U ->
  leq_term (trans_global_decls Σ) ϕ (trans T) (trans U).
Proof.
  intros HT HU H.
  eapply trans_eq_term_upto_univ ; eauto. tc.
Qed.

Lemma trans_eq_term {cf} Σ φ t u :
  ST.wf Σ ->
  S.wf t -> S.wf u -> SEq.eq_term Σ φ t u ->
  eq_term (trans_global_decls Σ) φ (trans t) (trans u).
Proof.
  intros HT HU H.
  eapply trans_eq_term_upto_univ ; eauto. tc.
Qed.

Lemma trans_eq_term_list {cf}:
  forall Σ φ l l',
    ST.wf Σ ->
    List.Forall S.wf l ->
    List.Forall S.wf l' ->
    All2 (SEq.eq_term Σ φ) l l' ->
    All2 (eq_term (trans_global_decls Σ) φ) (List.map trans l) (List.map trans l').
Proof.
  intros Σ φ l l' wfΣ w w' h.
  eapply All2_map.
  apply Forall_All in w. apply Forall_All in w'.
  pose proof (All2_All_mix_left w h) as h1.
  pose proof (All2_All_mix_right w' h1) as h2.
  simpl in h2.
  apply (All2_impl h2).
  intuition auto using trans_eq_term.
Qed.

(* Lemma wf_mkApps t u : S.wf (S.mkApps t u) -> List.Forall S.wf u. *)
(* Proof. *)
(*   induction u in t |- *; simpl. *)
(*   - intuition. *)
(*   - intros H; destruct t; try solve [inv H; intuition auto]. *)
(*     specialize (IHu (S.tApp t (l ++ [a]))). *)
(*     forward IHu. *)
(*     induction u; trivial. *)
(*     simpl. rewrite <- app_assoc. simpl. apply H. *)
(*     intuition. inv H. *)
(*     apply Forall_app in H3. intuition. *)
(* Qed. *)
(* Hint Resolve wf_mkApps : wf. *)

Lemma trans_nth n l x : trans (nth n l x) = nth n (List.map trans l) (trans x).
Proof.
  induction l in n |- *; destruct n; trivial.
  simpl in *. congruence.
Qed.

Lemma trans_iota_red pars c args brs :
  trans (ST.iota_red pars c args brs) =
  iota_red pars c (List.map trans args) (List.map (on_snd trans) brs).
Proof.
  unfold ST.iota_red, iota_red.
  rewrite trans_mkApps.
  f_equal. induction brs in c |- *; simpl; destruct c; trivial.
    now rewrite map_skipn.
Qed.

Lemma trans_isLambda t :
  S.wf t -> isLambda (trans t) = Ast.isLambda t.
Proof.
  destruct 1; cbnr.
  destruct u; [contradiction|]. cbn.
  generalize (map trans u) (trans t) (trans t0); clear.
  induction l; intros; cbnr. apply IHl.
Qed.

Lemma trans_unfold_fix mfix idx narg fn :
  List.Forall (fun def : def Tterm => S.wf (dtype def) /\ S.wf (dbody def)) mfix ->
  ST.unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold ST.unfold_fix, unfold_fix. intros wffix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  cbn.
  intros [= <- <-]. simpl.
  repeat f_equal.
  rewrite trans_subst.
  f_equal. clear Hdef.
  unfold fix_subst, ST.fix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction wffix; trivial.
  simpl; intros mfix. f_equal.
  eapply (IHwffix mfix).
Qed.

Lemma trans_unfold_cofix mfix idx narg fn :
  List.Forall (fun def : def Tterm => S.wf (dtype def) /\ S.wf (dbody def)) mfix ->
  ST.unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold ST.unfold_cofix, unfold_cofix. intros wffix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef.
  intros [= <- <-]. simpl. repeat f_equal.
  rewrite trans_subst.
  f_equal. clear Hdef.
  unfold cofix_subst, ST.cofix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction wffix; trivial.
  simpl; intros mfix. f_equal.
  eapply (IHwffix mfix). congruence.
Qed.

Definition isApp t := match t with tApp _ _ => true | _ => false end.

Lemma trans_is_constructor:
  forall (args : list Tterm) (narg : nat),
    ST.is_constructor narg args = true -> is_constructor narg (map trans args) = true.
Proof.
  intros args narg.
  unfold ST.is_constructor, is_constructor.
  rewrite nth_error_map. destruct nth_error. simpl. intros.
  destruct t; try discriminate || reflexivity. simpl in H.
  destruct t; try discriminate || reflexivity.
  simpl. unfold isConstruct_app.
  unfold decompose_app. rewrite decompose_app_rec_mkApps. now simpl.
  congruence.
Qed.

Lemma refine_red1_r Σ Γ t u u' : u = u' -> red1 Σ Γ t u -> red1 Σ Γ t u'.
Proof.
  intros ->. trivial.
Qed.

Lemma refine_red1_Γ Σ Γ Γ' t u : Γ = Γ' -> red1 Σ Γ t u -> red1 Σ Γ' t u.
Proof.
  intros ->. trivial.
Qed.
Ltac wf_inv H := try apply wf_inv in H; simpl in H; rdest.

Lemma wf_wf_decl_pred {cf} Σ : ST.wf Σ -> Typing.on_global_env (fun _ => wf_decl_pred) Σ.
Proof.
  move/typing_wf_wf.
  apply on_global_env_impl.
  intros.
  destruct T; simpl in *; auto.
  destruct X0 as [s [Ht Hs]].
  red. split; auto.
Qed.
Hint Resolve wf_wf_decl_pred : wf.

Lemma trans_red1 {cf} Σ Γ T U :
  ST.wf Σ ->
  List.Forall wf_decl Γ ->
  S.wf T ->
  ST.red1 Σ Γ T U ->
  red1 (map (on_snd trans_global_decl) Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  intros wfΣ wfΓ Hwf.
  induction 1 using ST.red1_ind_all; wf_inv Hwf; simpl in *;
    try solve [econstructor; eauto].

  - simpl. wf_inv H1. apply Forall_All in H2. inv H2.
    rewrite trans_mkApps; auto.
    rewrite trans_subst; auto. apply red1_mkApps_l. constructor.

  - rewrite trans_subst; eauto. repeat constructor.

  - rewrite trans_lift; eauto.
    destruct nth_error eqn:Heq.
    econstructor. unfold trans_local. rewrite nth_error_map. rewrite Heq. simpl.
    destruct c; simpl in *. injection H; intros ->. simpl. reflexivity.
    econstructor. simpl in H. discriminate.

  - rewrite trans_mkApps; eauto with wf; simpl.
    erewrite trans_iota_red; eauto. repeat constructor.

  - simpl. rewrite trans_mkApps.
    eapply red_fix. wf_inv H3.
    apply trans_unfold_fix; eauto.
    now apply trans_is_constructor.

  - apply wf_mkApps_napp in H1; auto.
    intuition.
    pose proof (unfold_cofix_wf _ _ _ _ H H3). wf_inv H3.
    rewrite !trans_mkApps; eauto with wf.
    apply trans_unfold_cofix in H; eauto with wf.
    eapply red_cofix_case; eauto.

  - eapply wf_mkApps_napp in Hwf; auto.
    intuition. pose proof (unfold_cofix_wf _ _ _ _ H H0). wf_inv H0.
    rewrite !trans_mkApps; intuition eauto with wf.
    eapply red_cofix_proj; eauto.
    apply trans_unfold_cofix; eauto with wf.

  - rewrite trans_subst_instance_constr. econstructor.
    apply (forall_decls_declared_constant _ c decl H).
    destruct decl. now simpl in *; subst cst_body.

  - rewrite trans_mkApps; eauto with wf.
    simpl. constructor. now rewrite nth_error_map H.

  - constructor. apply IHX. constructor; hnf; simpl; auto. hnf. auto.

  - constructor. apply IHX. constructor; hnf; simpl; auto. auto.

  - constructor. solve_all.
    apply OnOne2_map. apply (OnOne2_All_mix_left H1) in X. clear H1.
    solve_all. red. simpl in *.
    intuition eauto.
    apply b2. all: solve_all.

  - rewrite !trans_mkApps; auto with wf. eapply wf_red1 in X; auto with wf.
    apply red1_mkApps_l. auto.

  - apply Forall_All in H2. clear H H0 H1. revert M1. induction X.
    simpl. intuition. inv H2. specialize (X H).
    apply red1_mkApps_l. apply app_red_r. auto.
    inv H2. specialize (IHX X0).
    simpl. intros.
    eapply (IHX (S.tApp M1 [hd])).

  - constructor. apply IHX. constructor; hnf; simpl; auto. auto.
  - constructor. induction X; simpl; repeat constructor. apply p; auto. now inv Hwf.
    apply IHX. now inv Hwf.

  - constructor. constructor. eapply IHX; auto.
  - eapply refine_red1_r; [|constructor]. unfold subst1. simpl. now rewrite lift0_p.

  - constructor. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody.
    inversion b0. clear b0.
    intuition eauto.
    + eapply b. all: solve_all.
    + unfold map_def. simpl.
      f_equal. 2: auto.
      f_equal. assumption.

  - apply fix_red_body. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
    + unfold Template.Ast.app_context, trans_local in b.
      simpl in a. rewrite -> map_app in b.
      unfold app_context. unfold ST.fix_context in b.
      rewrite map_rev map_mapi in b. simpl in b.
      unfold fix_context. rewrite mapi_map. simpl.
      forward b.
      { clear b. solve_all. eapply All_app_inv; auto.
        apply All_rev. apply All_mapi.
        clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
        intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
        now eapply LiftSubst.wf_lift.
        depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
      }
      forward b by auto.
      eapply (refine_red1_Γ); [|apply b].
      f_equal. f_equal. apply mapi_ext; intros [] [].
      rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity.
      rewrite trans_lift. simpl. reflexivity.
    + simpl. inversion b0. reflexivity.

  - constructor. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody.
    inversion b0. clear b0.
    intuition eauto.
    + eapply b. all: solve_all.
    + unfold map_def. simpl.
      f_equal. 2: auto.
      f_equal. assumption.

  - apply cofix_red_body. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
    + unfold Template.Ast.app_context, trans_local in b.
      simpl in a. rewrite -> map_app in b.
      unfold app_context. unfold ST.fix_context in b.
      rewrite map_rev map_mapi in b. simpl in b.
      unfold fix_context. rewrite mapi_map. simpl.
      forward b.
      { clear b. solve_all. eapply All_app_inv; auto.
        apply All_rev. apply All_mapi.
        clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
        intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
        now eapply LiftSubst.wf_lift.
        depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
      }
      forward b by auto.
      eapply (refine_red1_Γ); [|apply b].
      f_equal. f_equal. apply mapi_ext; intros [] [].
      rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity.
      rewrite trans_lift. simpl. reflexivity.
    + simpl. inversion b0. reflexivity.
Qed.

Lemma global_levels_trans Σ
  : global_levels (trans_global_decls Σ) = ST.global_levels Σ.
Proof.
  induction Σ; simpl; auto.
  rewrite IHΣ. f_equal. clear.
  destruct a as [? []]; reflexivity.
Qed.

Lemma global_ext_levels_trans Σ
  : global_ext_levels (trans_global Σ) = ST.global_ext_levels Σ.
Proof.
  destruct Σ.
  unfold trans_global, ST.global_ext_levels, global_ext_levels; simpl.
  f_equal. clear u.
  now rewrite global_levels_trans.
Qed.

Lemma global_ext_constraints_trans Σ
  : global_ext_constraints (trans_global Σ) = ST.global_ext_constraints Σ.
Proof.
  destruct Σ.
  unfold trans_global, ST.global_ext_constraints, global_ext_constraints; simpl.
  f_equal. clear u.
  induction g.
  - reflexivity.
  - simpl. rewrite IHg. f_equal. clear.
    destruct a as [? []]; reflexivity.
Qed.

Lemma trans_cumul {cf} (Σ : Ast.global_env_ext) Γ T U :
  ST.wf Σ ->
  List.Forall wf_decl Γ ->
  S.wf T -> S.wf U -> ST.cumul Σ Γ T U ->
  trans_global Σ ;;; trans_local Γ |- trans T <= trans U.
Proof.
  intros wfΣ.
  induction 4.
  - constructor; auto.
    eapply trans_leq_term in l; eauto.
    now rewrite global_ext_constraints_trans.
  - pose proof r as H3. apply wf_red1 in H3; auto with wf.
    apply trans_red1 in r; auto. econstructor 2; eauto with wf.
  - econstructor 3.
    apply IHX; auto. apply wf_red1 in r; auto with wf.
    apply trans_red1 in r; auto.
Qed.

Definition Tlift_typing (P : Template.Ast.global_env_ext -> Tcontext -> Tterm -> Tterm -> Type) :=
  fun Σ Γ t T =>
    match T with
    | Some T => P Σ Γ t T
    | None => { s : Universe.t & P Σ Γ t (S.tSort s) }
    end.

Definition TTy_wf_local {cf : checker_flags} Σ Γ := ST.All_local_env (ST.lift_typing ST.typing Σ) Γ.

Lemma trans_wf_local {cf}:
  forall (Σ : Template.Ast.global_env_ext) (Γ : Tcontext) (wfΓ : TTy_wf_local Σ Γ),
    let P :=
        (fun Σ0 (Γ0 : Tcontext) _ (t T : Tterm) _ =>
           wf (trans_global Σ0).1 ->
           trans_global Σ0;;; trans_local Γ0 |- trans t : trans T)
    in
    wf (trans_global Σ).1 ->
    ST.All_local_env_over ST.typing P Σ Γ wfΓ ->
    wf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X0.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX0.
    + simpl. destruct tu. exists x. now eapply p.
  - simpl. constructor; auto. red. destruct tu. exists x; auto.
    simpl. eauto.
Qed.

Lemma trans_wf_local_env {cf} Σ Γ :
  ST.All_local_env
        (ST.lift_typing
           (fun (Σ : Ast.global_env_ext) (Γ : Tcontext) (b ty : Tterm) =>
              ST.typing Σ Γ b ty × trans_global Σ;;; trans_local Γ |- trans b : trans ty) Σ)
        Γ ->
  wf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct t0. exists x. eapply p.
  - simpl. constructor; auto. red. destruct t0. exists x. intuition auto.
    red. red in t1. destruct t1. eapply t2.
Qed.

(*   eapply ST.on_global_decls_impl. 2:eapply wf. eauto. intros * ongl ont. destruct t. *)
(*   red in ont. *)
(*   eapply typing_wf; eauto. destruct ont. exists x; eapply typing_wf; intuition eauto. *)
(* Qed. *)

Hint Resolve trans_wf_local : trans.

Axiom fix_guard_trans :
  forall Σ Γ mfix,
    ST.fix_guard Σ Γ mfix ->
    fix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Axiom cofix_guard_trans :
  forall Σ Γ mfix,
    ST.cofix_guard Σ Γ mfix ->
    cofix_guard (trans_global Σ) (trans_local Γ) (map (map_def trans trans) mfix).

Notation Swf_fix def := (S.wf (dtype def) /\ S.wf (dbody def)).

Lemma trans_subst_context s k Γ : 
  trans_local (SL.subst_context s k Γ) = subst_context (map trans s) k (trans_local Γ).
Proof.
  induction Γ as [|[na [b|] ty] Γ]; simpl; auto.
  - rewrite SL.subst_context_snoc /=. rewrite [subst_context _ _ _ ]subst_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_subst map_length.
  - rewrite SL.subst_context_snoc /=. rewrite [subst_context _ _ _ ]subst_context_snoc.
    f_equal; auto. rewrite IHΓ /snoc /subst_decl /map_decl /=; f_equal.
    now rewrite !trans_subst map_length.
Qed.

Lemma trans_smash_context Γ Δ : trans_local (ST.smash_context Γ Δ) = smash_context (trans_local Γ) (trans_local Δ).
Proof.
  induction Δ in Γ |- *; simpl; auto.
  destruct a as [na [b|] ty] => /=.
  rewrite IHΔ. f_equal.
  now rewrite (trans_subst_context [_]).
  rewrite IHΔ. f_equal. rewrite /trans_local map_app //.
Qed.
 
Lemma trans_decompose_app {t ind u l} : 
  S.wf t ->
  AstUtils.decompose_app t = (Ast.tInd ind u, l) ->
  ∑ l', decompose_app (trans t) = (tInd ind u, l').
Proof.
  intros wft. destruct (AstUtils.decompose_app t) eqn:da.
  pose proof (TypingWf.decompose_app_inv _ [] _ _ wft da) as [n [napp [eqsk ->]]].
  rewrite trans_mkApps.
  intros [= -> ->].
  rewrite decompose_app_mkApps //. eexists _; eauto.
Qed.

Lemma decompose_prod_assum_it_mkProd_or_LetIn ctx t ctx' t' :
  AstUtils.decompose_prod_assum ctx t = (ctx', t') ->
  Ast.it_mkProd_or_LetIn ctx t = Ast.it_mkProd_or_LetIn ctx' t'.
Proof.
  induction t in ctx, ctx', t' |- *; simpl; try intros [= -> <-]; auto.
  - intros H. now apply IHt2 in H.
  - intros H. now apply IHt3 in H.
Qed.

Lemma it_mkProd_or_LetIn_wf Γ t
  : Ast.wf (Ast.it_mkProd_or_LetIn Γ t) <-> Forall wf_decl Γ /\ Ast.wf t .
Proof.
  revert t. induction Γ.
  - intros t. simpl. split => //; try split => //; trivial. now intros [].
  - intros t.
    destruct a as [na [b|] ty]; simpl in *. rewrite /Ast.mkProd_or_LetIn /=.
    * rewrite IHΓ /=. split; intros [].
      depelim H0. intuition constructor; auto. split; auto. 
      depelim H. red in H. simpl in H. split; auto with wf. constructor; intuition auto.
    * rewrite IHΓ /=. split; intros [].
      depelim H0. simpl in H0_. split; [constructor|];auto.
      split; simpl; auto.
      depelim H. destruct H as [_ wfty]. simpl in wfty.
      split; auto. constructor; simpl; auto.
Qed.

Lemma trans_check_one_fix mfix ind :
  Swf_fix mfix ->
  ST.check_one_fix mfix = Some ind ->
  check_one_fix (map_def trans trans mfix) = Some ind.
Proof.
  unfold ST.check_one_fix, check_one_fix.
  case: mfix => [na ty arg rarg] /= [wfty wfarg].
  move: (trans_decompose_prod_assum [] ty wfty) => /=.
  destruct AstUtils.decompose_prod_assum as [ctx p] eqn:dp => /= // ->.
  rewrite -(trans_smash_context []) /trans_local.
  rewrite -List.map_rev nth_error_map.
  destruct nth_error eqn:hnth => /= //.
  destruct AstUtils.decompose_app eqn:da.
  destruct t => //.
  have [| l' eq] := (trans_decompose_app _ da).
  { eapply decompose_prod_assum_it_mkProd_or_LetIn in dp.
    simpl in dp; subst ty.
    eapply it_mkProd_or_LetIn_wf in wfty as [wfctx _].
    eapply (nth_error_forall (P:=wf_decl)) in hnth; cycle 1.
    eapply rev_Forall.
    pose proof (nth_error_Some_length hnth).
    rewrite nth_error_rev // List.rev_involutive in hnth.
    now apply wf_smash_context. apply hnth. }
  destruct c => /=. rewrite eq /= //.
Qed.

Lemma Forall_map_option_out_map_Some_spec {A B} {f g : A -> option B} {P : A -> Prop} {l} :
  (forall x t, P x -> f x = Some t -> g x = Some t) ->
  Forall P l ->
  forall t,
  map_option_out (map f l) = Some t ->
  map_option_out (map g l) = Some t.
Proof.
  move => Hfg Hl. move: Hl.
  induction 1; try constructor; auto.
  simpl. move=> //.
  case E: (f x) => [b|] //.
  rewrite (Hfg _ _ H E).
  case E' : map_option_out => [b'|] //.
  move=> t [= <-]. now rewrite (IHHl _ E').
Qed.

Lemma map_option_out_check_one_fix {mfix} :
  Forall (fun def => (S.wf (dtype def) /\ S.wf (dbody def))) mfix ->
  forall l, 
  map_option_out (map (fun x => ST.check_one_fix x) mfix) = Some l ->
  map_option_out (map (fun x => check_one_fix (map_def trans trans x)) mfix) = Some l.
Proof.
  eapply Forall_map_option_out_map_Some_spec => x kn.
  apply trans_check_one_fix.
Qed.

Lemma trans_check_one_cofix mfix ind :
  Swf_fix mfix ->
  ST.check_one_cofix mfix = Some ind ->
  check_one_cofix (map_def trans trans mfix) = Some ind.
Proof.
  unfold ST.check_one_cofix, check_one_cofix.
  case: mfix => [na ty arg rarg] /= [wfty wfarg].
  move: (trans_decompose_prod_assum [] ty wfty) => /=.
  destruct AstUtils.decompose_prod_assum as [ctx p] eqn:dp => /= // ->.
  destruct AstUtils.decompose_app eqn:da.
  destruct t => //.
  have [| l' ->] := (trans_decompose_app _ da) => //.
  { eapply decompose_prod_assum_it_mkProd_or_LetIn in dp.
    simpl in dp; subst ty.
    now eapply it_mkProd_or_LetIn_wf in wfty as [_ wfp]. }
Qed.

Lemma map_option_out_check_one_cofix {mfix} :
  Forall (fun def => (S.wf (dtype def) /\ S.wf (dbody def))) mfix ->
  forall l, 
  map_option_out (map (fun x => ST.check_one_cofix x) mfix) = Some l ->
  map_option_out (map (fun x => check_one_cofix (map_def trans trans x)) mfix) = Some l.
Proof.
  apply Forall_map_option_out_map_Some_spec => x kn.
  apply trans_check_one_cofix.
Qed.

Lemma trans_check_rec_kind {Σ k f} :
  ST.check_recursivity_kind Σ k f = check_recursivity_kind (trans_global_decls Σ) k f.
Proof.
  unfold ST.check_recursivity_kind, check_recursivity_kind.
  rewrite trans_lookup.
  destruct S.lookup_env as [[]|] => //.
Qed.

Lemma trans_wf_fixpoint Σ mfix :
  Forall (fun def => (S.wf (dtype def) /\ S.wf (dbody def))) mfix ->
  ST.wf_fixpoint Σ mfix ->
  wf_fixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix).
Proof.
  unfold ST.wf_fixpoint, wf_fixpoint.
  rewrite map_map_compose.
  intros wf.
  destruct map_option_out eqn:ma => //.
  rewrite (map_option_out_check_one_fix wf _ ma).
  destruct l; auto. now rewrite -trans_check_rec_kind.
Qed.

Lemma trans_wf_cofixpoint Σ mfix :
  Forall (fun def => (S.wf (dtype def) /\ S.wf (dbody def))) mfix ->
  ST.wf_cofixpoint Σ mfix ->
  wf_cofixpoint (trans_global_decls Σ) (map (map_def trans trans) mfix).
Proof.
  unfold ST.wf_cofixpoint, wf_cofixpoint.
  rewrite map_map_compose.
  intros wf.
  destruct map_option_out eqn:ma => //.
  rewrite (map_option_out_check_one_cofix wf _ ma).
  destruct l; auto. now rewrite -trans_check_rec_kind.
Qed.

Lemma trans_global_decl_universes d : 
  ST.universes_decl_of_decl d = 
  universes_decl_of_decl (trans_global_decl d).
Proof.
  destruct d; reflexivity.
Qed.

Lemma trans_consistent_instance_ext {cf:checker_flags} Σ d u : 
  ST.consistent_instance_ext Σ (ST.universes_decl_of_decl d) u ->
  consistent_instance_ext (trans_global Σ) (universes_decl_of_decl (trans_global_decl d)) u.
Proof.
  unfold ST.consistent_instance_ext, consistent_instance_ext.
  rewrite global_ext_levels_trans global_ext_constraints_trans trans_global_decl_universes.
  trivial.
Qed.

Theorem template_to_pcuic {cf} :
  ST.env_prop (fun Σ Γ t T =>
    wf (trans_global Σ).1 ->
    typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)).
Proof.
  apply (ST.typing_ind_env (fun Σ Γ t T =>
    wf (trans_global Σ).1 ->
    typing (trans_global Σ) (trans_local Γ) (trans t) (trans T)
  )%type).
  all: simpl.
  all: intros.
  all: auto.
  all: try solve [ econstructor; eauto with trans ].

  - rewrite trans_lift.
    eapply refine_type. eapply type_Rel; eauto.
    eapply trans_wf_local; eauto.
    unfold trans_local. rewrite nth_error_map. rewrite H. reflexivity.
    f_equal. destruct decl; reflexivity.

  - (* Sorts *)
    constructor; eauto.
    eapply trans_wf_local; eauto.
    destruct u; simpl in *; eauto.
    intros.
    now rewrite global_ext_levels_trans.

  - (* Casts *)
    eapply refine_type. eapply type_App with _ (trans t) _.
    2:{ eapply type_Lambda; eauto. eapply type_Rel. econstructor; auto.
    eapply typing_wf_local. eauto. eauto. simpl. exists s; auto. reflexivity. }
    eapply type_Prod. eauto.
    instantiate (1 := s). simpl.
    eapply (weakening _ _ [_] _ (tSort _)); eauto.
    constructor; eauto. eapply typing_wf_local; eauto. red.
    exists s; eauto. auto.
    simpl. unfold subst1. rewrite simpl_subst; auto. now rewrite lift0_p.

  - (* The interesting application case *)
    eapply type_mkApps; eauto.
    specialize (X0 X2).
    eapply typing_wf in X; eauto. destruct X.
    eapply PCUICValidity.validity in X0.
    clear H1 H H0. revert H2.
    induction X1.
    * econstructor; eauto. reflexivity.
    * simpl in p.
      destruct (TypingWf.typing_wf _ wfΣ _ _ _ typrod) as [wfAB _].
      intros wfS.
      econstructor; eauto.
      + exists s; eauto. eapply p; eauto.
      + change (tProd na (trans A) (trans B)) with (trans (S.tProd na A B)).
        apply trans_cumul; auto with trans.
        eapply Forall_impl. eapply TypingWf.typing_all_wf_decl; eauto.
        intros. auto.
      + eapply typing_wf in ty; eauto. destruct ty as [wfhd _].
        rewrite trans_subst in IHX1; eauto with wf.
        eapply IHX1; cycle 1.
        apply Template.LiftSubst.wf_subst; try constructor; auto. now inv wfAB.
        specialize (p X2). specialize (p0 X2).
        eapply PCUICInversion.inversion_Prod in p as [s1 [s2 [HA [HB Hs]]]]. 
        eapply PCUICArities.isType_subst with [vass na (trans A)]; eauto.
        constructor; eauto with pcuic.
        constructor; eauto with pcuic. now rewrite subst_empty.
        now exists s2.
        apply X2.
    * apply X2.

  - rewrite trans_subst_instance_constr.
    pose proof (forall_decls_declared_constant _ _ _ H).
    replace (trans (Template.Ast.cst_type decl)) with
        (cst_type (trans_constant_body decl)) by (destruct decl; reflexivity).
    constructor; eauto with trans.
    now apply (trans_consistent_instance_ext _ (S.ConstantDecl decl)).

  - rewrite trans_subst_instance_constr.
    pose proof (forall_decls_declared_inductive _ _ _ _ isdecl).
    replace (trans (Template.Ast.ind_type idecl)) with
        (ind_type (trans_one_ind_body idecl)) by (destruct idecl; reflexivity).
    eapply type_Ind; eauto. eauto with trans.
    now apply (trans_consistent_instance_ext _ (S.InductiveDecl mdecl)).

  - pose proof (forall_decls_declared_constructor _ _ _ _ _ isdecl).
    unfold ST.type_of_constructor in *.
    rewrite trans_subst.
    rewrite trans_subst_instance_constr.
    rewrite trans_inds. simpl.
    eapply refine_type. econstructor; eauto with trans.
    now apply (trans_consistent_instance_ext _ (S.InductiveDecl mdecl)).
    unfold type_of_constructor. simpl. f_equal. f_equal.
    destruct cdecl as [[id t] p]; simpl; auto.

  - rewrite trans_mkApps; auto with wf trans. apply typing_wf in X1; intuition auto.
    solve_all. apply typing_wf in X3; auto. intuition auto.
    rewrite map_app map_skipn.
    eapply type_Case.
    apply forall_decls_declared_inductive; eauto. destruct mdecl; auto.
    -- simpl. rewrite firstn_map.
       rewrite trans_build_case_predicate_type. erewrite H0. reflexivity.
    -- eapply X1.
    -- rewrite global_ext_constraints_trans; exact H1.
    -- rewrite trans_mkApps in X2; auto with wf.
    -- apply H2.
    -- eapply trans_build_branches_type in H3; eauto.
       rewrite firstn_map. exact H3.
    -- eapply All2_map. solve_all.
       destruct b0 as [s [Hs IHs]]; eauto.

  - destruct pdecl as [arity ty]; simpl in *.
    pose proof (TypingWf.declared_projection_wf _ _ _ _ _ isdecl).
    simpl in H0.
    eapply forall_decls_declared_projection in isdecl.
    destruct (typing_wf _ wfΣ _ _ _ X1) as [wfc wfind].
    eapply wf_mkApps_inv in wfind; auto.
    rewrite trans_subst; auto with wf. 
    simpl. rewrite map_rev. rewrite trans_subst_instance_constr.
    eapply (type_Proj _ _ _ _ _ _ _ (arity, trans ty)). eauto.
    rewrite trans_mkApps in X2; auto. rewrite map_length.
    destruct mdecl; auto.

  - eapply refine_type.
    assert (fix_context (map (map_def trans trans) mfix) =
            trans_local (ST.fix_context mfix)).
    { unfold trans_local, ST.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext; intros i x.
      simpl. rewrite trans_lift. reflexivity. }
    econstructor; eauto.
    eapply fix_guard_trans. assumption.
    now rewrite nth_error_map H0.
    -- eapply trans_wf_local; eauto.
    -- eapply All_map, (All_impl X0).
       intros x [s [Hs Hts]].
       now exists s.
    -- apply All_map. eapply All_impl; eauto.
       intuition eauto 3 with wf; cbn.
       rewrite H2. rewrite /trans_local map_length.
       rewrite /trans_local map_app in X3.
       rewrite <- trans_lift. apply X3; auto.
    -- eapply trans_wf_fixpoint => //.
        solve_all. destruct a as [s [Hs IH]].
        now eapply TypingWf.typing_wf in Hs.
        now eapply TypingWf.typing_wf in a0.
    -- destruct decl; reflexivity.

  - eapply refine_type.
    assert (fix_context (map (map_def trans trans) mfix) =
            trans_local (ST.fix_context mfix)).
    { unfold trans_local, ST.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext => i x.
      simpl. rewrite trans_lift. reflexivity. }
    econstructor; eauto.
    -- now eapply cofix_guard_trans.
    -- now rewrite nth_error_map H0.
    -- eapply trans_wf_local; eauto.
    -- eapply All_map, (All_impl X0).
       intros x [s [Hs Hts]]. now exists s.
    -- apply All_map. eapply All_impl; eauto.
       intuition eauto 3 with wf.
       rewrite H2. rewrite /trans_local map_length.
       unfold Template.Ast.app_context in X3.
       rewrite /trans_local map_app in X3.
       cbn. rewrite <- trans_lift. now apply X3.
    -- eapply trans_wf_cofixpoint => //.
       solve_all. destruct a as [s [Hs IH]].
       now eapply TypingWf.typing_wf in Hs.
       now eapply TypingWf.typing_wf in a0.
    -- destruct decl; reflexivity.

  - assert (S.wf B).
    { now apply typing_wf in X2. }
    eapply type_Cumul; eauto.
    eapply trans_cumul; eauto with trans. 
    clear X. apply typing_all_wf_decl in wfΓ; auto.
    eapply typing_wf in X0; eauto. destruct X0. auto.
Qed.

Lemma Alli_map {A B} (P : nat -> B -> Type) n (f : A -> B) l : 
  Alli (fun n x => P n (f x)) n l ->
  Alli P n (map f l).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma trans_arities_context m : trans_local (Ast.arities_context (Ast.ind_bodies m)) = 
  arities_context (map trans_one_ind_body (Ast.ind_bodies m)).
Proof.
  rewrite /trans_local /Ast.arities_context rev_map_spec map_rev map_map_compose 
    /PCUICEnvironment.arities_context rev_map_spec map_map_compose /= //.
Qed.

Lemma trans_lift_context n k Γ : lift_context n k (trans_local Γ) = 
  trans_local (LiftSubst.lift_context n k Γ).
Proof.
  rewrite /lift_context /LiftSubst.lift_context /fold_context /Ast.fold_context.
  rewrite /trans_local map_rev map_mapi -List.map_rev mapi_map.
  f_equal. apply mapi_ext. intros ? [na [b|] ty]; simpl; rewrite /trans_decl /= /map_decl; simpl; 
  f_equal; now rewrite trans_lift.
Qed.
  
Lemma trans_subst_telescope s k Γ : 
  map trans_decl (LiftSubst.subst_telescope s k Γ) = 
  subst_telescope (map trans s) k (map trans_decl Γ).
Proof.
  rewrite /subst_telescope /LiftSubst.subst_telescope.
  rewrite map_mapi mapi_map.
  apply mapi_ext => n [na [b|] ty] /=;
  rewrite /map_decl /=; f_equal;
  now rewrite trans_subst.
Qed.

Lemma trans_on_global_env `{checker_flags} Σ P Q :
  (forall Σ Γ t T, ST.on_global_env P Σ.1 -> P Σ Γ t T ->
    on_global_env Q (trans_global_decls Σ.1) ->
    Q (trans_global Σ) (trans_local Γ) (trans t) (option_map trans T)) ->
  ST.on_global_env P Σ -> on_global_env Q (trans_global_decls Σ).
Proof.
  intros X X0.
  simpl in *. induction X0; simpl; constructor; auto.
  - red in f |- *. apply Forall_map.
    solve_all.
  - simpl. subst udecl.
    clear -o. destruct d; simpl in *;
      destruct o as [? [? [? ?]]].
    * split; rewrite global_levels_trans //.
      repeat split => //.
      red in H3 |- *.
      rewrite -global_ext_constraints_trans in H3.
      apply H3.
    * split; rewrite global_levels_trans //.
      repeat split => //.
      red in H3 |- *.
      rewrite -global_ext_constraints_trans in H3.
      apply H3.
  - simpl.
    destruct d; simpl in *.
    * destruct c; simpl. destruct cst_body; simpl in *.
      red in o |- *. simpl in *. 
      apply (X (Σ, cst_universes) [] t (Some cst_type)); auto.
      red in o0 |- *. simpl in *.
      now apply (X (Σ, cst_universes) [] cst_type None).
    * destruct o0 as [onI onP onNP].
      constructor; auto.
      -- eapply Alli_map. eapply Alli_impl. exact onI. eauto. intros.
         unshelve refine {| ind_indices := trans_local X1.(ST.ind_indices); 
          ind_sort := X1.(ST.ind_sort);
          ind_cunivs := map trans_constructor_shape X1.(ST.ind_cunivs) |}.
        --- simpl; rewrite X1.(ST.ind_arity_eq).
            now rewrite !trans_it_mkProd_or_LetIn.
        --- apply ST.onArity in X1. unfold on_type in *; simpl in *.
            now apply (X (Σ, Ast.ind_universes m) [] (Ast.ind_type x) None).
        --- pose proof X1.(ST.onConstructors) as X11. red in X11.
            red. eapply All2_map.
            eapply All2_impl; eauto.
            simpl. intros [[? ?] ?] cs onc. destruct onc; unshelve econstructor; eauto.
            + simpl. unfold trans_local. rewrite context_assumptions_map.
              now rewrite cstr_args_length. 
            + simpl; unfold cstr_type, ST.cstr_type in cstr_eq |- *; simpl in *.
               rewrite cstr_eq. rewrite !trans_it_mkProd_or_LetIn.
               autorewrite with len. f_equal. f_equal.
               rewrite !trans_mkApps //.
               f_equal; auto. simpl.
               now rewrite /trans_local !map_length.
               rewrite map_app /=. f_equal.
               rewrite /trans_local !map_length.
               unfold TemplateEnvironment.to_extended_list_k.
               now rewrite trans_reln.
            + unfold cstr_type, ST.cstr_type in on_ctype |- *; simpl in *.
              red. 
              move: (X (Σ, Ast.ind_universes m) (Ast.arities_context (Ast.ind_bodies m)) t None).
              now rewrite trans_arities_context.
            + clear -X0 IHX0 X on_cargs. revert on_cargs. simpl.
              generalize (ST.cstr_args cs), (ST.cdecl_sorts cs).
              have foo := (X (Σ, udecl) _ _ _ X0).
              rewrite -trans_arities_context.
              induction c; destruct l; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
              split; intuition eauto;
              specialize (foo 
                (Ast.app_context (Ast.app_context (Ast.arities_context (Ast.ind_bodies m)) (Ast.ind_params m)) c));
              rewrite /trans_local !map_app in foo.
              now apply (foo ty None). 
              now apply (foo b (Some ty)).
              now apply (foo ty None).
              now apply (foo b (Some ty)).
              now apply (foo ty (Some (Ast.tSort _))).
            + clear -X0 IHX0 X on_cindices.
              revert on_cindices.
              rewrite trans_lift_context /trans_local -map_rev.
              simpl. rewrite {2}/trans_local map_length.
              generalize (List.rev (LiftSubst.lift_context #|ST.cstr_args cs| 0 (ST.ind_indices X1))).
              generalize (ST.cstr_indices cs).
              rewrite -trans_arities_context.
              induction 1; simpl; constructor; auto;
              have foo := (X (Σ, Ast.ind_universes m) _ _ _ X0);
              specialize (foo (Ast.app_context (Ast.app_context (Ast.arities_context (Ast.ind_bodies m)) 
                (Ast.ind_params m)) (ST.cstr_args cs))).
              rewrite /trans_local !map_app in foo.
              now apply (foo i (Some t)).
              now rewrite (trans_subst_telescope [i] 0) in IHon_cindices.
              now rewrite (trans_subst_telescope [b] 0) in IHon_cindices.
            + clear -IHX0 on_ctype_positive.
              unfold ST.cstr_type in *. unfold cstr_type. simpl in *.
              change [] with (map trans_decl []). revert on_ctype_positive.
              generalize (@nil Ast.context_decl). induction 1; simpl.
              rewrite trans_mkApps. simpl.
              subst headrel.
              assert (#|PCUICEnvironment.ind_bodies (trans_minductive_body m)| = #|TemplateEnvironment.ind_bodies m|) as <-.
              now rewrite /trans_minductive_body /= map_length.
              assert (#|ctx| = #|map trans_decl ctx|) as ->. now rewrite map_length.
              eapply positive_cstr_concl.
              rewrite map_length.
              eapply All_map. eapply All_impl; eauto.
              simpl; intros. admit.
              constructor. now rewrite -(trans_subst [b]).
              constructor. admit.
              apply IHon_ctype_positive.
            + clear -on_ctype_variance.
              intros v indv. admit.
        --- simpl; intros. have onp := X1.(ST.onProjections).
            admit.
        --- have inds := X1.(ST.ind_sorts).
            admit.
        --- have inds := X1.(ST.onIndices).
            admit.
      -- red in onP. red.
        admit.
      -- admit.
Admitted.

Lemma template_to_pcuic_env {cf} Σ : Template.Typing.wf Σ -> wf (trans_global_decls Σ).
Proof.
  intros Hu.
  eapply trans_on_global_env; eauto. simpl; intros.
  epose proof (ST.env_prop_typing _ template_to_pcuic _ X Γ).
  forward X2.
  red in X0. destruct T.
  now eapply ST.typing_wf_local.
  destruct X0 as [s Hs]. eapply ST.typing_wf_local; eauto.
  destruct T; simpl in *.
  - eapply X2; eauto.
  - destruct X0 as [s Hs]. exists s.
    eapply (X2 _ (Ast.tSort s)); eauto.
Qed.

Lemma template_to_pcuic_env_ext {cf} Σ : Template.Typing.wf_ext Σ -> wf_ext (trans_global Σ).
Proof.
  intros [u Hu].
  split. now apply template_to_pcuic_env.
  destruct Hu as [? [? [? ?]]].
  split; rewrite global_levels_trans //.
  repeat split => //. 
  red in H2 |- *.
  rewrite -global_ext_constraints_trans in H2.
  apply H2.
Qed.

Theorem template_to_pcuic_typing {cf} Σ Γ t T :
  ST.wf Σ.1 ->
  ST.typing Σ Γ t T ->
  typing (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.
  intros wf ty.
  apply (ST.env_prop_typing _ template_to_pcuic _ wf); auto.
  now eapply ST.typing_wf_local.
  now apply template_to_pcuic_env.
Qed.
