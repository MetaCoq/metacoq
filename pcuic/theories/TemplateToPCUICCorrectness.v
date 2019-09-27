(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Coq Require Import Bool String List Program BinPos Compare_dec Omega.
From MetaCoq.Template Require Import config utils AstUtils BasicAst Ast.
(* For two lemmata wf_instantiate_params_subst_term and
   wf_instantiate_params_subst_ctx, maybe they should be moved *)
From MetaCoq.Checker Require Import WfInv Typing Weakening TypingWf
     WeakeningEnv Substitution.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICEquality
     PCUICUnivSubst PCUICTyping PCUICGeneration TemplateToPCUIC.

Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Module T := Template.Ast.
Module TTy := Checker.Typing.

Local Existing Instance default_checker_flags.

Module TL := Template.LiftSubst.

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
  trans (TL.lift n k t) = lift n k (trans t).
Proof.
  revert k. induction t using Template.Induction.term_forall_list_ind; simpl; intros; try congruence.
  - now destruct leb.
  - f_equal. rewrite !map_map_compose. solve_all.
  - rewrite lift_mkApps, IHt, map_map.
    f_equal. rewrite map_map; solve_all.

  - f_equal; auto. red in H. solve_list.
  - f_equal; auto; red in H; solve_list.
  - f_equal; auto; red in H; solve_list.
Qed.

Lemma mkApps_app f l l' : mkApps f (l ++ l') = mkApps (mkApps f l) l'.
Proof.
  revert f l'; induction l; simpl; trivial.
Qed.

Lemma trans_mkApp u a : trans (T.mkApp u a) = tApp (trans u) (trans a).
Proof.
  induction u; simpl; try reflexivity.
  rewrite map_app.
  replace (tApp (mkApps (trans u) (map trans args)) (trans a))
    with (mkApps (mkApps (trans u) (map trans args)) [trans a]) by reflexivity.
  rewrite mkApps_app. reflexivity.
Qed.

Lemma trans_mkApps u v : T.wf u -> List.Forall T.wf v ->
  trans (T.mkApps u v) = mkApps (trans u) (List.map trans v).
Proof.
  revert u; induction v.
  simpl; trivial.
  intros.
  rewrite <- Template.LiftSubst.mkApps_mkApp; auto.
  rewrite IHv. simpl. f_equal.
  apply trans_mkApp.

  apply Template.LiftSubst.wf_mkApp; auto. inversion_clear H0. auto.
  inversion_clear H0. auto.
Qed.

Lemma trans_subst t k u : All T.wf t -> T.wf u ->
  trans (TL.subst t k u) = subst (map trans t) k (trans u).
Proof.
  intros wft wfu.
  revert k. induction wfu using Template.Induction.term_wf_forall_list_ind; simpl; intros; try congruence.

  - repeat nth_leb_simpl; auto.
    rewrite trans_lift.
    rewrite nth_error_map in e0. rewrite e in e0.
    injection e0. congruence.

  - f_equal; solve_list.

  - rewrite subst_mkApps. rewrite <- IHwfu.
    rewrite trans_mkApps. f_equal.
    solve_list.
    apply Template.LiftSubst.wf_subst; auto.
    solve_all. solve_all. apply Template.LiftSubst.wf_subst; auto. solve_all.

  - f_equal; auto; red in H; solve_list.
  - f_equal; auto; red in H; solve_list.
  - f_equal; auto; red in H; solve_list.
Qed.

Notation Tterm := Template.Ast.term.
Notation Tcontext := Template.Ast.context.

Lemma trans_subst_instance_constr u t : trans (Template.UnivSubst.subst_instance_constr u t) =
                                        subst_instance_constr u (trans t).
Proof.
  induction t using Template.Induction.term_forall_list_ind; simpl; try congruence.
  f_equal. rewrite !map_map_compose. solve_all.
  rewrite IHt. rewrite map_map_compose.
  rewrite mkApps_morphism; auto. f_equal.
  rewrite !map_map_compose. solve_all.
  1-3:f_equal; auto; Template.AstUtils.merge_All; solve_list.
Qed.

Require Import ssreflect.

Lemma forall_decls_declared_constant Σ cst decl :
  TTy.declared_constant Σ cst decl ->
  declared_constant (trans_global_decls Σ) cst (trans_constant_body decl).
Proof.
  unfold declared_constant, TTy.declared_constant.
  induction Σ => //; try discriminate.
  case: a => // /= k b; case: (ident_eq cst k); auto.
  - by move => [=] -> ->.
  - by discriminate.
Qed.

Lemma forall_decls_declared_minductive Σ cst decl :
  TTy.declared_minductive Σ cst decl ->
  declared_minductive (trans_global_decls Σ) cst (trans_minductive_body decl).
Proof.
  unfold declared_minductive, TTy.declared_minductive.
  induction Σ => //; try discriminate.
  case: a => // /= k b; case: (ident_eq cst k); auto.
  - by discriminate.
  - by move => [=] -> ->.
Qed.

Lemma forall_decls_declared_inductive Σ mdecl ind decl :
  TTy.declared_inductive Σ mdecl ind decl ->
  declared_inductive (trans_global_decls Σ) (trans_minductive_body mdecl) ind (trans_one_ind_body decl).
Proof.
  unfold declared_inductive, TTy.declared_inductive.
  move=> [decl' Hnth].
  pose proof (forall_decls_declared_minductive _ _ _ decl').
  eexists. eauto. destruct decl'; simpl in *.
  red in H. destruct mdecl; simpl.
  by rewrite nth_error_map Hnth.
Qed.

Lemma forall_decls_declared_constructor Σ cst mdecl idecl decl :
  TTy.declared_constructor Σ mdecl idecl cst decl ->
  declared_constructor (trans_global_decls Σ) (trans_minductive_body mdecl) (trans_one_ind_body idecl)
                    cst ((fun '(x, y, z) => (x, trans y, z)) decl).
Proof.
  unfold declared_constructor, TTy.declared_constructor.
  move=> [decl' Hnth].
  pose proof (forall_decls_declared_inductive _ _ _ _ decl'). split; auto.
  destruct idecl; simpl.
  by rewrite nth_error_map Hnth.
Qed.

Lemma forall_decls_declared_projection Σ cst mdecl idecl decl :
  TTy.declared_projection Σ mdecl idecl cst decl ->
  declared_projection (trans_global_decls Σ) (trans_minductive_body mdecl) (trans_one_ind_body idecl)
                    cst ((fun '(x, y) => (x, trans y)) decl).
Proof.
  unfold declared_constructor, TTy.declared_constructor.
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
  T.wf t ->
  match TTy.destArity ctx t with
  | Some (args, s) =>
    destArity (trans_local ctx) (trans t) =
    Some (trans_local args, s)
  | None => True
  end.
Proof.
  intros wf; revert ctx.
  induction wf using Template.Induction.term_wf_forall_list_ind; intros ctx; simpl; trivial.
  apply (IHwf0 (T.vass n t :: ctx)).
  apply (IHwf1 (T.vdef n t t0 :: ctx)).
Qed.

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

Definition on_pair {A B C D} (f : A -> B) (g : C -> D) (x : A * C) :=
  (f (fst x), g (snd x)).

Lemma trans_inds kn u bodies : map trans (TTy.inds kn u bodies) = inds kn u (map trans_one_ind_body bodies).
Proof.
  unfold inds, TTy.inds. rewrite map_length.
  induction bodies. simpl. reflexivity. simpl; f_equal. auto.
Qed.

Lemma trans_instantiate_params_subst params args s t :
  All TypingWf.wf_decl params -> All Ast.wf s ->
  All Ast.wf args ->
  forall s' t',
    TTy.instantiate_params_subst params args s t = Some (s', t') ->
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
       now (inv Hparams).
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
  T.wf t ->
  All TypingWf.wf_decl params ->
  All Ast.wf args ->
  forall t',
    TTy.instantiate_params params args t = Some t' ->
    instantiate_params (map trans_decl params) (map trans args) (trans t) =
    Some (trans t').
Proof.
  intros wft wfpars wfargs t' eq.
  revert eq.
  unfold TTy.instantiate_params.
  case_eq (TTy.instantiate_params_subst (List.rev params) args [] t).
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
  - apply Forall_All. assumption.
  - assumption.
Qed.

Lemma trans_it_mkProd_or_LetIn ctx t :
  trans (Template.AstUtils.it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (map trans_decl ctx) (trans t).
Proof.
  induction ctx in t |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl; auto.
  now rewrite IHctx.
  now rewrite IHctx.
Qed.

Lemma trans_types_of_case (Σ : T.global_env) ind mdecl idecl args p u pty indctx pctx ps btys :
  T.wf p -> T.wf pty -> T.wf (T.ind_type idecl) ->
  All Ast.wf args ->
  TTy.wf Σ ->
  TTy.declared_inductive Σ mdecl ind idecl ->
  TTy.types_of_case ind mdecl idecl args u p pty = Some (indctx, pctx, ps, btys) ->
  types_of_case ind (trans_minductive_body mdecl) (trans_one_ind_body idecl)
  (map trans args) u (trans p) (trans pty) =
  Some (trans_local indctx, trans_local pctx, ps, map (on_snd trans) btys).
Proof.
  intros wfp wfpty wfdecl wfargs wfsigma Hidecl. simpl.
  pose proof (on_declared_inductive wfsigma Hidecl) as [onmind onind].
  apply TTy.onParams in onmind as Hparams.
  assert (closedparams : Closed.closed_ctx (Ast.ind_params mdecl)).
  { eapply closed_wf_local ; eauto. eauto. }
  assert (wfparams : All wf_decl (Ast.ind_params mdecl)).
  { apply Forall_All. eapply typing_all_wf_decl ; eauto. simpl. eauto.  }
  unfold TTy.types_of_case, types_of_case. simpl.
  pose proof (trans_instantiate_params (Ast.ind_params mdecl) args (Ast.ind_type idecl)) as ht.
  case_eq (TTy.instantiate_params (Ast.ind_params mdecl) args (Ast.ind_type idecl)).
  all: try discriminate. intros ity e.
  rewrite e in ht. specialize ht with (4 := eq_refl).
  (* rewrite ht ; trivial. clear ht. *)
  (* apply wf_instantiate_params in e as wfity ; trivial. *)
  (* all: try apply All_Forall ; trivial. *)
  (* pose proof (trans_destArity [] ity wfity); trivial. *)
  (* destruct TTy.destArity as [[ctx s] | ]; try congruence. *)
  (* rewrite H. *)
  (* pose proof (trans_destArity [] pty wfpty); trivial. *)
  (* destruct TTy.destArity as [[ctx' s'] | ]; try congruence. *)
  (* rewrite H0. *)
  (* apply TTy.onConstructors in onind. *)
  (* assert(forall brtys, *)
  (*           map_option_out (TTy.build_branches_type ind mdecl idecl args u p) = Some brtys -> *)
  (*           map_option_out *)
  (*             (build_branches_type ind (trans_minductive_body mdecl) (trans_one_ind_body idecl) (map trans args) u (trans p)) = *)
  (*           Some (map (on_snd trans) brtys)). *)
  (* intros brtys. *)
  (* unfold TTy.build_branches_type, build_branches_type. *)
  (* unfold trans_one_ind_body. simpl. rewrite -> mapi_map. *)
  (* eapply Alli_map_option_out_mapi_Some_spec. eapply onind. eauto. *)
  (* intros i [[id t] n] [t0 ar]. *)
  (* unfold compose, on_snd. simpl. *)
  (* intros [ont cshape]. destruct cshape; simpl in *. *)
  (* destruct ont. destruct x; simpl in *. subst t. simpl. *)
  (* unfold TTy.instantiate_params, instantiate_params. *)
  (* destruct TTy.instantiate_params_subst eqn:Heq. *)
  (* destruct p0 as [s0 ty]. *)
  (* pose proof Heq. *)
  (* apply instantiate_params_subst_make_context_subst in H1 as [ctx'' Hctx'']. *)

  (* eapply trans_instantiate_params_subst in Heq. simpl in Heq. *)
  (* rewrite map_rev in Heq. *)
  (* rewrite trans_subst in Heq. apply Forall_All. apply wf_inds. *)
  (* apply wf_subst_instance_constr. *)
  (* now eapply typing_wf in t2. *)
  (* rewrite trans_subst_instance_constr trans_inds in Heq. *)
  (* rewrite Heq. *)
  (* apply PCUICSubstitution.instantiate_params_subst_make_context_subst in Heq. *)
  (* destruct Heq as [ctx''' [Hs0 Hdecomp]]. *)
  (* rewrite List.rev_length map_length in Hdecomp. *)
  (* rewrite <- trans_subst_instance_constr in Hdecomp. *)
  (* rewrite !Template.UnivSubst.subst_instance_constr_it_mkProd_or_LetIn in Hdecomp. *)
  (* rewrite !trans_it_mkProd_or_LetIn in Hdecomp. *)
  (* assert (#|Template.Ast.ind_params mdecl| = *)
  (*   #|PCUICTyping.subst_context *)
  (*     (inds (inductive_mind ind) u (map trans_one_ind_body (Template.Ast.ind_bodies mdecl))) 0 *)
  (*     (map trans_decl (Template.UnivSubst.subst_instance_context u (Template.Ast.ind_params mdecl)))|). *)
  (* now rewrite PCUICSubstitution.subst_context_length map_length Template.UnivSubst.subst_instance_context_length. *)
  (* rewrite H1 in Hdecomp. *)
  (* rewrite PCUICSubstitution.subst_it_mkProd_or_LetIn in Hdecomp. *)
  (* rewrite decompose_prod_n_assum_it_mkProd in Hdecomp. *)
  (* injection Hdecomp. intros <- <-. clear Hdecomp. *)

  (* subst cshape_concl_head. destruct Hctx''. *)

  (* admit. admit. admit. admit. congruence. *)
  (* revert H1. destruct map_option_out. intros. *)
  (* specialize (H1 _ eq_refl). rewrite H1. *)
  (* congruence. *)
  (* intros. discriminate. *)
Admitted.

Hint Constructors T.wf : wf.

Hint Resolve Checker.TypingWf.typing_wf : wf.

Lemma mkApps_trans_wf U l : T.wf (T.tApp U l) -> exists U' V', trans (T.tApp U l) = tApp U' V'.
Proof.
  simpl. induction l using rev_ind. intros. inv H. congruence.
  intros. rewrite map_app. simpl. exists (mkApps (trans U) (map trans l)), (trans x).
  clear. revert U x ; induction l. simpl. reflexivity.
  simpl. intros.
  rewrite mkApps_app. simpl. reflexivity.
Qed.

Lemma trans_eq_term ϕ T U :
  T.wf T -> T.wf U -> TTy.eq_term ϕ T U ->
  eq_term ϕ (trans T) (trans U).
Proof.
  intros HT HU H.
(* TODO move eq_term to type in Template as well *)
Admitted.
(*   revert U HU H; induction HT using Template.Induction.term_wf_forall_list_ind; intros U HU HH; inversion HH; subst; simpl; repeat constructor; unfold eq_term in *; *)
(*     inversion_clear HU; try easy. *)
(*   - eapply Forall2_map. eapply Forall2_impl. *)
(*     eapply Forall_Forall2_and. 2: eassumption. *)
(*     eapply Forall_Forall2_and'; eassumption. *)
(*     cbn. now intros x y [? [? ?]]. *)
(*   - eapply PCUICCumulativity.eq_term_mkApps; unfold eq_term. easy. *)
(*     eapply Forall2_map. eapply Forall2_impl. *)
(*     eapply Forall_Forall2_and. 2: eassumption. *)
(*     eapply Forall_Forall2_and'; eassumption. *)
(*     cbn. now intros x y [? [? ?]]. *)
(*   - eapply Forall2_map. eapply Forall2_impl. *)
(*     eapply Forall_Forall2_and. 2: eassumption. *)
(*     eapply Forall_Forall2_and'; eassumption. *)
(*     cbn. intros x y [? [? ?]]. split ; easy. *)
(*   - eapply Forall2_map. eapply Forall2_impl. *)
(*     eapply Forall_Forall2_and. 2: exact H. *)
(*     eapply Forall_Forall2_and. 2: exact H0. *)
(*     eapply Forall_Forall2_and'; eassumption. *)
(*     cbn. now intros x y [? [? ?]]. *)
(*   - eapply Forall2_map. eapply Forall2_impl. *)
(*     eapply Forall_Forall2_and. 2: exact H. *)
(*     eapply Forall_Forall2_and'; eassumption. *)
(*     cbn. now intros x y [? [? ?]]. *)
(* Qed. *)


Lemma trans_eq_term_list ϕ T U :
  List.Forall T.wf T -> List.Forall T.wf U -> Forall2 (TTy.eq_term ϕ) T U ->
  All2 (eq_term ϕ) (List.map trans T) (List.map trans U).
Proof.
(*   intros H H0 H1. eapply All2_map. *)
(*   pose proof (Forall_Forall2_and H1 H) as H2. *)
(*   pose proof (Forall_Forall2_and' H2 H0) as H3. *)
(*   apply (Forall2_impl H3). *)
(*   intuition auto using trans_eq_term. *)
(* Qed. *)
Admitted.

Lemma leq_term_mkApps ϕ t u t' u' :
  eq_term ϕ t t' -> All2 (eq_term ϕ) u u' ->
  leq_term ϕ (mkApps t u) (mkApps t' u').
Proof.
  intros Hn Ht.
  revert t t' Ht Hn; induction u in u' |- *; intros.

  inversion_clear Ht.
  simpl. apply eq_term_leq_term. assumption.

  inversion_clear Ht.
  simpl in *. apply IHu. assumption. constructor; assumption.
Qed.

Lemma eq_term_upto_univ_App `{checker_flags} Re Rle f f' :
  eq_term_upto_univ Re Rle f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps `{checker_flags} Re Rle f l f' l' :
  eq_term_upto_univ Re Rle f f' ->
  All2 (eq_term_upto_univ Re Re) l l' ->
  eq_term_upto_univ Re Rle (mkApps f l) (mkApps f' l').
Proof.
  induction l in f, f', l' |- *; intro e; inversion_clear 1.
  - assumption.
  - pose proof (eq_term_upto_univ_App _ _ _ _ e).
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

Lemma trans_eq_term_upto_univ Re Rle T U :
  T.wf T -> T.wf U -> TTy.eq_term_upto_univ Re Rle T U ->
  eq_term_upto_univ Re Rle (trans T) (trans U).
Proof.
  intros HT HU H.
  revert U HU H.

(* First need an eliminator to Type for wf template-coq terms *)
(*
  induction HT in Rle |- * using Template.Induction.term_wf_forall_list_ind.
  all: intros U HU HH.
  all: try solve [
    inversion HH ; subst ; simpl ;
    repeat constructor ;
    inversion_clear HU ; try easy
  ].
  - dependent destruction HH. simpl.
    dependent destruction HU.
    econstructor.
    eapply Forall2_map. eapply Forall2_impl.
    + eapply Forall_Forall2_and. 2: eassumption.
      eapply Forall_Forall2_and'. all: eassumption.
    + simpl. intros x y [H2 [HHH H4]].
      eapply H2 ; eauto.
  - dependent destruction HH. simpl.
    dependent destruction HU.
    eapply eq_term_upto_univ_mkApps.
    + eapply IHHT ; eauto.
    + eapply Forall2_map. eapply Forall2_impl.
      * eapply Forall_Forall2_and. 2: eassumption.
        eapply Forall_Forall2_and'. all: eassumption.
      * simpl. intros x y [H7 [? ?]].
        eapply H7 ; eauto.
  - dependent destruction HH. simpl.
    dependent destruction HU.
    econstructor.
    all: try solve [ repeat econstructor ; easy ].
    eapply Forall2_map. eapply Forall2_impl.
    + eapply Forall_Forall2_and. 2: eassumption.
      eapply Forall_Forall2_and'. all: eassumption.
    + simpl. intros x y [H2 [[? ?] ?]].
      split ; eauto.
  - dependent destruction HH. simpl.
    dependent destruction HU.
    econstructor.
    eapply Forall2_map. eapply Forall2_impl.
    eapply Forall_Forall2_and. 2: exact H.
    eapply Forall_Forall2_and. 2: exact H0.
    eapply Forall_Forall2_and'; eassumption.
    cbn. now intros x y [? [? ?]].
  - dependent destruction HH. simpl.
    dependent destruction HU.
    econstructor.
    eapply Forall2_map. eapply Forall2_impl.
    eapply Forall_Forall2_and. 2: exact H.
    eapply Forall_Forall2_and'; eassumption.
    cbn. now intros x y [? [? ?]].
*)
Admitted.

Lemma trans_leq_term ϕ T U :
  T.wf T -> T.wf U -> TTy.leq_term ϕ T U ->
  leq_term ϕ (trans T) (trans U).
Proof.
  intros HT HU H.
  eapply trans_eq_term_upto_univ ; eauto.
Qed.

(* Lemma wf_mkApps t u : T.wf (T.mkApps t u) -> List.Forall T.wf u. *)
(* Proof. *)
(*   induction u in t |- *; simpl. *)
(*   - intuition. *)
(*   - intros H; destruct t; try solve [inv H; intuition auto]. *)
(*     specialize (IHu (T.tApp t (l ++ [a]))). *)
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

Lemma trans_iota_red pars ind c u args brs :
  T.wf (Template.Ast.mkApps (Template.Ast.tConstruct ind c u) args) ->
  List.Forall (compose T.wf snd) brs ->
  trans (TTy.iota_red pars c args brs) =
  iota_red pars c (List.map trans args) (List.map (on_snd trans) brs).
Proof.
  unfold TTy.iota_red, iota_red. intros wfapp wfbrs.
  rewrite trans_mkApps.

  - induction wfbrs in c |- *.
    destruct c; simpl; constructor.
    destruct c; simpl; try constructor; auto with wf.
  - apply wf_mkApps_napp in wfapp. solve_all. apply All_skipn. solve_all. constructor.
  - f_equal. induction brs in c |- *; simpl; destruct c; trivial.
    now rewrite map_skipn.
Qed.

Lemma trans_unfold_fix mfix idx narg fn :
  List.Forall (fun def : def Tterm => T.wf (dtype def) /\ T.wf (dbody def) /\
              T.isLambda (dbody def) = true) mfix ->
  TTy.unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TTy.unfold_fix, unfold_fix. intros wffix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef => //.
  intros [= <- <-]. simpl.
  destruct isLambda eqn:isl => //.
  repeat f_equal.
  rewrite trans_subst. clear Hdef.
  unfold TTy.fix_subst. generalize mfix at 2.
  induction mfix0. constructor. simpl. repeat (constructor; auto).
  apply (nth_error_forall Hdef) in wffix. simpl in wffix; intuition.
  f_equal. clear Hdef.
  unfold fix_subst, TTy.fix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction wffix; trivial.
  simpl; intros mfix. f_equal.
  eapply (IHwffix mfix).

  apply (nth_error_forall Hdef) in wffix.
  simpl in wffix. intuition auto.
  destruct (dbody d); simpl in *; congruence.
Qed.

Lemma trans_unfold_cofix mfix idx narg fn :
  List.Forall (fun def : def Tterm => T.wf (dtype def) /\ T.wf (dbody def)) mfix ->
  TTy.unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def trans trans) mfix) idx = Some (narg, trans fn).
Proof.
  unfold TTy.unfold_cofix, unfold_cofix. intros wffix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef.
  intros [= <- <-]. simpl. repeat f_equal.
  rewrite trans_subst. clear Hdef.
  unfold TTy.cofix_subst. generalize mfix at 2.
  induction mfix0. constructor. simpl. repeat (constructor; auto).
  apply (nth_error_forall Hdef) in wffix. simpl in wffix; intuition.
  f_equal. clear Hdef.
  unfold cofix_subst, TTy.cofix_subst. rewrite map_length.
  generalize mfix at 1 3.
  induction wffix; trivial.
  simpl; intros mfix. f_equal.
  eapply (IHwffix mfix). congruence.
Qed.

Definition isApp t := match t with tApp _ _ => true | _ => false end.

Lemma trans_is_constructor:
  forall (args : list Tterm) (narg : nat),
    Checker.Typing.is_constructor narg args = true -> is_constructor narg (map trans args) = true.
Proof.
  intros args narg.
  unfold Checker.Typing.is_constructor, is_constructor.
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
Ltac wf_inv H := try apply wf_inv in H; simpl in H; repeat destruct_conjs.

Lemma trans_red1 Σ Γ T U :
  TTy.on_global_env (fun Σ => wf_decl_pred) Σ ->
  List.Forall wf_decl Γ ->
  T.wf T -> TTy.red1 Σ Γ T U ->
  red1 (map trans_global_decl Σ) (trans_local Γ) (trans T) (trans U).
Proof.
  intros wfΣ wfΓ Hwf.
  induction 1 using Checker.Typing.red1_ind_all; wf_inv Hwf; simpl in *;
    try solve [econstructor; eauto].

  - simpl. wf_inv H1. apply Forall_All in H2. inv H2.
    rewrite trans_mkApps; auto. apply Template.LiftSubst.wf_subst; auto with wf; solve_all.
    apply All_Forall. auto.
    rewrite trans_subst; auto. apply PCUICSubstitution.red1_mkApps_l. constructor.

  - rewrite trans_subst; eauto. repeat constructor.

  - rewrite trans_lift; eauto.
    destruct nth_error eqn:Heq.
    econstructor. unfold trans_local. rewrite nth_error_map. rewrite Heq. simpl.
    destruct c; simpl in *. injection H; intros ->. simpl. reflexivity.
    econstructor. simpl in H. discriminate.

  - rewrite trans_mkApps; eauto with wf; simpl.
    erewrite trans_iota_red; eauto. repeat constructor.

  - simpl. eapply red_fix. wf_inv H3.
    now apply trans_unfold_fix; eauto.
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

  - constructor. solve_all. solve_all.
    apply OnOne2_map. apply (OnOne2_All_mix_left H1) in X. clear H1.
    solve_all. red. simpl. simpl in *. split; auto. apply b1. solve_all. simpl. auto.
    admit. (* Need to update template-coq's red1 with annotation preservation *)

  - rewrite !trans_mkApps; auto with wf. eapply wf_red1 in X; auto.
    apply PCUICSubstitution.red1_mkApps_l. auto.

  - apply Forall_All in H2. clear H H0 H1. revert M1. induction X.
    simpl. intuition. inv H2. specialize (X H).
    apply PCUICSubstitution.red1_mkApps_l. apply app_red_r. auto.
    inv H2. specialize (IHX H0).
    simpl. intros.
    eapply (IHX (T.tApp M1 [hd])).

  - constructor. apply IHX. constructor; hnf; simpl; auto. auto.
  - constructor. induction X; simpl; repeat constructor. apply p; auto. now inv Hwf.
    apply IHX. now inv Hwf.

  - constructor. constructor. eapply IHX; auto.
  - eapply refine_red1_r; [|constructor]. unfold subst1. simpl. now rewrite lift0_p.

  - constructor. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
    eapply b0; solve_all; eauto. rewrite b. auto. simpl.
    admit. (* Annotation preservation *)

  - apply fix_red_body. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
    unfold Template.AstUtils.app_context, trans_local in b0.
    simpl in a. rewrite -> map_app in b0.
    unfold app_context. unfold Checker.Typing.fix_context in b0.
    rewrite map_rev map_mapi in b0. simpl in b0.
    unfold fix_context. rewrite mapi_map. simpl.
    forward b0.
    { clear b0. solve_all. eapply All_app_inv; auto.
      apply All_rev. apply All_mapi. simpl.
      clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
      intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
      now eapply LiftSubst.wf_lift.
      depelim a. simpl. depelim Hwf. simpl in *. intuition auto. }
    forward b0 by auto.
    eapply (refine_red1_Γ); [|apply b0].
    f_equal. f_equal. apply mapi_ext; intros [] [].
    rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity.
    rewrite trans_lift. simpl. reflexivity. simpl.
    rewrite b. admit.

  - constructor. solve_all. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X. clear Hwf.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
    apply b0. toAll. auto. auto. rewrite b. auto. simpl. admit.

  - apply cofix_red_body. apply OnOne2_map. repeat toAll.
    apply (OnOne2_All_mix_left Hwf) in X.
    solve_all.
    red. rewrite <- !map_dtype. rewrite <- !map_dbody. intuition eauto.
    unfold Template.AstUtils.app_context, trans_local in b0.
    simpl in a. rewrite -> map_app in b0.
    unfold app_context. unfold Checker.Typing.fix_context in b0.
    rewrite map_rev map_mapi in b0. simpl in b0.
    unfold fix_context. rewrite mapi_map. simpl.
    forward b0.
    { solve_all. eapply All_app_inv; auto.
      apply All_rev. apply All_mapi. simpl.
      clear -Hwf; generalize 0 at 2; induction mfix0; constructor; hnf; simpl; auto.
      intuition auto. depelim a. simpl. depelim Hwf. simpl in *. intuition auto.
      now eapply LiftSubst.wf_lift.
      depelim a. simpl. depelim Hwf. simpl in *. intuition auto. }
    forward b0 by auto.
    eapply (refine_red1_Γ); [|apply b0].
    f_equal. f_equal. apply mapi_ext; intros [] [].
    rewrite lift0_p. simpl. rewrite LiftSubst.lift0_p. reflexivity.
    rewrite trans_lift. simpl. reflexivity. simpl.
    rewrite b. admit.
Admitted.

Lemma global_ext_levels_trans Σ
  : global_ext_levels (trans_global Σ) = TTy.global_ext_levels Σ.
Proof.
  destruct Σ.
  unfold trans_global, TTy.global_ext_levels, global_ext_levels; simpl.
  f_equal. clear u.
  induction l. reflexivity.
  simpl. rewrite IHl. f_equal. clear.
  destruct a; reflexivity.
Qed.

Lemma global_ext_constraints_trans Σ
  : global_ext_constraints (trans_global Σ) = TTy.global_ext_constraints Σ.
Proof.
  destruct Σ.
  unfold trans_global, TTy.global_ext_constraints, global_ext_constraints; simpl.
  f_equal. clear u.
  induction l. reflexivity.
  simpl. rewrite IHl. f_equal. clear.
  destruct a; reflexivity.
Qed.

Lemma trans_cumul (Σ : Ast.global_env_ext) Γ T U :
  TTy.on_global_env (fun Σ => wf_decl_pred) Σ ->
  List.Forall wf_decl Γ ->
  T.wf T -> T.wf U -> TTy.cumul Σ Γ T U ->
  trans_global Σ ;;; trans_local Γ |- trans T <= trans U.
Proof.
  intros wfΣ wfΓ.
  induction 3. constructor; auto.
  apply trans_leq_term in l; auto.
  now rewrite global_ext_constraints_trans.
  pose proof r as H3. apply wf_red1 in H3; auto.
  apply trans_red1 in r; auto. econstructor 2; eauto.
  econstructor 3.
  apply IHX; auto. apply wf_red1 in r; auto.
  apply trans_red1 in r; auto.
Qed.

Definition Tlift_typing (P : Template.Ast.global_env_ext -> Tcontext -> Tterm -> Tterm -> Type) :=
  fun Σ Γ t T =>
    match T with
    | Some T => P Σ Γ t T
    | None => { s : universe & P Σ Γ t (T.tSort s) }
    end.

Lemma trans_wf_local:
  forall (Σ : Template.Ast.global_env_ext) (Γ : Tcontext) (wfΓ : TTy.wf_local Σ Γ),
    let P :=
        (fun Σ0 (Γ0 : Tcontext) _ (t T : Tterm) _ =>
           trans_global Σ0;;; trans_local Γ0 |- trans t : trans T)
    in
    TTy.All_local_env_over TTy.typing P Σ Γ wfΓ ->
    wf_local (trans_global Σ) (trans_local Γ).
Proof.
  intros.
  induction X.
  - simpl. constructor.
  - simpl. econstructor.
    + eapply IHX.
    + simpl. destruct tu. exists x. eapply p.
  - simpl. constructor; auto. red. destruct tu. exists x. auto.
Qed.

Lemma trans_wf_local_env Σ Γ :
  TTy.All_local_env
        (TTy.lift_typing
           (fun (Σ : Ast.global_env_ext) (Γ : Tcontext) (b ty : Tterm) =>
              TTy.typing Σ Γ b ty × trans_global Σ;;; trans_local Γ |- trans b : trans ty) Σ)
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

Lemma typing_wf_wf:
  forall (Σ : Template.Ast.global_env_ext),
    TTy.wf Σ ->
    TTy.Forall_decls_typing
      (fun (_ : Template.Ast.global_env_ext) (_ : Tcontext) (t T : Tterm) => Ast.wf t /\ Ast.wf T) Σ.
Proof.
  intros Σ wf.
  red. unfold TTy.lift_typing.
  induction wf. constructor. constructor; auto.
  red. red in o0. destruct d; auto. hnf. destruct c as [ty [d|] ?] => /=.
  red in o0. simpl in o0. eapply typing_wf; eauto. simpl. auto. red.
  destruct o0. exists x; simpl in *; auto. eapply typing_wf; eauto. eauto.
  destruct o0. admit.
  (* General implication lemma would be nicer: Simon *)
Admitted.

(*   eapply TTy.on_global_decls_impl. 2:eapply wf. eauto. intros * ongl ont. destruct t. *)
(*   red in ont. *)
(*   eapply typing_wf; eauto. destruct ont. exists x; eapply typing_wf; intuition eauto. *)
(* Qed. *)

Hint Resolve trans_wf_local : trans.

Lemma check_correct_arity_trans (Σ : T.global_env_ext) idecl ind u indctx npar args pctx :
  TTy.check_correct_arity (TTy.global_ext_constraints Σ) idecl ind u indctx (firstn npar args) pctx ->
  check_correct_arity (global_ext_constraints (trans_global Σ)) (trans_one_ind_body idecl) ind u
                      (trans_local indctx) (firstn npar (map trans args))
                      (trans_local pctx).
Proof.
  destruct idecl; simpl in *. unfold TTy.check_correct_arity, check_correct_arity in *.
  simpl. (* Types of cases check *)
  clear. simpl. induction pctx; simpl. intros.
  depelim H. intros H. depelim H. constructor; auto.
  red. red in e. intuition auto.
  red. simpl. red in a0. simpl in *. destruct a as [? [?|] ?]; simpl in *; try discriminate; auto.
  red in a0. simpl in *. destruct a as [? [?|] ?]; simpl in *; try discriminate; try tauto.
  red. eapply trans_eq_term in b.
  rewrite trans_mkApps in b. constructor. admit.
Admitted.

Axiom fix_guard_trans :
  forall mfix,
    TTy.fix_guard mfix ->
    fix_guard (map (map_def trans trans) mfix).

Lemma isWFArity_wf (Σ : Ast.global_env_ext) Γ T : Typing.wf Σ -> TTy.isWfArity TTy.typing Σ Γ T -> T.wf T.
Proof.
  intros wfΣ [].
  destruct s as [s [eq wf]].
  generalize (destArity_spec [] T). rewrite eq.
  simpl. move => ->.
  apply (it_mkProd_or_LetIn_wf Γ).
  rewrite -AstUtils.it_mkProd_or_LetIn_app.
  eapply wf_it_mkProd_or_LetIn. instantiate (1:=wf).
  induction wf; constructor; auto.
  destruct t0. eapply typing_wf; eauto.
  eapply typing_wf; eauto. simpl.
  destruct t0.
  eapply typing_wf; eauto. constructor.
Qed.

Theorem template_to_pcuic (Σ : T.global_env_ext) Γ t T :
  TTy.wf Σ -> TTy.typing Σ Γ t T ->
  typing (trans_global Σ) (trans_local Γ) (trans t) (trans T).
Proof.
  simpl; intros.
  pose proof (TTy.typing_wf_local X0).
  revert Σ X Γ X1 t T X0.
  apply (TTy.typing_ind_env
           (fun Σ Γ t T => typing (trans_global Σ) (trans_local Γ) (trans t) (trans T))%type); simpl; intros;
    auto; try solve [econstructor; eauto with trans].

  - rewrite trans_lift.
    eapply refine_type. eapply type_Rel; eauto.
    eapply trans_wf_local; eauto.
    unfold trans_local. rewrite nth_error_map. rewrite H. reflexivity.
    f_equal. destruct decl; reflexivity.

  - (* Sorts *)
    constructor; eauto.
    eapply trans_wf_local; eauto.
    now rewrite global_ext_levels_trans.

  - (* Casts *)
    eapply refine_type. eapply type_App with nAnon (trans t).
    eapply type_Lambda; eauto. eapply type_Rel. econstructor; auto.
    eapply typing_wf_local. eauto. eauto. simpl. exists s; auto. reflexivity. eauto.
    simpl. unfold subst1. rewrite simpl_subst; auto. now rewrite lift0_p.

  - (* The interesting application case *)
    eapply type_mkApps; eauto.
    eapply typing_wf in X; eauto. destruct X.
    clear H1 X0 H H0. revert H2.
    induction X1. econstructor; eauto.
    (* Need updated typing_spine in template-coq *) admit.
    simpl in p.
    destruct (TypingWf.typing_wf _ wfΣ _ _ _ typrod) as [wfAB _].
    intros wfT.
    econstructor; eauto. right. exists s; eauto.
    change (tProd na (trans A) (trans B)) with (trans (T.tProd na A B)).
    apply trans_cumul; auto with trans.
    apply TypingWf.typing_wf_sigma; auto.
    eapply Forall_impl. eapply TypingWf.typing_all_wf_decl; eauto.
    intros. auto.
    eapply typing_wf in ty; eauto. destruct ty as [wfhd _].
    rewrite trans_subst in IHX1; eauto with wf. now inv wfAB.
    eapply IHX1. apply Template.LiftSubst.wf_subst; try constructor; auto. now inv wfAB.

  - rewrite trans_subst_instance_constr.
    pose proof (forall_decls_declared_constant _ _ _ H).
    replace (trans (Template.Ast.cst_type decl)) with
        (cst_type (trans_constant_body decl)) by (destruct decl; reflexivity).
    constructor; eauto with trans. admit.

  - rewrite trans_subst_instance_constr.
    pose proof (forall_decls_declared_inductive _ _ _ _ isdecl).
    replace (trans (Template.Ast.ind_type idecl)) with
        (ind_type (trans_one_ind_body idecl)) by (destruct idecl; reflexivity).
    eapply type_Ind; eauto. eauto with trans. admit.

  - pose proof (forall_decls_declared_constructor _ _ _ _ _ isdecl).
    unfold TTy.type_of_constructor in *.
    rewrite trans_subst.
    -- apply Forall_All. apply wf_inds.
    -- apply wf_subst_instance_constr.
       eapply declared_constructor_wf in isdecl; eauto with wf.
       eauto with wf trans.
       apply typing_wf_wf; auto.
    -- rewrite trans_subst_instance_constr.
       rewrite trans_inds. simpl.
       eapply refine_type. econstructor; eauto with trans. admit.
       unfold type_of_constructor. simpl. f_equal. f_equal.
       destruct cdecl as [[id t] p]; simpl; auto.

  - rewrite trans_mkApps; auto with wf trans. apply typing_wf in X1; intuition auto.
    solve_all. apply typing_wf in X3; auto. intuition auto.
    apply wf_mkApps_inv in H4.
    apply All_app_inv. apply All_skipn. solve_all. constructor; auto.
    rewrite map_app map_skipn.
    eapply type_Case.
    apply forall_decls_declared_inductive; eauto. destruct mdecl; auto.
    eapply X2.
    rewrite firstn_map.
    eapply trans_types_of_case; eauto.
    -- eapply typing_wf in X1; intuition auto.
    -- eapply typing_wf in X1; intuition auto.
    -- eapply declared_inductive_wf in isdecl; eauto.
       apply typing_wf_wf; auto.
    -- eapply typing_wf in X3; intuition auto.
       eapply wf_mkApps_inv in H4. apply All_firstn. solve_all.
    -- revert H1. apply check_correct_arity_trans.
    -- destruct idecl; simpl in *; auto.
    -- rewrite trans_mkApps in X4; auto with wf.
       eapply typing_wf in X3; auto. intuition. eapply wf_mkApps_inv in H4; auto.
    -- apply All2_map. solve_all.
       (* TODO Update type_Case for TemplateCoq *)
       admit.

  - destruct pdecl as [arity ty]; simpl in *.
    pose proof (TypingWf.declared_projection_wf _ _ u _ _ _ isdecl).
    simpl in H0.
    eapply forall_decls_declared_projection in isdecl.
    destruct (typing_wf _ wfΣ _ _ _ X1) as [wfc wfind].
    eapply wf_mkApps_inv in wfind; auto.
    rewrite trans_subst; auto with wf. constructor; solve_all.
    apply H0.
    eapply typing_wf_wf; auto.
    simpl. rewrite map_rev. rewrite trans_subst_instance_constr.
    eapply (type_Proj _ _ _ _ _ _ _ (arity, trans ty)). eauto.
    rewrite trans_mkApps in X2; auto. constructor. rewrite map_length.
    destruct mdecl; auto.

  - eapply refine_type.
    assert (fix_context (map (map_def trans trans) mfix) =
            trans_local (TTy.fix_context mfix)).
    { unfold trans_local, TTy.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext; intros i x.
      simpl. rewrite trans_lift. reflexivity. }
    econstructor; eauto.
    eapply fix_guard_trans. assumption.
    now rewrite nth_error_map H0.
    -- unfold app_context, trans_local.
       rewrite H1. unfold trans_local.
       rewrite -map_app.
       eapply trans_wf_local_env. eapply X.
    -- apply All_map. eapply All_impl; eauto.
       unfold compose. simpl. intuition eauto 3 with wf.
       rewrite H1. rewrite /trans_local map_length.
       unfold Template.AstUtils.app_context in b.
       rewrite /trans_local map_app in b.
       rewrite <- trans_lift. apply b.
       destruct (dbody x); simpl in *; congruence.
    -- destruct decl; reflexivity.

  - eapply refine_type.
    assert (fix_context (map (map_def trans trans) mfix) =
            trans_local (TTy.fix_context mfix)).
    { unfold trans_local, TTy.fix_context.
      rewrite map_rev map_mapi /fix_context mapi_map.
      f_equal. apply mapi_ext => i x.
      simpl. rewrite trans_lift. reflexivity. }
    econstructor; eauto.
    now rewrite nth_error_map H.
    -- unfold app_context, trans_local.
       rewrite H1. unfold trans_local.
       rewrite <- map_app.
       eapply trans_wf_local_env. eauto.
    -- apply All_map. eapply All_impl; eauto.
       unfold compose. simpl. intuition eauto 3 with wf.
       rewrite H1. rewrite /trans_local map_length.
       unfold Template.AstUtils.app_context in b.
       rewrite /trans_local map_app in b.
       rewrite <- trans_lift. apply b.
    -- destruct decl; reflexivity.

  - assert (T.wf B).
    { destruct X2. destruct i as [wfa allwfa].
      now apply (isWFArity_wf _ _ _ wfΣ wfa).
      destruct s as [s [H ?]].
      eapply typing_wf in H; intuition eauto. }
    eapply type_Cumul. eauto.
    * destruct X2. red in i.
      destruct i as [wfa allwfa].
      left.
      destruct wfa as [ctx [s ?]].
      exists (trans_local ctx), s. destruct p.
      generalize (trans_destArity [] B); rewrite e.
      intros. split; auto.
      eapply trans_wf_local in allwfa. simpl in allwfa.
      rewrite /trans_local in allwfa.
      now rewrite map_app in allwfa.
      right.
      destruct s as [s [? ?]]; exists s; auto.
    * clear X2. pose proof (typing_wf _ wfΣ _ _ _ X0).
      eapply trans_cumul; eauto with trans.
      eapply typing_wf_sigma; auto.
      clear X. apply typing_all_wf_decl in wfΓ; auto. solve_all.
Admitted.
