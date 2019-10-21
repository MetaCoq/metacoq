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
From Equations Require Import Equations.
Require Import Equations.Prop.DepElim.

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

Definition isApp t := match t with tApp _ _ => true | _ => false end.


Definition Tlift_typing (P : Template.Ast.global_env_ext -> Tcontext -> Tterm -> Tterm -> Type) :=
  fun Σ Γ t T =>
    match T with
    | Some T => P Σ Γ t T
    | None => { s : universe & P Σ Γ t (T.tSort s) }
    end.

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
Admitted.
