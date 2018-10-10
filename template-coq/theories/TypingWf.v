(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From Template Require Import config utils Ast AstUtils univ Induction LiftSubst UnivSubst Typing.
Require Import ssreflect.

Set Asymmetric Patterns.

(** * Well-formedness of terms and types in typing derivations

  The internal representation of terms is not canonical, so we show
  that only well-formed terms and types can appear in typing derivations
  and the global context.
*)


Definition wf_decl d := match decl_body d with Some b => Ast.wf b | None => True end /\ Ast.wf (decl_type d).

Definition wf_decl_pred : global_context -> context -> term -> term -> Type :=
  (fun _ _ t T => Ast.wf t /\ Ast.wf T).

Lemma All_local_env_wf_decl:
  forall Σ (Γ : context),
    Forall wf_decl Γ -> All_local_env wf_decl_pred Σ Γ.
Proof.
  intros Σ Γ X.
  induction Γ in X |- *.
  - constructor; eauto.
  - destruct a as [na [body|] ty].
    constructor. apply IHΓ. inv X; eauto.
    red. inv X. eauto.
    eapply (localenv_cons_abs _ _ _ _ _ (Universe.make Level.lProp)).
    apply IHΓ. inv X; eauto.
    red. inv X. red in H. intuition eauto. constructor.
Qed.

Lemma All_local_env_wf_decl_inv:
  forall (Σ : global_context) (a : context_decl) (Γ : list context_decl)
         (X : All_local_env wf_decl_pred Σ (a :: Γ)),
    on_local_decl wf_decl_pred Σ Γ a * All_local_env wf_decl_pred Σ Γ.
Proof.
  intros Σ a Γ X.
  inv X; intuition; red; simpl; eauto.
Qed.

Lemma wf_strip_outer_cast t : Ast.wf t -> Ast.wf (strip_outer_cast t).
Proof.
  induction t; auto.
  simpl. intros H; now inv H.
Qed.

Lemma wf_mkApps_napp t u : isApp t = false -> Ast.wf (mkApps t u) -> Ast.wf t /\ List.Forall Ast.wf u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros Happ H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (tApp t (l ++ [a]))).
    forward IHu.
    induction u; trivial. discriminate.
Qed.
Hint Resolve wf_mkApps_napp : wf.

Lemma wf_mkApps_inv t u : Ast.wf (mkApps t u) -> List.Forall Ast.wf u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (tApp t (l ++ [a]))).
    forward IHu.
    induction u; trivial.
    simpl. rewrite <- app_assoc. simpl. apply H.
    intuition. inv H.
    apply Forall_app in H3. intuition.
Qed.
Hint Resolve wf_mkApps_inv : wf.
Hint Constructors Ast.wf : wf.

Lemma isLambda_isApp t : isLambda t = true -> isApp t = false.
Proof. destruct t; simpl; congruence. Qed.

Lemma unfold_fix_wf:
  forall (mfix : mfixpoint term) (idx : nat) (narg : nat) (fn : term),
    unfold_fix mfix idx = Some (narg, fn) ->
    Ast.wf (tFix mfix idx) ->
    Ast.wf fn /\ isApp fn <> true.
Proof.
  intros mfix idx narg fn Hf Hwf.
  unfold unfold_fix in Hf. inv Hwf.
  destruct nth_error eqn:eqnth; try congruence.
  pose proof (nth_error_forall eqnth H). simpl in H0.
  injection Hf. intros <- <-.
  destruct H0 as [ _ [ wfd islamd ] ]. apply (isLambda_subst (fix_subst mfix) 0) in islamd.
  apply isLambda_isApp in islamd. split; try congruence.
  apply wf_subst; auto. clear wfd islamd Hf eqnth.
  assert(forall n, Ast.wf (tFix mfix n)). constructor; auto.
  unfold fix_subst. generalize #|mfix|; intros. induction n; auto.
Qed.

Lemma unfold_cofix_wf:
  forall (mfix : mfixpoint term) (idx : nat) (narg : nat) (fn : term),
    unfold_cofix mfix idx = Some (narg, fn) ->
    Ast.wf (tCoFix mfix idx) -> Ast.wf fn.
Proof.
  intros mfix idx narg fn Hf Hwf.
  unfold unfold_cofix in Hf. inv Hwf.
  destruct nth_error eqn:eqnth; try congruence.
  pose proof (nth_error_forall eqnth H). simpl in H0.
  injection Hf. intros <- <-.
  destruct H0 as [ _ wfd ].
  apply wf_subst; auto. clear wfd Hf eqnth.
  assert(forall n, Ast.wf (tCoFix mfix n)). constructor; auto.
  unfold cofix_subst. generalize #|mfix|; intros. induction n; auto.
Qed.

Lemma wf_subst_instance_constr u c :
  Ast.wf c -> Ast.wf (subst_instance_constr u c).
Proof.
  induction 1 using term_wf_forall_list_ind; simpl; try solve [ constructor; auto using Forall_map ].

  constructor; auto. destruct t; simpl in *; try congruence. destruct l; simpl in *; congruence.
  now apply Forall_map.
  constructor; auto. solve_all.
  unfold compose. solve_all.
  destruct x; simpl in *.
  destruct dbody; simpl in *; congruence.
Qed.

Lemma wf_nth:
  forall (n : nat) (args : list term), Forall Ast.wf args -> Ast.wf (nth n args tDummy).
Proof.
  intros n args H. induction H in n; destruct n; simpl; try constructor; auto.
Qed.
Hint Resolve wf_nth.

Lemma red1_isLambda Σ Γ t u :
  red1 Σ Γ t u -> isLambda t -> isLambda u.
Proof.
  induction 1 using red1_ind_all; simpl; try discriminate; auto.
Qed.

Lemma OnOne2_All_All {A} {P Q} {l l' : list A} :
  OnOne2 P l l' ->
  (forall x y, P x y -> Q x -> Q y) ->
  All Q l -> All Q l'.
Proof. intros Hl H. induction Hl; intros H'; inv H'; constructor; eauto. Qed.

Lemma All_mapi {A B} (P : B -> Type) (l : list A) (f : nat -> A -> B) :
  Alli (fun i x => P (f i x)) 0 l -> All P (mapi f l).
Proof.
  unfold mapi. generalize 0.
  induction 1; constructor; auto.
Qed.

Lemma Alli_id {A} (P : nat -> A -> Type) n (l : list A) :
  (forall n x, P n x) -> Alli P n l.
Proof.
  intros H. induction l in n |- *; constructor; auto.
Qed.

Lemma wf_red1 `{CF:checker_flags} Σ Γ M N :
  on_global_env (fun Σ Γ t T => match t with Some b => Ast.wf b /\ Ast.wf T | None => Ast.wf T end) Σ ->
  List.Forall (fun d => match decl_body d with Some b => Ast.wf b | None => True end) Γ ->
  Ast.wf M -> red1 (fst Σ) Γ M N -> Ast.wf N.
Proof.
  intros wfΣ wfΓ wfM H.
  induction H using red1_ind_all in wfM, wfΓ |- *; inv wfM; try solve[ constructor; auto with wf ].

  - inv H1. inv H2.
    eauto with wf.
  - auto with wf.
  - apply wf_lift.
    unfold option_map in H. destruct nth_error eqn:Heq; try discriminate.
    eapply nth_error_forall in wfΓ; eauto. simpl in *. destruct (decl_body c); congruence.
  - unfold iota_red.
    apply wf_mkApps_inv in H0.
    apply wf_mkApps; auto.
    induction brs in c, H1 |- *; destruct c; simpl in *. constructor. constructor.
    inv H1; auto. inv H1; auto.
    induction H0 in pars |- *; destruct pars; try constructor; auto. simpl. auto.
  - apply unfold_fix_wf in H; auto. constructor; intuition auto.
  - constructor; auto. apply wf_mkApps_napp in H1 as [Hcof Hargs]; auto.
    apply unfold_cofix_wf in H; auto.
    apply wf_mkApps; intuition auto.
  - constructor; auto. apply wf_mkApps_napp in H0 as [Hcof Hargs]; auto.
    apply unfold_cofix_wf in H; auto.
    apply wf_mkApps; intuition auto.
  - apply wf_subst_instance_constr.
    unfold declared_constant in H.
    eapply lookup_on_global_env in H as [Σ' [onΣ' prf]]; eauto.
    destruct decl; simpl in *.
    subst cst_body; intuition. red in prf. simpl in prf. easy.
  - apply wf_mkApps_inv in H0.
    eapply nth_error_forall in H0; eauto.
  - constructor; auto. apply IHred1; auto. constructor; simpl; auto.
  - constructor; auto. apply IHred1; auto. constructor; simpl; auto.
  - constructor; auto. induction H; constructor; inv H2; intuition auto.
  - apply wf_mkApps; auto.
  - constructor; auto. induction H; congruence.
    clear H1. induction H; inv H3; constructor; intuition auto.
  - constructor; auto. apply IHred1; auto. constructor; simpl; auto.
  - constructor; auto. induction H; inv H0; constructor; intuition auto.
  - auto.
  - constructor; auto.
    induction H; inv H0; constructor; intuition auto; congruence.
  - constructor; auto. solve_all.
    revert H0.
    apply (OnOne2_All_All H). clear H.
    intros. destruct H as [Hred [<- Hwf]].
    intuition. apply Hwf. solve_all. apply All_app_inv; auto. unfold fix_context.
    apply All_rev.
    eapply All_mapi. simpl. apply Alli_id. intros; exact I.
    auto.
    apply red1_isLambda in Hred; auto.
  - constructor; auto.
    induction H; inv H0; constructor; intuition auto; congruence.
  - constructor; auto. solve_all. revert H0.
    apply (OnOne2_All_All H). clear H.
    intros. destruct H as [Hred [<- Hwf]].
    intuition. apply Hwf. solve_all. apply All_app_inv; auto. unfold fix_context.
    apply All_rev.
    eapply All_mapi. simpl. apply Alli_id. intros; exact I.
    auto.
Qed.

Ltac wf := intuition try (eauto with wf || congruence || solve [constructor]).
Hint Unfold wf_decl vass vdef : wf.
Hint Extern 10 => progress simpl : wf.
Hint Unfold snoc : wf.
Hint Extern 3 => apply wf_lift || apply wf_subst || apply wf_subst_instance_constr : wf.
Hint Extern 10 => constructor : wf.
Hint Resolve All_skipn : wf.

Lemma wf_inds mind bodies u : Forall Ast.wf (inds mind u bodies).
Proof.
  unfold inds. generalize #|bodies|. induction n. constructor.
  constructor; auto. wf.
Qed.

Hint Resolve wf_inds : wf.

Ltac specialize_goal :=
  repeat match goal with
  | H : ?P -> _, H' : ?P |- _ => specialize (H H')
  end.

Lemma wf_lift_wf n k t : Ast.wf (lift n k t) -> Ast.wf t.
Proof.
  induction t in n, k |- * using term_forall_list_ind; simpl in *;
    intros Hwf; inv Hwf; try constructor; eauto;
      repeat (unfold compose, snd, on_snd in *; simpl in *; solve_all).

  - destruct t; try discriminate. simpl in *. congruence.
  - destruct l; simpl in *; congruence.
  - destruct x; simpl in *; intuition eauto.
    destruct dbody; simpl in *; try discriminate. destruct Nat.leb; auto.
    reflexivity.
Qed.

Lemma declared_projection_wf:
  forall (H : checker_flags) (Σ : global_context) (p : projection) (u : universe_instance)
         (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (pdecl : ident * term),
    declared_projection (fst Σ) mdecl idecl p pdecl ->
    Forall_decls_typing (fun (_ : global_context) (_ : context) (t T : term) => Ast.wf t /\ Ast.wf T) Σ ->
    Ast.wf (subst_instance_constr u (snd pdecl)).
Proof.
  intros H Σ p u mdecl idecl pdecl isdecl X.
  destruct isdecl as [[Hmdecl Hidecl] Hpdecl].
  eapply lookup_on_global_env in Hmdecl as [Σ' [wfΣ' prf]]; eauto. red in prf.
  apply onInductives in prf.
  eapply nth_error_alli in Hidecl; eauto. intuition.
  eapply onProjections in Hidecl.
  eapply nth_error_alli in Hidecl; eauto. red in Hidecl.
  destruct decompose_prod_assum.
  destruct Hidecl as [[s Hs] Hnpars]. apply wf_subst_instance_constr. apply Hs.
Qed.

Lemma typing_wf_gen `{checker_flags} : env_prop (fun Σ Γ t T => Ast.wf t /\ Ast.wf T).
Proof.
  apply typing_ind_env; intros; auto with wf;
    specialize_goal;
    try solve [split; try constructor; intuition auto with wf].

  - split; wf. apply wf_lift.
    apply (All_local_env_lookup H1) in H0.
    red in H0. destruct decl as [na [body|] ty]; simpl in *; intuition auto.
    destruct H0; intuition auto.
  - split. constructor; auto. wf.
    clear H1 H2 X.
    induction X0. wf. constructor. wf.
    apply IHX0. split. wf. apply wf_subst. wf. wf. now inv H0.
    clear H1 H2 X.
    induction X0. wf. apply IHX0. constructor. wf.
    apply wf_subst. wf. wf. now inv H0.
  - split. wf. apply wf_subst_instance_constr. wf.
    red in H0.
    eapply lookup_on_global_env in H0 as [Σ' [wfΣ' prf]]; eauto.
    red in prf. destruct decl; destruct cst_body; red in prf; simpl in *; wf.
    destruct prf. apply a.

  - split. wf. apply wf_subst_instance_constr. wf.
    destruct isdecl as [Hmdecl Hidecl]. red in Hmdecl.
    eapply lookup_on_global_env in X as [Σ' [wfΣ' prf]]; eauto.
    apply onInductives in prf.
    eapply nth_error_alli in Hidecl; eauto.
    eapply onArity in Hidecl.
    destruct Hidecl as [[s Hs] Hpars]; wf.
  - split. wf.
    destruct isdecl as [[Hmdecl Hidecl] Hcdecl]. red in Hmdecl.
    eapply lookup_on_global_env in X as [Σ' [wfΣ' prf]]; eauto. red in prf.
    apply onInductives in prf.
    eapply nth_error_alli in Hidecl; eauto. simpl in *. intuition.
    apply onConstructors in Hidecl.
    eapply nth_error_alli in Hcdecl; eauto.
    destruct Hcdecl as [[s Hs] Hpars]. unfold type_of_constructor. wf.
  - split. wf. constructor; eauto. solve_all.
    apply wf_mkApps. wf. solve_all. apply wf_mkApps_inv in H10. solve_all.
    apply All_app_inv; solve_all. now apply All_skipn.
  - split. wf. apply wf_subst. solve_all. constructor. wf.
    apply wf_mkApps_inv in H3. apply All_rev. solve_all.
    subst ty. eapply declared_projection_wf in isdecl; eauto.

  - subst types.
    apply All_local_env_app in X as [HΓ Hmfix].
    clear Hmfix.
    split.
    + revert X0. generalize (fix_context mfix). intros.
      clear decl H0. constructor. induction mfix. constructor. constructor.
      2:{ apply IHmfix. inv X0. auto. }
      inv X0. intuition. now apply wf_lift_wf in H1.
    + eapply nth_error_all in X0; eauto. simpl in X0. intuition eauto.
      now apply wf_lift_wf in H2.
  - subst types.
    apply All_local_env_app in X as [HΓ Hmfix].
    clear Hmfix.
    split.
    + revert X0. generalize (fix_context mfix). intros.
      clear decl H0. constructor. induction mfix. constructor. constructor.
      2:{ apply IHmfix. inv X0. auto. }
      inv X0. intuition. now apply wf_lift_wf in H1.
    + eapply nth_error_all in X0; eauto. simpl in X0; intuition eauto.
      now apply wf_lift_wf in H2.
Qed.

Lemma typing_all_wf_decl `{checker_flags} Σ (wfΣ : wf Σ) Γ (wfΓ : wf_local Σ Γ) :
  Forall wf_decl Γ.
Proof.
  induction wfΓ. constructor. constructor; auto. red. simpl. split; wf.
  apply typing_wf_gen in t0; eauto. apply t0; auto.
  constructor; auto. red; simpl. apply typing_wf_gen in t0; auto. intuition auto.
Qed.
Hint Resolve typing_all_wf_decl : wf.

Lemma typing_wf_sigma `{checker_flags} Σ (wfΣ : wf Σ) :
  on_global_env (fun Σ Γ t T => match t with Some b => Ast.wf b /\ Ast.wf T | None => Ast.wf T end) Σ.
Proof.
  intros.
  pose proof (env_prop_sigma _ typing_wf_gen _ wfΣ). red in X.
  red in X. unfold lift_typing in X. red. do 2 red in wfΣ.
  unshelve eapply (on_global_decls_mix _ wfΣ) in X.
  red. intros. destruct b; intuition auto with wf.
  destruct X0 as [u Hu]. exists u. intuition auto with wf.
  clear wfΣ.
  eapply on_global_decls_impl; eauto; simpl; intros. clear X.
  destruct X1 as [Hty Ht].
  pose proof (on_global_decls_proj X0).
  destruct t. apply Ht. destruct Ht; wf.
Qed.

Lemma typing_wf `{checker_flags} Σ (wfΣ : wf Σ) Γ t T :
  Σ ;;; Γ |- t : T -> Ast.wf t /\ Ast.wf T.
Proof.
  intros. eapply typing_wf_gen in X; intuition eauto with wf.
Qed.
