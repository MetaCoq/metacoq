(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils Ast AstUtils Induction LiftSubst
     UnivSubst Reduction WfInv Typing.
From Equations Require Import Equations.
Require Import ssreflect ssrbool.

(** * Well-formedness of terms and types in typing derivations

  The internal representation of terms is not canonical, so we show
  that only well-formed terms and types can appear in typing derivations
  and the global context.
*)


Definition wf_decl d :=
  match decl_body d with
  | Some b => Ast.wf b
  | None => True
  end /\ Ast.wf (decl_type d).

Definition wf_decl_pred : context -> term -> option term -> Type :=
  (fun _ t T => Ast.wf t /\ match T with
                        | Some T => Ast.wf T
                        | None => True
                        end).

Lemma All_local_env_wf_decl :
  forall (Γ : context),
    Forall wf_decl Γ -> All_local_env wf_decl_pred Γ.
Proof.
  intros Γ X.
  induction Γ in X |- *.
  - constructor; eauto.
  - destruct a as [na [body|] ty].
    + econstructor.
      * apply IHΓ. inv X; eauto.
      * red. inv X. split.
        -- apply H.
        -- constructor.
      * red. inv X. eauto.
    + econstructor.
      * apply IHΓ. inv X; eauto.
      * red. inv X. split.
        -- apply H.
        -- constructor.
Qed.

Lemma All_local_env_wf_decl_inv:
  forall (a : context_decl) (Γ : list context_decl)
         (X : All_local_env wf_decl_pred (a :: Γ)),
    on_local_decl wf_decl_pred Γ a * All_local_env wf_decl_pred Γ.
Proof.
  intros a Γ X.
  inv X; intuition; red; simpl; eauto.
Qed.

Lemma wf_strip_outer_cast t : Ast.wf t -> Ast.wf (strip_outer_cast t).
Proof.
  induction t; auto.
  simpl. intros H; now inv H.
Qed.

Lemma wf_mkApps_napp t u : ~~ isApp t -> Ast.wf (mkApps t u) -> Ast.wf t /\ List.Forall Ast.wf u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros Happ H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (tApp t (u ++ [a]))).
    forward IHu.
    induction u; trivial. discriminate.
Qed.
#[global]
Hint Resolve wf_mkApps_napp : wf.

Lemma wf_mkApps_inv t u : Ast.wf (mkApps t u) -> List.Forall Ast.wf u.
Proof.
  induction u in t |- *; simpl.
  - intuition.
  - intros H; destruct t; try solve [inv H; intuition auto].
    specialize (IHu (tApp t (args ++ [a]))).
    forward IHu.
    induction u; trivial.
    simpl. rewrite <- app_assoc. simpl. apply H.
    intuition. inv H.
    apply Forall_app in H3. intuition.
Qed.
#[global]
Hint Resolve wf_mkApps_inv : wf.
#[global]
Hint Constructors Ast.wf : wf.

Lemma isLambda_isApp t : isLambda t = true -> ~~ isApp t.
Proof. destruct t; simpl; congruence. Qed.

Lemma unfold_fix_wf:
  forall (mfix : mfixpoint term) (idx : nat) (narg : nat) (fn : term),
    unfold_fix mfix idx = Some (narg, fn) ->
    Ast.wf (tFix mfix idx) ->
    Ast.wf fn.
Proof.
  intros mfix idx narg fn Hf Hwf.
  unfold unfold_fix in Hf. inv Hwf.
  destruct nth_error eqn:eqnth; try congruence.
  pose proof (nth_error_forall eqnth H). simpl in H0.
  destruct H0 as [ _ wfd].
  injection Hf. intros <- <-.
  apply wf_subst; auto. clear wfd Hf eqnth.
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
  - constructor; auto. destruct t; simpl in *; try congruence.
    destruct l; simpl in *; congruence.
    now apply Forall_map.
  - constructor; auto. solve_all.
  - constructor. solve_all.
  - constructor. solve_all.
Qed.

Lemma wf_nth:
  forall (n : nat) (args : list term), Forall Ast.wf args -> Ast.wf (nth n args tDummy).
Proof.
  intros n args H. induction H in n; destruct n; simpl; try constructor; auto.
Qed.
#[global]
Hint Resolve wf_nth : core.

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


Lemma All_Alli {A} {P : A -> Type} {Q : nat -> A -> Type} {l n} :
  All P l ->
  (forall n x, P x -> Q n x) ->
  Alli Q n l.
Proof. intro H. revert n. induction H; constructor; eauto. Qed.


Lemma wf_red1 {cf:checker_flags} Σ Γ M N :
  on_global_env (fun Σ => wf_decl_pred) Σ ->
  List.Forall wf_decl Γ ->
  Ast.wf M ->
  red1 Σ Γ M N ->
  Ast.wf N.
Proof.
  intros wfΣ wfΓ wfM H.
  induction H using red1_ind_all in wfM, wfΓ |- *.
  all: inv wfM.
  all: try solve[ constructor; auto with wf ].

  - inv H1. inv H2.
    eauto with wf.
  - auto with wf.
  - apply wf_lift.
    unfold option_map in H. destruct nth_error eqn:Heq; try discriminate.
    eapply nth_error_forall in wfΓ; eauto. unfold wf_decl in *.
    apply some_inj in H; rewrite H in wfΓ; apply wfΓ.
  - unfold iota_red.
    apply wf_mkApps_inv in H0.
    apply wf_mkApps; auto.
    induction brs in c, H1 |- *; destruct c; simpl in *. constructor. constructor.
    inv H1; auto. inv H1; auto.
    induction H0 in pars |- *; destruct pars; try constructor; auto. simpl. auto.
  - apply unfold_fix_wf in H; auto. eapply wf_mkApps; auto.
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
    subst cst_body; simpl in *; compute in prf; intuition auto.
  - apply wf_mkApps_inv in H0.
    eapply nth_error_forall in H0; eauto.
  - constructor; auto. apply IHred1; auto. constructor; simpl; auto.
    constructor; cbn; easy.
  - constructor; auto. apply IHred1; auto. constructor; simpl; auto.
    constructor; auto.
  - constructor; auto. induction X; constructor; inv H1; intuition auto.
  - apply wf_mkApps; auto.
  - constructor; auto. induction X; congruence.
    clear H0. induction X; inv H2; constructor; intuition auto.
  - constructor; auto. apply IHred1; auto. constructor; simpl; auto.
    constructor; cbn; easy.
  - constructor; auto. induction X; inv H; constructor; intuition auto.
  - auto.
  - constructor; auto.
    induction X; inv H; constructor; intuition auto; congruence.
  - constructor; auto. solve_all.
    pose proof H as H'. revert H.
    apply (OnOne2_All_All X). clear X.
    intros [na bo ty ra] [nb bb tb rb] [[r ih] e] [? ?].
    simpl in *.
    inversion e. subst. clear e.
    intuition eauto.
    + eapply ih. 2: assumption.
      solve_all. apply All_app_inv. 2: assumption.
      unfold fix_context. apply All_rev. eapply All_mapi.
      eapply All_Alli. 1: exact H'.
      cbn. unfold wf_decl. simpl.
      intros ? [? ? ? ?] ?. simpl in *.
      intuition eauto with wf.
  - constructor; auto.
    induction X; inv H; constructor; intuition auto; congruence.
  - constructor; auto. solve_all.
    pose proof H as H'. revert H.
    apply (OnOne2_All_All X). clear X.
    intros [na bo ty ra] [nb bb tb rb] [[r ih] e] [? ?].
    simpl in *.
    inversion e. subst. clear e.
    intuition eauto.
    eapply ih. 2: assumption.
    solve_all. apply All_app_inv. 2: assumption.
    unfold fix_context. apply All_rev. eapply All_mapi.
    eapply All_Alli. 1: exact H'.
    cbn. unfold wf_decl. simpl.
    intros ? [? ? ? ?] ?. simpl in *.
    intuition eauto with wf.
Qed.

Ltac wf := intuition try (eauto with wf || congruence || solve [constructor]).
#[global]
Hint Unfold wf_decl vass vdef : wf.
#[global]
Hint Extern 10 => progress simpl : wf.
#[global]
Hint Unfold snoc : wf.
#[global]
Hint Extern 3 => apply wf_lift || apply wf_subst || apply wf_subst_instance_constr : wf.
#[global]
Hint Extern 10 => constructor : wf.
#[global]
Hint Resolve All_skipn : wf.

Lemma wf_inds mind bodies u : Forall Ast.wf (inds mind u bodies).
Proof.
  unfold inds. generalize #|bodies|. induction n. constructor.
  constructor; auto. wf.
Qed.

#[global]
Hint Resolve wf_inds : wf.

Lemma wf_projs ind npars p : Forall Ast.wf (projs ind npars p).
Proof.
  unfold projs. induction p; constructor; wf.
Qed.

Ltac specialize_goal :=
  repeat match goal with
  | H : ?P -> _, H' : ?P |- _ => specialize (H H')
  end.

Lemma wf_lift_wf n k t : Ast.wf (lift n k t) -> Ast.wf t.
Proof.
  induction t in n, k |- * using term_forall_list_ind; simpl in *;
    intros Hwf; inv Hwf; try constructor; eauto;
      repeat (unfold snd, on_snd in *; simpl in *; solve_all).

  - destruct t; try reflexivity. discriminate.
  - destruct l; simpl in *; congruence.
Qed.

Lemma declared_inductive_wf {cf:checker_flags} :
  forall (Σ : global_env) ind
         (mdecl : mutual_inductive_body) (idecl : one_inductive_body),
  Forall_decls_typing (fun (_ : global_env_ext) (_ : context) (t T : term) => Ast.wf t /\ Ast.wf T) Σ ->
  declared_inductive Σ mdecl ind idecl -> Ast.wf (ind_type idecl).
Proof.
  intros.
  destruct H as [Hmdecl Hidecl]. red in Hmdecl.
  eapply lookup_on_global_env in X as [Σ' [wfΣ' prf]]; eauto.
  apply onInductives in prf.
  eapply nth_error_alli in Hidecl; eauto.
  eapply onArity in Hidecl.
  destruct Hidecl as [s Hs]; wf.
Qed.

Lemma declared_constructor_wf {cf:checker_flags}:
  forall (Σ : global_env) (ind : inductive) (i : nat) (u : list Level.t)
         (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : ident * term * nat),
    Forall_decls_typing (fun (_ : global_env_ext) (_ : context) (t T : term) => Ast.wf t /\ Ast.wf T) Σ ->
    declared_constructor Σ mdecl idecl (ind, i) cdecl ->
    Ast.wf (cdecl_type cdecl).
Proof.
  intros Σ ind i u mdecl idecl cdecl X isdecl.
  destruct isdecl as [[Hmdecl Hidecl] Hcdecl]. red in Hmdecl.
  eapply lookup_on_global_env in X as [Σ' [wfΣ' prf]]; eauto. red in prf.
  apply onInductives in prf.
  eapply nth_error_alli in Hidecl; eauto. simpl in *.
  pose proof (onConstructors Hidecl) as h. unfold on_constructors in h.
  eapply All2_nth_error_Some in Hcdecl. 2: eassumption.
  destruct Hcdecl as [cs [Hnth [? ? ? [? [? ?]] ?]]].
  assumption.
Qed.
 
Lemma on_inductive_wf_params {cf:checker_flags} {Σ : global_env_ext} {ind mdecl} :
    forall (oib : on_inductive
    (lift_typing (fun _ _ (t T : term) => Ast.wf t /\ Ast.wf T)) Σ
    (inductive_mind ind) mdecl),
    Forall wf_decl (ind_params mdecl).
Proof.
  intros oib. apply onParams in oib.
  red in oib.
  induction (ind_params mdecl) as [|[? [] ?] ?]; simpl in oib; inv oib; constructor;
    try red in X0; try red in X1; try red; simpl; intuition auto.
  destruct X0; intuition auto.
Qed.

Lemma declared_inductive_wf_shapes {cf:checker_flags} {Σ : global_env_ext} {ind mdecl idecl} :
    forall (oib : on_ind_body
    (lift_typing (fun _ _ (t T : term) => Ast.wf t /\ Ast.wf T)) Σ
    (inductive_mind ind) mdecl (inductive_ind ind) idecl),
    Forall (fun cs => Forall wf_decl (cshape_args cs)) oib.(ind_cshapes).
Proof.
  intros oib.
  pose proof (onConstructors oib) as h. unfold on_constructors in h.
  induction h; constructor; auto.
  destruct r.
  clear -on_cargs.
  revert on_cargs. generalize (cshape_sorts y).
  induction (cshape_args y) as [|[? [] ?] ?]; simpl;
    destruct l; intuition auto;
    constructor;
    try red; simpl; intuition eauto.
Qed.

Lemma wf_subst_context s k Γ : Forall wf_decl Γ -> Forall Ast.wf s -> Forall wf_decl (subst_context s k Γ).
Proof.
  intros wfΓ. induction wfΓ in s |- *.
  - intros. constructor.
  - rewrite subst_context_snoc. constructor; auto.
    destruct H. destruct x as [? [] ?]; constructor; simpl in *; wf.
Qed.

Lemma wf_smash_context Γ Δ : Forall wf_decl Γ -> Forall wf_decl Δ ->
   Forall wf_decl (smash_context Δ Γ).
Proof.
  intros wfΓ; induction wfΓ in Δ |- *; intros wfΔ; simpl; auto.
  destruct x as [? [] ?]; simpl. apply IHwfΓ.
  eapply wf_subst_context; auto. constructor; auto. apply H.
  eapply IHwfΓ.
  eapply All_Forall. apply All_app_inv; auto. now apply Forall_All in wfΔ.
Qed.

(* Lemma smash_context_app Γ Δ : smash_context Δ Γ = smash_context [] Γ ++ Δ.
Proof.
  induction Γ in Δ |- *; simpl; auto.
  destruct a as [? [] ?]; simpl; auto. rewrite IHΓ.
  rewrite IHΓ. *)

Lemma declared_projection_wf {cf:checker_flags}:
  forall (Σ : global_env) (p : projection)
         (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (pdecl : ident * term),
    declared_projection Σ mdecl idecl p pdecl ->
    Forall_decls_typing (fun (_ : global_env_ext) (_ : context) (t T : term) => Ast.wf t /\ Ast.wf T) Σ ->
    Ast.wf (snd pdecl).
Proof.
  intros Σ p mdecl idecl pdecl isdecl X.
  destruct isdecl as [[Hmdecl Hidecl] Hpdecl].
  eapply lookup_on_global_env in Hmdecl as [Σ' [wfΣ' prf]]; eauto. red in prf.
  assert (wfpars := on_inductive_wf_params prf).
  apply onInductives in prf.
  eapply nth_error_alli in Hidecl; eauto. intuition auto.
  pose proof (onProjections Hidecl) as on_projs.
  forward on_projs by now eapply nth_error_Some_non_nil in H.
  destruct (ind_cshapes Hidecl) as [|? [|]] eqn:Heq; try contradiction.
  destruct on_projs.
  eapply nth_error_alli in on_projs; eauto. red in on_projs.
  hnf in on_projs. simpl in on_projs.
  destruct (nth_error (smash_context _ _) _) eqn:Heq'; try contradiction.
  pose proof (declared_inductive_wf_shapes Hidecl).
  eapply Forall_All in H1.
  simpl in Heq. rewrite Heq in H1.
  inv H1. clear X0. destruct on_projs as [onna on_projs]. rewrite on_projs.
  eapply wf_subst.    
  eapply wf_inds. eapply wf_subst. eapply wf_projs.
  eapply wf_lift. eapply app_Forall in wfpars; [|eapply H2].
  eapply (wf_smash_context _ []) in wfpars.
  2:constructor.
  eapply nth_error_forall in Heq'; eauto.
  apply Heq'.
Qed.

(* TODO MOVE *)
Definition on_option {A} (P : A -> Prop) (o : option A) :=
  match o with
  | Some x => P x
  | None => True
  end.

Lemma declared_constant_wf {cf:checker_flags} :
  forall Σ cst decl,
    Forall_decls_typing (fun (_ : global_env_ext) (_ : context) (t T : term) =>
      Ast.wf t /\ Ast.wf T
    ) Σ ->
    declared_constant Σ cst decl ->
    Ast.wf decl.(cst_type) /\
    on_option Ast.wf decl.(cst_body).
Proof.
  intros Σ cst decl wΣ h.
  unfold declared_constant in h.
  eapply lookup_on_global_env in h as [Σ' [wΣ' h']]. 2: eassumption.
  simpl in h'.
  destruct decl as [ty [bo|]]. all: cbn in *.
  - intuition eauto.
  - destruct h'. intuition eauto.
Qed.


Lemma destArity_spec ctx T :
  match destArity ctx T with
  | Some (ctx', s) => it_mkProd_or_LetIn ctx T = it_mkProd_or_LetIn ctx' (tSort s)
  | None => True
  end.
Proof.
  induction T in ctx |- *; simpl; try easy.
  - specialize (IHT2 (ctx,, vass na T1)). now destruct destArity.
  - specialize (IHT3 (ctx,, vdef na T1 T2)). now destruct destArity.
Qed.


Lemma wf_it_mkProd_or_LetIn `{checker_flags} Σ Γ (wfΓ : wf_local Σ Γ)
  : All_local_env_over typing
  (fun (Σ : global_env_ext) (Γ : context) (_ : wf_local Σ Γ)
     (t T : term) (_ : Σ;;; Γ |- t : T) => Ast.wf t /\ Ast.wf T) Σ
         Γ wfΓ
-> forall t, Ast.wf t -> Ast.wf (it_mkProd_or_LetIn Γ t).
Proof.
  induction 1; simpl.
  - trivial.
  - intros t0 Ht0. apply IHX. constructor. apply p. assumption.
  - intros t0 Ht0. apply IHX. constructor. apply p. apply p. assumption.
Qed.

Lemma it_mkProd_or_LetIn_wf Γ t
  : Ast.wf (it_mkProd_or_LetIn Γ t) -> Ast.wf t.
Proof.
  revert t. induction Γ; [trivial|]. intros t XX.
  destruct a, decl_body; simpl in *.
  apply IHΓ in XX. now inv XX.
  apply IHΓ in XX. now inv XX.
Qed.


Lemma typing_wf_gen {cf:checker_flags} : env_prop (fun Σ Γ t T => Ast.wf t /\ Ast.wf T).
Proof.
  apply typing_ind_env; intros; auto with wf;
    specialize_goal;
    try solve [split; try constructor; intuition auto with wf].

  - split; wf. apply wf_lift.
    pose proof (nth_error_All_local_env_over H X) as XX.
    cbn in XX.
    destruct decl as [na [body|] ty]; simpl in *; intuition auto.
  - split. constructor; auto. wf.
    clear H0 H1 X.
    induction X0. wf. constructor. wf.
    apply IHX0. split. wf. apply wf_subst. wf. wf. now inv H.
    clear H0 H1 X.
    induction X0. wf. apply IHX0. constructor. wf.
    apply wf_subst. wf. wf. now inv H.
  - split. wf. apply wf_subst_instance_constr. wf.
    red in H.
    eapply lookup_on_global_env in H as [Σ' [wfΣ' prf]]; eauto.
    red in prf. destruct decl; destruct cst_body; red in prf; simpl in *; wf.
    destruct prf. apply a.

  - split. wf. apply wf_subst_instance_constr.
    eapply declared_inductive_wf; eauto.

  - split. wf. unfold type_of_constructor.
    apply wf_subst; auto with wf. apply wf_subst_instance_constr.
    eapply declared_constructor_wf; eauto.
  - split. wf. constructor; eauto. solve_all.
    apply wf_mkApps. wf. solve_all. apply wf_mkApps_inv in H8. solve_all.
    apply All_app_inv; solve_all. now apply All_skipn.
  - split. wf. apply wf_subst. solve_all. constructor. wf.
    apply wf_mkApps_inv in H2. apply All_rev. solve_all.
    subst ty. eapply declared_projection_wf in isdecl; eauto.
    now eapply wf_subst_instance_constr. 

  - subst types.
    clear H.
    split.
    + constructor.
      solve_all. destruct a.
      intuition.
    + eapply All_nth_error in X0; eauto. destruct X0 as [s ?]; intuition. 

  - subst types.
    split.
    + constructor.
      solve_all. destruct a.
      intuition.
    + eapply All_nth_error in X0; eauto. destruct X0 as [s ?]; intuition. 
Qed.

Lemma typing_all_wf_decl {cf:checker_flags} Σ (wfΣ : wf Σ.1) Γ (wfΓ : wf_local Σ Γ) :
  Forall wf_decl Γ.
Proof.
  induction wfΓ.
  - constructor.
  - constructor; auto. red. simpl. split; wf.
    destruct t0 as [u t0].
    apply typing_wf_gen in t0; eauto. apply t0; auto.
  - constructor; auto. red; simpl. apply typing_wf_gen in t1; auto.
    intuition auto.
Qed.
#[global]
Hint Resolve typing_all_wf_decl : wf.

Lemma on_global_env_impl `{checker_flags} Σ P Q :
  (forall Σ Γ t T, on_global_env P Σ.1 -> P Σ Γ t T -> Q Σ Γ t T) ->
  on_global_env P Σ -> on_global_env Q Σ.
Proof.
  intros X X0.
  simpl in *. induction X0; constructor; auto.
  clear IHX0. destruct d; simpl.
  - destruct c; simpl. destruct cst_body; simpl in *.
    red in o |- *. simpl in *. now eapply X.
    red in o |- *. simpl in *. now eapply X.
  - simpl in *.
    destruct o0 as [onI onP onNP].
    constructor; auto.
    -- eapply Alli_impl. exact onI. eauto. intros.
       refine {| ind_indices := X1.(ind_indices);
                 ind_arity_eq := X1.(ind_arity_eq);
                 ind_cshapes := X1.(ind_cshapes) |}.
       --- apply onArity in X1. unfold on_type in *; simpl in *.
           now eapply X.
       --- pose proof X1.(onConstructors) as X11. red in X11.
           eapply All2_impl; eauto.
           simpl. intros. destruct X2 as [? ? ? ?]; unshelve econstructor; eauto.
           * apply X; eauto.
           * clear -X0 X on_cargs. revert on_cargs.
              generalize (cshape_args y), (cshape_sorts y).
              induction c; destruct l; simpl; auto;
              destruct a as [na [b|] ty]; simpl in *; auto;
           split; intuition eauto.
           * clear -X0 X on_cindices.
             revert on_cindices.
             generalize (List.rev  (lift_context #|cshape_args y| 0 (ind_indices X1))).
             generalize (cshape_indices y).
             induction 1; simpl; constructor; auto.
       --- simpl; intros. apply (onProjections X1 H0).
       --- destruct X1. simpl. unfold check_ind_sorts in *.
           destruct Universe.is_prop; auto.
           destruct Universe.is_sprop; auto.
           split. apply ind_sorts. destruct indices_matter; auto.
           eapply type_local_ctx_impl. eapply ind_sorts. auto.
       --- apply (onIndices X1).
    -- red in onP. red.
       eapply All_local_env_impl. eauto.
       intros. now apply X.
Qed.

Lemma typing_wf_sigma {cf:checker_flags} Σ (wfΣ : wf Σ) :
  on_global_env (fun _ => wf_decl_pred) Σ.
Proof.
  intros.
  pose proof (env_prop_sigma _ typing_wf_gen _ wfΣ). red in X.
  unfold lift_typing in X. do 2 red in wfΣ.
  eapply on_global_env_impl; eauto; simpl; intros.
  destruct T. red. apply X1. red. destruct X1 as [x [a wfs]]. split; auto.
Qed.

Lemma typing_wf {cf:checker_flags} Σ (wfΣ : wf Σ.1) Γ t T :
  Σ ;;; Γ |- t : T -> Ast.wf t /\ Ast.wf T.
Proof.
  intros. eapply typing_wf_gen in X; intuition eauto with wf.
Qed.

Lemma wf_instantiate_params_subst_term :
  forall params args s t ctx t',
    Ast.wf t ->
    instantiate_params_subst params args s t = Some (ctx, t') ->
    Ast.wf t'.
Proof.
  intros params args s t ctx t' h e.
  revert args s t ctx t' h e.
  induction params ; intros args s t ctx t' h e.
  - destruct args ; try discriminate. cbn in e. inversion e.
    subst. assumption.
  - destruct a as [na [bo|] ty].
    + cbn in e. destruct t ; try discriminate.
      eapply IHparams ; try exact e.
      invs h. assumption.
    + cbn in e. destruct t ; try discriminate.
      destruct args ; try discriminate.
      eapply IHparams ; try exact e.
      invs h. assumption.
Qed.

Lemma wf_instantiate_params_subst_ctx :
  forall params args s t ctx t',
    Forall Ast.wf args ->
    Forall wf_decl params ->
    Forall Ast.wf s ->
    instantiate_params_subst params args s t = Some (ctx, t') ->
    Forall Ast.wf ctx.
Proof.
  intros params args s t ctx t' ha hp hx e.
  revert args s t ctx t' ha hp hx e.
  induction params ; intros args s t ctx t' ha hp hx e.
  - destruct args ; try discriminate. cbn in e. inversion e.
    subst. assumption.
  - destruct a as [na [bo|] ty].
    + cbn in e. destruct t ; try discriminate.
      invs hp. destruct H1 as [h1 h2]. simpl in h1, h2.
      eapply IHparams ; try exact e ; try assumption.
      constructor ; try assumption.
      eapply wf_subst ; assumption.
    + cbn in e. destruct t ; try discriminate.
      destruct args ; try discriminate.
      invs hp. simpl in *.
      invs ha.
      eapply IHparams ; try exact e ; try assumption.
      constructor ; assumption.
Qed.

Lemma wf_instantiate_params :
  forall params args t t',
    Forall wf_decl params ->
    Forall Ast.wf args ->
    Ast.wf t ->
    instantiate_params params args t = Some t' ->
    Ast.wf t'.
Proof.
  intros params args t t' hparamas hargs ht e.
  unfold instantiate_params in e. revert e.
  case_eq (instantiate_params_subst (List.rev params) args [] t) ; try discriminate.
  intros [ctx u] eq e. inversion e. subst. clear e.
  apply wf_instantiate_params_subst_term in eq as h1 ; trivial.
  apply wf_instantiate_params_subst_ctx in eq as h2 ; trivial.
  - eapply wf_subst ; trivial.
  - eapply rev_Forall. assumption.
Qed.

Record wf_inductive_body idecl := {
  wf_ind_type : Ast.wf (ind_type idecl);
  wf_ind_ctors : Forall (fun cdecl => Ast.wf (cdecl_type cdecl)) (ind_ctors idecl);
  wf_ind_projs : Forall (fun pdecl => Ast.wf pdecl.2) (ind_projs idecl)
}.

Lemma declared_minductive_declared {cf:checker_flags} {Σ : global_env_ext} {mind} {mdecl} :
  wf Σ.1 ->  
  declared_minductive Σ mind mdecl ->
  (Alli (fun i decl => declared_inductive Σ mdecl {| inductive_mind := mind; inductive_ind := i |} decl)
    0 (ind_bodies mdecl)).
Proof.
 intros; eapply forall_nth_error_Alli. intros; split; auto.
Qed.

Lemma declared_inductive_declared {cf:checker_flags} {Σ : global_env_ext}
  {ind mdecl idecl} :
  wf Σ.1 ->  
  declared_inductive Σ mdecl ind idecl ->
  (Alli (fun i decl => declared_constructor Σ mdecl idecl (ind, i) decl) 0 (ind_ctors idecl)) *
  (Alli (fun i decl => declared_projection Σ mdecl idecl ((ind, ind_npars mdecl), i) decl) 0 (ind_projs idecl)).
Proof.
 intros; split; eapply forall_nth_error_Alli; intros; split; auto.
Qed.

Lemma declared_minductive_wf {cf:checker_flags} {Σ : global_env_ext} {mind mdecl} :
  wf Σ.1 ->  
  declared_minductive Σ mind mdecl ->
  Forall wf_decl (ind_params mdecl) /\
  Forall wf_inductive_body (ind_bodies mdecl).
Proof.  
  intros wfΣ declm.
  pose proof (typing_wf_gen _ wfΣ _ localenv_nil _ _ (type_Prop _)) as [X _].
  split. eapply lookup_on_global_env in declm as [? [? ?]]; eauto.
  red in o.
  now apply (on_inductive_wf_params (ind:={|inductive_mind := mind; inductive_ind := 0|})) in o.
  eapply All_Forall.
  move: (declared_minductive_declared wfΣ declm) => decli.
  eapply Alli_All; eauto.
  intros i oib H. simpl in H.
  destruct (declared_inductive_declared wfΣ H) as [declc declp].
  split.
  now eapply declared_inductive_wf in H.
  eapply All_Forall, Alli_All; eauto. simpl; intros.
  eapply declared_constructor_wf in H0; eauto. exact [].
  eapply All_Forall, Alli_All; eauto. simpl; intros.
  eapply declared_projection_wf in H0; eauto.
Qed.

Lemma mkApp_ex_wf t u : Ast.wf (mkApp t u) ->
  exists f args, mkApp t u = tApp f args /\ ~~ isApp f.
Proof.
  induction t; simpl; try solve [eexists _, _; split; reflexivity].
  intros wf.
  eapply wf_inv in wf as [appt [_ [wft wfargs]]].
  eapply Forall_app in wfargs as [wfargs wfu]. depelim wfu.
  forward IHt. eapply wf_mkApp; intuition auto.
  destruct IHt as [f [ar [eqf isap]]].
  eexists _, _; split; auto. rewrite appt //.
Qed.

Lemma decompose_app_mkApp f u : 
  (decompose_app (mkApp f u)).2 <> [].
Proof.
  induction f; simpl; auto; try congruence.
  destruct args; simpl; congruence.
Qed.

Lemma mkApps_tApp' f u f' u' :
  ~~ isApp f' -> 
  mkApp f u = tApp f' u' -> mkApps f [u] = mkApps f' u'.
Proof.
  intros.
  rewrite -(mkApp_mkApps f u []).
  simpl. rewrite H0.
  rewrite -(mkApps_tApp f') // ?H //.
  destruct u' => //.
  eapply (f_equal decompose_app) in H0.
  simpl in H0. pose proof (decompose_app_mkApp f u).
  rewrite H0 /= in H1. congruence.
Qed.

Lemma eq_decompose_app x y :
  Ast.wf x -> Ast.wf y ->
  decompose_app x = decompose_app y -> x = y.
Proof.
  intros wfx; revert y.
  induction wfx using term_wf_forall_list_ind; intros [] wfy; 
  eapply wf_inv in wfy; simpl in wfy; simpl;
   intros [= ?]; try intuition congruence.
Qed.

Lemma mkApp_ex t u : ∑ f args, mkApp t u = tApp f args.
Proof.
  induction t; simpl; try solve [eexists _, _; reflexivity].
Qed.

Lemma strip_casts_decompose_app t : 
  Ast.wf t ->
  forall f l, decompose_app t = (f, l) ->
  strip_casts t = mkApps (strip_casts f) (map strip_casts l).
Proof.
  intros wf.
  induction wf using term_wf_forall_list_ind; simpl; intros; auto; noconf H;
  try noconf H0;
    rewrite ?map_map_compose  ?compose_on_snd ?compose_map_def ?map_length;
      f_equal; solve_all; eauto.

  - now noconf H3.
  - now noconf H3.
Qed.

Lemma mkApps_tApp f args :
  ~~ isApp f ->
  ~~ is_empty args ->
  tApp f args = mkApps f args.
Proof.
  intros.
  destruct args, f; try discriminate; auto.
Qed.

Lemma strip_casts_mkApps_napp_wf f u : 
  ~~ isApp f -> Ast.wf f -> Forall Ast.wf u ->
  strip_casts (mkApps f u) = mkApps (strip_casts f) (map strip_casts u).
Proof.
  intros nisapp wf wf'.
  destruct u.
  simpl. auto.
  rewrite -(mkApps_tApp f (t :: u)) //.
Qed.

Lemma mkApp_mkApps f u : mkApp f u = mkApps f [u].
Proof. reflexivity. Qed.

Lemma decompose_app_inv f l hd args : 
  Ast.wf f ->
  decompose_app (mkApps f l) = (hd, args) ->
  ∑ n, ~~ isApp hd /\ l = skipn n args /\ f = mkApps hd (firstn n args).
Proof.
  destruct (isApp f) eqn:Heq.
  revert l args hd.
  induction f; try discriminate. intros.
  simpl in H.
  move/wf_inv: H => /= [isAppf [Hargs [wff wfargs]]].
  rewrite mkApps_tApp ?isAppf in H0 => //. destruct args => //.
  rewrite mkApps_nested in H0.
  rewrite decompose_app_mkApps ?isAppf in H0; auto. noconf H0.
  exists #|args|; split; auto. now rewrite isAppf.
  rewrite skipn_all_app.
  rewrite firstn_app. rewrite firstn_all2. lia.
  rewrite Nat.sub_diag firstn_O app_nil_r. split; auto.
  rewrite mkApps_tApp ?isAppf //. now destruct args.

  intros wff fl.
  rewrite decompose_app_mkApps in fl; auto. now apply negbT.
  inversion fl. subst; exists 0.
  split; auto. now eapply negbT.
Qed.

Lemma eq_tip_skipn {A} (x : A) n l : [x] = skipn n l -> 
  exists l', l = l' ++ [x] /\ n = #|l'|.
Proof.
  induction l in n |- *. rewrite skipn_nil //.
  destruct n. simpl. destruct l => //.
  intros eq. noconf eq. exists []; split; auto.
  rewrite skipn_S. intros Hx.
  destruct (IHl _ Hx) as [l' [-> ->]].
  exists (a :: l'); split; reflexivity.
Qed.

Lemma strip_casts_mkApp_wf f u : 
  Ast.wf f -> Ast.wf u ->
  strip_casts (mkApp f u) = mkApp (strip_casts f) (strip_casts u).
Proof.
  intros wf wf'.
  assert (wfa : Ast.wf (mkApp f u)). now apply wf_mkApp.
  destruct (mkApp_ex_wf f u wfa) as [f' [args [eq isapp]]].
  eapply (f_equal decompose_app) in eq. simpl in eq.
  epose proof (strip_casts_decompose_app _ wfa _ _ eq).
  rewrite H. 
  rewrite mkApp_mkApps in eq.
  destruct (decompose_app_inv _ _ _ _ wf eq) as [n [ng [stripeq stripf]]].
  apply eq_tip_skipn in stripeq. destruct stripeq as [l' [eqargs eqn]].
  subst n args. rewrite (firstn_app_left _ 0) // /= app_nil_r in stripf. subst f.
  eapply wf_mkApps_napp in wf as [wff' wfl] => //.
  rewrite strip_casts_mkApps_napp_wf //.
  now rewrite mkApp_mkApps mkApps_nested map_app.
Qed.

Lemma strip_casts_mkApps_wf f u : 
  Ast.wf f -> Forall Ast.wf u ->
  strip_casts (mkApps f u) = mkApps (strip_casts f) (map strip_casts u).
Proof.
  intros wf wf'. induction wf' in f, wf |- *.
  simpl. auto.
  rewrite -mkApps_mkApp IHwf'.
  apply wf_mkApp; auto with wf.
  rewrite strip_casts_mkApp_wf //.
  now rewrite mkApps_mkApp.
Qed.
