(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Utf8 String Lia.
From Template Require Import config utils univ BasicAst.
From PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICReduction PCUICWeakening PCUICSubstitution
     PCUICParallelReduction.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Set Asymmetric Patterns.

Notation "'∃' x .. y , P" := (sigT (fun x => .. (sigT (fun y => P%type)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : type_scope.

Existing Instance config.default_checker_flags.

Section Confluence.

  Lemma mkApps_eq_decompose {f args t} :
    mkApps f args = t ->
    isApp f = false ->
    fst (decompose_app t) = f.
  Proof.
    intros H Happ; apply (f_equal decompose_app) in H.
    rewrite decompose_app_mkApps in H. auto. rewrite <- H. reflexivity.
  Qed.

  Ltac finish_discr :=
    match goal with
    | [ H : mkApps _ _ = mkApps _ _ |- _ ] =>
      let H0 := fresh in let H1 := fresh in

      specialize (mkApps_eq_inj H eq_refl eq_refl) as [H0 H1]; try (congruence || (noconf H0; noconf H1))
    | [ H : mkApps _ _ = _ |- _ ] => apply mkApps_eq_head in H
    end.

  Ltac prepare_discr :=
    match goal with
    | [ H : mkApps _ _ = mkApps _ _ |- _ ] => idtac
    | [ H : mkApps ?f ?l = tApp ?y ?r |- _ ] => change (mkApps f l = mkApps y [r]) in H
    | [ H : tApp ?f ?l = mkApps ?y ?r |- _ ] => change (mkApps f [l] = mkApps y r) in H
    | [ H : mkApps ?x ?l = ?y |- _ ] =>
      change (mkApps x l = mkApps y []) in H
    | [ H : ?x = mkApps ?y ?l |- _ ] =>
      change (mkApps x [] = mkApps y l) in H
    end.

  Lemma atom_mkApps {t l} : atom (mkApps t l) -> atom t /\ l = [].
  Proof.
    induction l in t |- *; simpl; auto.
    intros. destruct (IHl _ H). discriminate.
  Qed.

  Lemma pred_atom_mkApps {t l} : pred_atom (mkApps t l) -> pred_atom t /\ l = [].
  Proof.
    induction l in t |- *; simpl; auto.
    intros. destruct (IHl _ H). discriminate.
  Qed.

  Definition application_atom t :=
    match t with
    | tVar _
    | tMeta _
    | tSort _
    | tInd _ _
    | tConstruct _ _ _
    | tLambda _ _ _ => true
    | _ => false
    end.

  Lemma application_atom_mkApps {t l} : application_atom (mkApps t l) -> application_atom t /\ l = [].
  Proof.
    induction l in t |- *; simpl; auto.
    intros. destruct (IHl _ H). discriminate.
  Qed.

  Ltac solve_discr :=
    (try (progress (prepare_discr; finish_discr)));
    (try (match goal with
          | [ H : is_true (application_atom _) |- _ ] => discriminate
          | [ H : is_true (atom _) |- _ ] => discriminate
          | [ H : is_true (atom (mkApps _ _)) |- _ ] => destruct (atom_mkApps H); subst; try discriminate
          | [ H : is_true (pred_atom _) |- _ ] => discriminate
          | [ H : is_true (pred_atom (mkApps _ _)) |- _ ] => destruct (pred_atom_mkApps H); subst; try discriminate
          | [ H : is_true (application_atom (mkApps _ _)) |- _ ] =>
            destruct (application_atom_mkApps H); subst; try discriminate
          end)).

  Lemma pred_mkApps Σ Γ M0 M1 N0 N1 :
    pred1 Σ Γ M0 M1 ->
    All2 (pred1 Σ Γ) N0 N1 ->
    pred1 Σ Γ (mkApps M0 N0) (mkApps M1 N1).
  Proof.
    intros.
    induction X0 in M0, M1, X |- *. auto.
    simpl. eapply IHX0. now eapply pred_app.
  Qed.

  Lemma pred_snd_nth:
    ∀ (Σ : global_context) (Γ : context) (c : nat) (brs1 brs' : list (nat * term)),
      All2
        (on_Trel (pred1 Σ Γ) snd) brs1
        brs'
      → pred1 Σ Γ
              (snd (nth c brs1 (0, tDummy)))
              (snd (nth c brs' (0, tDummy))).
  Proof.
    intros Σ Γ c brs1 brs' brsl.
    induction brsl in c |- *; simpl. apply pred1_refl.
    destruct c; auto.
  Qed.

  Lemma mkApps_eq_decompose_app {t t' l l'} :
    mkApps t l = mkApps t' l' ->
    decompose_app_rec t l = decompose_app_rec t' l'.
  Proof.
    induction l in t, t', l' |- *; simpl.
    - intros ->. rewrite !decompose_app_rec_mkApps.
      now rewrite app_nil_r.
    - intros H. apply (IHl _ _ _ H).
  Qed.

  Lemma pred1_mkApps_tConstruct (Σ : global_context) (Γ : context)
        ind pars k (args : list term) c :
    pred1 Σ Γ (mkApps (tConstruct ind pars k) args) c ->
    {args' : list term & (c = mkApps (tConstruct ind pars k) args') * (All2 (pred1 Σ Γ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    depelim X... exists []. intuition auto.
    intros. rewrite <- mkApps_nested in X.
    depelim X... apply mkApps_eq_decompose_app in x.
    rewrite !decompose_app_rec_mkApps in x. noconf x.
    destruct (IHargs _ X1) as [args' [-> Hargs']].
    exists (args' ++ [N1])%list.
    rewrite <- mkApps_nested. intuition auto.
    eapply All2_app; auto. 
  Qed.

  Lemma pred1_mkApps_refl_tConstruct (Σ : global_context) Γ i k u l l' :
    pred1 Σ Γ (mkApps (tConstruct i k u) l) (mkApps (tConstruct i k u) l') ->
    All2 (pred1 Σ Γ) l l'.
  Proof.
    intros.
    eapply pred1_mkApps_tConstruct in X. destruct X.
    destruct p. now eapply mkApps_eq_inj in e as [_ <-].
  Qed.

  Lemma pred1_mkApps_tFix_inv (Σ : global_context) (Γ : context)
        mfix0 idx (args0 : list term) c :
    pred1 Σ Γ (mkApps (tFix mfix0 idx) args0) c ->
    ({ mfix1 & { args1 : list term &
                         (c = mkApps (tFix mfix1 idx) args1) *
                         All2_prop2_eq Γ (Γ ,,, fix_context mfix0) dtype dbody
                                    (fun x => (dname x, rarg x))
                                    (pred1 Σ) mfix0 mfix1 *
                         (All2 (pred1 Σ Γ) ) args0 args1 } }%type) +
    ({ args1 & { narg & { fn0 & { fn1 &
     ((unfold_fix mfix0 idx = Some (narg, fn0)) *
      (is_constructor narg args1 = true) *
      (All2 (pred1 Σ Γ) args0 args1) *
      (pred1 Σ Γ fn0 fn1) * (c = mkApps fn1 args1)) } } } })%type.
  Proof with solve_discr.
    intros pred. remember (mkApps _ _) as fixt. revert mfix0 idx args0 Heqfixt.
    induction pred; intros; solve_discr.
    - right. exists args1, narg, fn0, fn1. intuition eauto.
    - destruct args0 using rev_ind. noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2. specialize (IHpred1 _ _ _ eq_refl).
      destruct IHpred1 as [[? [? ?]]|[? [? [? [? ?]]]]].
      -- left. eexists _. eexists (_ ++ [N1])%list. rewrite <- mkApps_nested.
         intuition eauto. simpl. subst M1. reflexivity.
         eapply All2_app; eauto.
      -- right. eexists (x ++ [N1])%list, x0, x1, x2. intuition auto.
         clear -b2.
         generalize [N1]. unfold is_constructor in *.
         destruct nth_error eqn:Heq.
         pose proof (nth_error_Some_length Heq).
         intros. rewrite nth_error_app_lt; auto. rewrite Heq; auto.
         intros. discriminate.
         eapply All2_app; eauto.
         now rewrite <- mkApps_nested, b.

    - left.
      eexists mfix1, []. intuition auto.
    - subst t. eapply pred_atom_mkApps in i as [Heq ->].
      left. exists mfix0, []. intuition auto.
      red. generalize (fix_context mfix0).
      induction mfix0; constructor; unfold on_Trel_eq, on_Trel; intuition auto using pred1_refl.
      apply X.
  Qed.

  Lemma pred1_mkApps_tCoFix_inv (Σ : global_context) (Γ : context)
        mfix0 idx (args0 : list term) c :
    pred1 Σ Γ (mkApps (tCoFix mfix0 idx) args0) c ->
    ∃ mfix1 args1,
      (c = mkApps (tCoFix mfix1 idx) args1) *
      All2_prop2_eq Γ (Γ ,,, fix_context mfix0) dtype dbody
                    (fun x => (dname x, rarg x))
                    (pred1 Σ) mfix0 mfix1 *
      (All2 (pred1 Σ Γ) ) args0 args1.
  Proof with solve_discr.
    intros pred. remember (mkApps _ _) as fixt. revert mfix0 idx args0 Heqfixt.
    induction pred; intros; solve_discr.
    - destruct args0 using rev_ind. noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2. specialize (IHpred1 _ _ _ eq_refl).
      destruct IHpred1 as [? [? [[-> ?] ?]]].
      eexists x, (x0 ++ [N1])%list. intuition auto.
      now rewrite <- mkApps_nested.
      eapply All2_app; eauto.
    - exists mfix1, []; intuition (simpl; auto).
    - subst t. eapply pred_atom_mkApps in i as [Heq ->].
      exists mfix0, []. intuition auto.
      red. generalize (fix_context mfix0).
      induction mfix0; constructor; unfold on_Trel_eq, on_Trel; intuition auto using pred1_refl.
      apply X.
  Qed.

  Lemma pred1_mkApps_tCoFix_refl_inv (Σ : global_context) (Γ : context)
        mfix0 mfix1 idx (args0 args1 : list term) :
    pred1 Σ Γ (mkApps (tCoFix mfix0 idx) args0) (mkApps (tCoFix mfix1 idx) args1) ->
      All2_prop2_eq Γ (Γ ,,, fix_context mfix0) dtype dbody
                    (fun x => (dname x, rarg x))
                    (pred1 Σ) mfix0 mfix1 *
      (All2 (pred1 Σ Γ) ) args0 args1.
  Proof with solve_discr.
    intros pred. remember (mkApps _ _) as fixt.
    remember (mkApps _ args1) as fixt'.
    revert mfix0 mfix1 idx args0 args1 Heqfixt Heqfixt'.
    induction pred; intros; symmetry in Heqfixt; solve_discr.
    - destruct args0 using rev_ind. noconf Heqfixt. clear IHargs0.
      rewrite <- mkApps_nested in Heqfixt. noconf Heqfixt.
      clear IHpred2.
      symmetry in Heqfixt'.
      destruct args1 using rev_ind. discriminate. rewrite <- mkApps_nested in Heqfixt'.
      noconf Heqfixt'.
      destruct (IHpred1 _ _ _ _ _ eq_refl eq_refl) as [H H'].
      unfold All2_prop2_eq. split. apply H. apply All2_app; auto.
    - destruct args1 using rev_ind; simpl in *; try discriminate. noconf Heqfixt'.
      unfold All2_prop2_eq. intuition (simpl; auto).
      rewrite <- mkApps_nested in Heqfixt'; noconf Heqfixt'.
    - subst t. eapply pred_atom_mkApps in i as [Heq ->].
      apply mkApps_eq_inj in Heqfixt'; auto.
      destruct Heqfixt' as [[= ->] <-]. intuition auto.
      red. generalize (fix_context mfix1).
      induction mfix1; constructor; unfold on_Trel_eq, on_Trel; intuition auto using pred1_refl.
      apply X.
  Qed.

  Lemma mkApps_eq_decompose_app_rec {f args t l} :
    mkApps f args = t ->
    isApp f = false ->
    match decompose_app_rec t l with
    | (f', args') => f' = f /\ mkApps t l = mkApps f' args'
    end.
  Proof.
    revert f t l.
    induction args using rev_ind; simpl.
    - intros * -> **. rewrite atom_decompose_app; auto.
    - intros. rewrite <- mkApps_nested in H.
      specialize (IHargs f).
      destruct (isApp t) eqn:Heq.
      destruct t; try discriminate.
      simpl in Heq. noconf H. simpl.
      specialize (IHargs (mkApps f args) (x :: l) eq_refl H0).
      destruct decompose_app_rec. intuition.
      subst t.
      simpl in Heq. discriminate.
  Qed.

  Lemma mkApps_eq_decompose' {f args t} :
    mkApps f args = t ->
    isApp f = false ->
    match decompose_app t with
    | (f', args') => f' = f /\ t = mkApps f' args'
    end.
  Proof.
    intros. apply (@mkApps_eq_decompose_app_rec f args t []); auto.
  Qed.

  Ltac apply_hyp :=
    match reverse goal with
    | [ H : forall r, pred1 _ _ ?s _ -> _, H' : pred1 _ _ ?s _, H'' : pred1_ctx _ _ _, H''' : pred1_ctx _ _ _ |- _ ] =>
      let target := fresh "v" in specialize (H _ H' _ _ H''' H'') as [target [? ?]]
    end.

  Hint Constructors pred1 : pcuic.

  Lemma All2_prop_eq_All2 {A B} {Σ Γ} {f : A -> term} {g : A -> B} args0 args1 args3 :
    All2_prop_eq Γ f g
     (λ (Γ : context) (x y : term),
      (pred1 Σ Γ x y *
       (∀ r : term, pred1 Σ Γ x r →
        ∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ y v * pred1 Σ Δ' r v}))%type)
     args0 args1 ->
    All2 (on_Trel_eq (pred1 Σ Γ) f g) args0 args3 ->
    All2 (fun x y =>
        ∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ (f x) v * pred1 Σ Δ' (f y) v * (g x = g y)})%type args1 args3.
  Proof.
    intros HP H. red in HP.
    induction HP in args3, H |- *; depelim H; constructor; eauto.
    unfold on_Trel_eq, on_Trel in *. destruct r as [[pr Hr] Heq].
    destruct r0 as [pr0 eq0]. !intros.
    destruct (Hr _ pr0 _ _ predΔ predΔ'). rewrite <- Heq.
    intuition eauto.
  Qed.

  Lemma All2_prop_All2 {Σ Γ} args0 args1 args3 :
    All2_prop Γ
     (λ (Γ : context) (x y : term),
      (pred1 Σ Γ x y *
       (∀ r : term, pred1 Σ Γ x r →
        ∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ y v * pred1 Σ Δ' r v}))%type)
     args0 args1 ->
    All2 (pred1 Σ Γ) args0 args3 ->
    All2 (fun x y =>
        ∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ x v * pred1 Σ Δ' y v})%type args1 args3.
  Proof.
    intros HP H. red in HP.
    induction HP in args3, H |- *; depelim H; constructor; eauto.
    unfold on_Trel_eq, on_Trel in *.
    !intros.
    destruct r as [r Hr].
    exact (Hr _ p _ _ predΔ predΔ').
  Qed.

  Definition on_Trel2 {A B} (R : A -> A -> Type) (f : B -> A) : B -> A -> Type :=
    fun x y => R (f x) y.

  Lemma All2_join_eq {A B} (f : A -> term) (g : A -> B) (h : term -> B -> A) {Σ Γ x y} :
    ∀ {Δ Δ' : context}, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
    (forall x y, f (h x y) = x) ->
    (forall x y, g (h x y) = y) ->
    All2 (λ x y,
         (∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ (f x) v * pred1 Σ Δ' (f y) v * (g x = g y)}))%type x y ->
    { l : list A & (All2 (on_Trel_eq (pred1 Σ Δ) f g) x l * All2 (on_Trel_eq (pred1 Σ Δ') f g) y l)%type }.
  Proof.
    intros * redΔ redΔ' Hfh Hgh. induction 1. exists []. split; auto.
    destruct (r _ _ redΔ redΔ') as [r' [[rl rr] req]].
    destruct IHX as [IHl [ll lr]].
    exists (h r' (g x) :: IHl). intuition auto. constructor; auto.
    red. intuition auto. red. now rewrite Hfh.
    constructor; auto.
    red. intuition auto. red. now rewrite Hfh.
    rewrite <- req. auto.
  Qed.

  Lemma All2_join {Σ Γ x y} :
    ∀ {Δ Δ' : context}, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
    All2 (λ x y,
         (∀ Δ Δ' : context, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' →
        {v : term & pred1 Σ Δ x v * pred1 Σ Δ' y v}))%type x y ->
    { l : list term & (All2 (pred1 Σ Δ) x l * All2 (pred1 Σ Δ') y l)%type }.
  Proof.
    intros * redΔ redΔ'. induction 1. exists []. split; auto.
    destruct (r _ _ redΔ redΔ') as [r' [rl rr]].
    destruct IHX as [IHl [ll lr]].
    exists (r' :: IHl). intuition auto.
  Qed.

  Lemma All2_on_Trel_eq_impl {A B} Σ Γ {f : A -> term} {g : A -> B} {x y} :
    All2 (on_Trel_eq (pred1 Σ Γ) f g) x y ->
    All2 (on_Trel (pred1 Σ Γ) f) x y.
  Proof.
    induction 1; constructor; intuition auto. red in r. intuition.
  Qed.
  Hint Resolve All2_on_Trel_eq_impl : pcuic.

  Lemma fst_decompose_app_rec t l : fst (decompose_app_rec t l) = fst (decompose_app t).
  Proof.
    induction t in l |- *; simpl; auto. rewrite IHt1.
    unfold decompose_app. simpl. now rewrite (IHt1 [t2]).
  Qed.

  Lemma isConstruct_app_inv t :
    isConstruct_app t = true ->
    ∃ ind k u args, t = mkApps (tConstruct ind k u) args.
  Proof.
    induction t; try discriminate.
    - unfold isConstruct_app. unfold decompose_app. simpl.
      rewrite fst_decompose_app_rec. intros.
      specialize (IHt1 H). destruct IHt1 as [ind [k [u [args ->]]]].
      rewrite decompose_app_mkApps in H; auto. simpl in H.
      exists ind, k, u, (args ++ [t2])%list.
      now rewrite <- mkApps_nested.
    - intros H.
      now exists i, n, u, [].
  Qed.

  Derive NoConfusion for global_decl.

  Hint Resolve pred1_refl : pcuic.

  Lemma All2_nth_error_Some_right {A} {P : A -> A -> Type} {l l'} n t :
    All2 P l l' ->
    nth_error l' n = Some t ->
    { t' : A & (nth_error l n = Some t') * P t' t}%type.
  Proof.
    intros Hall. revert n.
    induction Hall; destruct n; simpl; try congruence. intros [= ->]. exists x. intuition auto.
    eauto.
  Qed.

  Lemma All2_local_env_skipn P l l' n :
    All2_local_env P l l' ->
    All2_local_env P (skipn n l) (skipn n l').
  Proof.
    induction n in l, l' |- *. auto.
    intros.
    destruct l; depelim X.
    - constructor.
    - apply IHn; auto.
    - apply IHn; auto.
  Qed.

  Lemma skipn_nth_error {A} (l : list A) i :
     match nth_error l i with
     | Some a => skipn i l = a :: skipn (S i) l
     | None => skipn i l = []
     end.
  Proof.
    induction l in i |- *. destruct i. reflexivity. reflexivity.
    destruct i. simpl. reflexivity.
    simpl. specialize (IHl i). destruct nth_error.
    rewrite [skipn _ _]IHl. reflexivity.
    rewrite [skipn _ _]IHl. reflexivity.
  Qed.

  Theorem confluence Σ Γ t l r : wf Σ ->
    pred1 Σ Γ t l -> forall (Hr : pred1 Σ Γ t r),
        forall Δ Δ', pred1_ ctx Σ Γ Δ -> pred1_ctx Σ Γ Δ' ->
                  { v & (pred1 Σ Δ l v) * (pred1 Σ Δ' r v) }%type.
  Proof with solve_discr.
    intros wfΣ H; revert Γ t l H r.
    refine (pred1_ind_all Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [eexists; split; constructor; eauto].

  - (* Beta *)
    depelim Hr...
    + clear X1 X. repeat unshelve apply_hyp.
      specialize (forall_r _ Hr1 (Δ ,, vass na t) (Δ' ,, vass na t)) as [b' [lb' rb']].
      constructor; eauto. red. eapply pred1_refl.
      constructor; eauto. red. eapply pred1_refl.
      eexists. intuition eauto using substitution0_pred1.
    + clear X1 X; repeat apply_hyp.
      depelim Hr1...
      specialize (forall_r _ Hr1_2 (Δ ,, vass na M') (Δ' ,, vass na M')) as [b' [lb' rb']].
      constructor. auto with pcuic. simpl. auto.
      constructor. auto. simpl. auto.
      exists (b' {0:=v}). intuition eauto using substitution0_pred1.
      constructor; eauto.

  - (* Zeta *)
    depelim Hr...
    + (* Zeta / Zeta *)
      specialize (forall_r _ Hr1 _ _ predΔ predΔ') as [v [? ?]].
      specialize (forall_r0 _ Hr2 (Δ ,, vdef na d1 t) (Δ' ,, vdef na d3 t)) as [v0 [? ?]].
      constructor; auto with pcuic.
      constructor; auto with pcuic.
      constructor. auto. constructor. auto. apply pred1_refl.
      pose proof (substitution_let_pred1 Σ Δ [vdef na d1 t] [] [d1] [v] b1 v0 wfΣ) as H.
      simpl in H. forward H.
      pose proof (cons_let_def Σ Δ [] [] [] na d1 v t).
      rewrite -> !subst_empty in *.
      forward X0 by constructor.
      apply X0, p.
      pose proof (substitution_let_pred1 Σ Δ' [vdef na d3 t] [] [d3] [v] b3 v0 wfΣ) as H'.
      simpl in H'. forward H'.
      pose proof (cons_let_def Σ Δ' [] [] [] na d3 v t).
      rewrite !subst_empty in X0.
      forward X0 by constructor.
      apply X0, p0.
      eexists. split; eauto.

    + (* Zeta / Congruence *)
      specialize (forall_r _ Hr1 _ _ predΔ predΔ') as [v [? ?]].
      specialize (forall_r0 _ Hr3 (Δ ,, vdef na d1 t) (Δ' ,, vdef na d3 t1)) as [v0 [? ?]].
      1-2:constructor; auto with pcuic; red; intuition eauto with pcuic.
      exists (v0 { 0 := v }).
      intuition eauto using substitution0_let_pred1.
      econstructor; eauto.

  - (* Zeta in context *)
    eapply nth_error_pred1_ctx in X; eauto.
    destruct X as [b [? ?]]; intuition; rename_all_hyps.
    depelim Hr...
    -- (* Zeta in context / Zeta in context *)
      pose proof heq_option_map0.
      eapply nth_error_pred1_ctx_l in H. 2:eapply a.
      destruct H as [body' [Heqbody' Hredbody']].
      rewrite e in Heqbody'. noconf Heqbody'.
      specialize (forall_r _ Hredbody' (skipn (S i) Δ) (skipn (S i) Δ')).
      forward forall_r. now apply All2_local_env_skipn.
      forward forall_r. now apply All2_local_env_skipn.
      destruct forall_r. destruct p.
      exists (lift0 (S i) x).
      split.
      ++ pose proof (weakening_pred1_0 Σ (skipn (S i) Δ) (firstn (S i) Δ) body x wfΣ p).
         unfold app_context in X; rewrite firstn_skipn in X.
         pose proof (All2_local_env_length predΔ).
         destruct (nth_error Γ i) eqn:Heq; noconf heq_option_map0.
         apply nth_error_Some_length in Heq.
         now rewrite firstn_length_le in X.
      ++ pose proof (weakening_pred1_0 Σ (skipn (S i) Δ') (firstn (S i) Δ') body0 x wfΣ p0).
         unfold app_context in X; rewrite firstn_skipn in X.
         pose proof (All2_local_env_length predΔ').
         destruct (nth_error Γ i) eqn:Heq; noconf heq_option_map0.
         apply nth_error_Some_length in Heq.
         now rewrite firstn_length_le in X.

    -- (* Zeta in context / reflexivity *)
      clear heq_option_map.
      specialize (nth_error_pred1_ctx_l i b predΔ') as [body'' [Hb Hred]]; eauto.
      specialize (forall_r _ Hred (skipn (S i) Δ) (skipn (S i) Δ')).
      forward forall_r. now apply All2_local_env_skipn.
      forward forall_r. now apply All2_local_env_skipn.
      destruct forall_r. destruct p.
      exists (lift0 (S i) x).
      assert (S i <= #|Γ|).
      destruct nth_error eqn:Heq; noconf heq_option_map0.
      eapply nth_error_Some_length in Heq. lia.
      pose proof (All2_local_env_length predΔ).
      pose proof (All2_local_env_length predΔ').
      split.
      { eapply weakening_pred1_0 in p; eauto.
        unfold app_context in p. erewrite firstn_skipn in p.
        now rewrite firstn_length_le in p; try lia. }
      { destruct (nth_error Δ' i) eqn:Heq'; noconf Hb.
        destruct c as [na [b'|] ty]; noconf H.
        eapply (pred_rel_def_unfold _ _ _ (skipn (S i) Δ' ,, vdef na x ty ,,, firstn i Δ')).
        rewrite -{1}(firstn_skipn i Δ'). eapply All2_local_env_app_inv.
         move:(skipn_nth_error Δ' i). rewrite Heq' => ->.
         constructor. apply pred1_ctx_refl.
         red. split. apply p0. eapply pred1_refl.
         generalize (firstn i Δ'). intros.
         clear. induction l. constructor.
         destruct a as [na [b|] ty]; constructor; try red; auto using pred1_refl.
         rewrite nth_error_app_ge firstn_length_le; try lia.
         rewrite (minus_diag). reflexivity. }

  - (* Refl *)

  (* Lemma pred1_tRel_inv (Σ : global_context) (Γ : context) i r : *)
  (*   pred1 Σ Γ (tRel i) r -> *)
  (*   (r = tRel i) + *)
  (*   (∃ body body', (option_map decl_body (nth_error Γ i) = Some (Some body)) * *)
  (*            (r = lift0 (S i) body') * *)
  (*            pred1 Σ (skipn (S i) Γ) body body')%type. *)
  (* Proof with solve_discr. *)
  (*   intros pred. *)
  (*   depelim pred... *)
  (*   - right. eapply nth_error_pred1_ctx in a; eauto. destruct a. *)
  (*     exists x, body. intuition eauto. *)
  (*   - left. reflexivity. *)
  (* Qed. *)
  (* eapply pred1_tRel_inv in Hr. destruct Hr. subst. exists (tRel i); split; auto with pcuic. *)

    depelim Hr...
    -- (* Refl , Zeta in context *)
      pose proof e.
      eapply nth_error_pred1_ctx in H. 2:eauto.
      destruct H; intuition.
      specialize (nth_error_pred1_ctx_l i x predΔ) as [body'' [Hb Hred]]; eauto.
      destruct (nth_error_pred1_ctx_l i x X a0). destruct p as [HΓ' [predxx0 IH]].
      pose proof (IH _ Hred (skipn (S i) Δ') (skipn (S i) Δ)).
      forward X0 by now apply All2_local_env_skipn.
      forward X0 by now apply All2_local_env_skipn.
      destruct X0 as [v [vl vr]].
      pose proof (All2_local_env_length predΔ).
      pose proof (All2_local_env_length predΔ').
      assert (S i <= #|Γ|).
      destruct (nth_error Γ _) eqn:Heq; noconf a0.
      eapply nth_error_Some_length in Heq. lia.
      pose proof (IH _ b (skipn (S i) Δ') (skipn (S i) Δ')).
      forward X0 by now apply All2_local_env_skipn.
      forward X0 by now apply All2_local_env_skipn.
      destruct X0 as [v' [vl' vr']].
      exists (lift0 (S i) v').
      split.
      2:{ eapply weakening_pred1_0 in vr'; eauto.
          unfold app_context in vr'. erewrite firstn_skipn in vr'.
          now rewrite firstn_length_le in vr'; try lia. }
      { destruct (nth_error Δ i) eqn:Heq'; noconf Hb.
        destruct c as [na [b'|] ty]; noconf H.
        eapply (pred_rel_def_unfold _ _ _ (skipn (S i) Δ ,, vdef na v' ty ,,, firstn i Γ')).
        rewrite -{1}(firstn_skipn i Δ). eapply All2_local_env_app_inv.
         move:(skipn_nth_error Δ i). rewrite Heq' => ->.
         constructor.  apply pred1_ctx_refl. (* No idea how to relate them *)
         red. split. apply vr. eapply pred1_refl.
         generalize (firstn i Δ). intros.
         clear. induction l. constructor.
         destruct a as [na [b|] ty]; constructor; try red; auto using pred1_refl.
         rewrite nth_error_app_ge firstn_length_le; try lia.
         rewrite (minus_diag). reflexivity. }
      {



      specialize (forall_r _ Hred (skipn (S i) Δ) (skipn (S i) Δ')).

      eapply nth_error_pred1_ctx_l in X. 2:eapply a0.
      destruct X; intuition; rename_all_hyps.
      pose proof heq_option_map0.
      eapply nth_error_pred1_ctx_l in H. 2:eapply predΔ.
      destruct H as [b' [eqn Hpred]].
      pose proof heq_option_map0.
      eapply nth_error_pred1_ctx_l in H. 2:eapply predΔ'.
      destruct H as [b'' [eqn' Hpred']].
      remember (nth_error Δ i) as Hnth.
      destruct Hnth as [[na [b'''|] ty]|]; noconf eqn.
      specialize (forall_r x0 a2).
      specialize (forall_r (skipn (S i) Δ) (skipn (S i) Δ')).
      forward forall_r. now apply All2_local_env_skipn.
      forward forall_r. now apply All2_local_env_skipn.
      destruct forall_r as [v [vl vr]].
      exists (lift0 (S i) v).
      split.
      ++ eapply (pred_rel_def_unfold Σ Δ i (skipn (S i) Δ ,, vdef na v ty ,,, firstn i Δ)).
         rewrite -{1}(firstn_skipn i Δ). eapply All2_local_env_app_inv.
         move:(skipn_nth_error Δ i). rewrite -HeqHnth => ->.
         constructor. apply pred1_ctx_refl.
         red. split. apply vr. eapply pred1_refl.
         generalize (firstn i Δ). intros.
         clear. induction l. constructor.
         destruct a as [na [b|] ty]; constructor; try red; auto using pred1_refl.
         symmetry in HeqHnth. eapply nth_error_Some_length in HeqHnth.
         rewrite nth_error_app_ge firstn_length_le; try lia.
         rewrite (minus_diag). reflexivity.
      ++ epose proof (weakening_pred1_0 Σ _ (firstn (S i) Δ) _ _ _ vr).
         unfold app_context in X. rewrite firstn_skipn firstn_length_le in X; eauto.
         pose proof (All2_local_env_length predΔ').
         pose proof (All2_local_env_length predΔ).
         lia.
         destruct (nth_error Γ i) eqn:Heq; noconf heq_option_map0. simpl in H.
         pose proof (All2_local_env_length predΔ').
         eapply nth_error_Some_length in Heq. lia.
    -- exists (tRel i). intuition auto with pcuic.

  - (* Iota reduction *)
    depelim Hr...
    -- (* Iota / Iota *)
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [l [Hl Hr]]; auto.
      eapply All2_prop_eq_All2 in X0; eauto.
      eapply (All2_join_eq snd fst (fun x y => (y, x)) predΔ predΔ') in X0 as [brs' [brsl brsr]]; eauto.
      exists (iota_red pars c l brs').
      unfold iota_red. simpl.
      split; eapply pred_mkApps; try eapply pred_snd_nth; auto.
      now eapply All2_on_Trel_eq_impl. now apply All2_skipn.
      now eapply All2_on_Trel_eq_impl. now apply All2_skipn.
    -- (* Iota / Congruence *)
       eapply All2_prop_eq_All2 in X0; eauto.
       eapply (All2_join_eq snd fst (fun x y => (y, x)) predΔ predΔ') in X0 as [brs' [brsl brsr]]; auto.
       eapply pred1_mkApps_tConstruct in Hr2 as [args' [-> Hargs']].
       eapply All2_prop_All2 in X; eauto.
       eapply (All2_join predΔ predΔ') in X as [l [Hl Hr]]; auto.
       exists (iota_red pars c l brs').
       unfold iota_red. simpl.
       split. eapply pred_mkApps; eauto using pred_snd_nth, All2_on_Trel_eq_impl.
       now eapply All2_skipn.
       econstructor; eauto.

  - (* Fixpoint unfolding *)
    (* Needs a specialized inversion lemma as fixpoints require spines of arguments. *)
    apply pred1_mkApps_tFix_inv in Hr as [[mfix1 [args2 [[-> Hmfix] Hargs]]]|[mfix1 [fn0' [fn1' [H1 H2]]]]].
    * (* Fix / Congruence *)
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [args' [argsl argsr]]; auto.
      unfold unfold_fix in heq_unfold_fix.
      destruct (nth_error mfix idx) eqn:Heq; try discriminate.
      noconf heq_unfold_fix. red in Hmfix.
      eapply All2_nth_error_Some in Hmfix as [fn' [Hmfn' [Hredty [Hredbody Heqann]]]]; eauto.
      red in Hredbody.
      specialize (forall_r (subst0 (fix_subst mfix1) (dbody fn'))).
      forward forall_r.
      eapply (substitution_let_pred1 Σ Γ (fix_context mfix) [] (fix_subst mfix) (fix_subst mfix1)); eauto.
      (* That proof is somewhere already *) admit.
      specialize (forall_r _ _ predΔ predΔ') as [fn3 [fn1fn3 Hfn3]].
      exists (mkApps fn3 args').
      split. eapply pred_mkApps; eauto.
      econstructor; eauto. unfold unfold_fix. rewrite Hmfn'. reflexivity.
      noconf Heqann. simpl in H. noconf H. rewrite <- H0.
      clear -heq_is_constructor argsl.
      unfold is_constructor in heq_is_constructor.
      destruct nth_error eqn:Heq; try discriminate.
      { eapply All2_nth_error_Some in argsl as [t' [Hred]]; eauto.
        eapply isConstruct_app_inv in heq_is_constructor as [ind [k [u [args ->]]]].
        eapply pred1_mkApps_tConstruct in p as [args'' [-> Hredargs]].
        unfold is_constructor. rewrite Hred. unfold isConstruct_app.
        rewrite decompose_app_mkApps; auto. }

    * (* Fix / Fix *)
      rewrite heq_unfold_fix in H2. intuition. rename_all_hyps.
      subst. noconf heq_Some.
      eapply All2_prop_All2 in X; eauto.
      specialize (forall_r _ b0 _ _ predΔ predΔ') as [fn' [lfn' rfn']].
      eapply (All2_join predΔ predΔ') in X as [args' [argsl argsr]]; auto.
      exists (mkApps fn' args'). split; eapply pred_mkApps; eauto.

  - (* CoFix reduction *)
    depelim Hr...
    + (* CoFix / CoFix *)
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [args [Hl Hr]]; eauto.
      eapply All2_prop_eq_All2 in X4; eauto.
      eapply (All2_join_eq snd fst (fun x y => (y, x)) predΔ predΔ') in X4 as [brs' [brsl brsr]]; auto.
      clear X0 X2. repeat apply_hyp.
      rewrite heq_unfold_cofix in e.
      noconf e. apply_hyp.
      exists (tCase ip v (mkApps v0 args) brs').
      split; econstructor; eauto using pred_mkApps.

    + (* CoFix / Congruence *)
      apply pred1_mkApps_tCoFix_inv in Hr2 as [mfix' [args' [[-> Hmfix]]]].
      eapply All2_prop_eq_All2 in X4; eauto.
      eapply (All2_join_eq snd fst (fun x y => (y, x)) predΔ predΔ') in X4 as [brs' [brsl brsr]]; auto.
      clear X0 X2. repeat apply_hyp.
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [args [Hl Hr]]; eauto.
      red in Hmfix.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix idx) eqn:Heq; try discriminate.
      noconf heq_unfold_cofix.
      eapply All2_nth_error_Some in Hmfix as [fn' [Hmfn' [Hredty [Hredbody Heqann]]]]; eauto.
      injection Heqann. intros.
      red in Hredbody.
      specialize (forall_r (subst0 (cofix_subst mfix') (dbody fn'))).
      forward forall_r.
      eapply (substitution_let_pred1 Σ Γ (fix_context mfix) [] (cofix_subst mfix) (cofix_subst mfix')); eauto.
      admit.
      specialize (forall_r _ _ predΔ predΔ') as [fn3 [fn1fn3 Hfn3]].
      exists (tCase ip v (mkApps fn3 args) brs').
      split. econstructor; eauto using pred_mkApps.
      eapply pred_cofix_case; eauto. unfold unfold_cofix.
      rewrite Hmfn'. reflexivity.

  - (* Proj CoFix *)
    depelim Hr...
    + (* Proj Cofix / Proj Cofix *)
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [args [Hargsl Hargsr]]; eauto.
      clear X0.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix idx) eqn:Heq; try discriminate.
      noconf heq_unfold_cofix. unfold unfold_cofix in e. rewrite Heq in e.
      noconf e. apply_hyp.
      exists (tProj p (mkApps v args)).
      intuition eauto using pred_mkApps, pred_proj_congr.

    + (* Proj CoFix / Congruence *)
      apply pred1_mkApps_tCoFix_inv in Hr as [mfix' [args' [[-> Hmfix]]]].
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [args [Hargsl Hargsr]]; eauto.
      clear X0.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix idx) eqn:Heq; try discriminate.
      noconf heq_unfold_cofix.
      red in Hmfix.
      eapply All2_nth_error_Some in Hmfix as [fn' [Hmfn' [Hredty [Hredbody Heqann]]]]; eauto.
      injection Heqann. intros.
      red in Hredbody.
      specialize (forall_r (subst0 (cofix_subst mfix') (dbody fn'))).
      forward forall_r.
      eapply (substitution_let_pred1 Σ Γ (fix_context mfix) [] (cofix_subst mfix) (cofix_subst mfix')); eauto.
      admit.
      specialize (forall_r _ _ predΔ predΔ') as [fn3 [fn1fn3 Hfn3]].
      exists (tProj p (mkApps fn3 args)).
      intuition eauto using pred_mkApps, pred_proj_congr.
      econstructor. unfold unfold_cofix. rewrite Hmfn'. all:eauto.

  - (* Constant unfolding *)
    depelim Hr...
    + (* Unfolding *)
      unfold declared_constant in *. rewrite H in isdecl. noconf isdecl.
      rewrite heq_cst_body in e. noconf e.
      eexists; intuition eauto using pred1_refl.
    + (* Reflexivity *)
      eexists; intuition eauto with pcuic.

  - (* Constant reflexivity *)
    depelim Hr...
    + (* Unfolding *)
      eexists. split; [|eauto with pcuic]. eauto with pcuic.
    + (* Reflexivity *)
      exists (tConst c u). intuition eauto with pcuic.

  - (* Proj Construct *)
    depelim Hr...
    + (* / Proj Construct red *)
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [args [Hargsl Hargsr]]; eauto.
      eapply All2_nth_error_Some in Hargsl as [arg1' [Harg1' Hredarg1']]; eauto.
      eapply All2_nth_error_Some in Hargsr as [arg2 [Harg2 Hredarg2]]; eauto.
      rewrite Harg1' in Harg2. noconf Harg2.
      exists arg1'; auto.
    + (* / Constructor Congruence *)
      eapply pred1_mkApps_tConstruct in Hr as [args' [-> Hargs']].
      eapply All2_prop_All2 in X; eauto.
      eapply (All2_join predΔ predΔ') in X as [l [Hl Hr]]; auto.
      eapply All2_nth_error_Some in Hl as [arg1' [Harg1' Hredarg1']]; eauto.
      exists arg1'. split; eauto.
      econstructor; eauto.

  - (* Lambda *)
    depelim Hr...
    specialize (forall_r _ Hr1 _ _ predΔ predΔ') as [T' [lT' rT']].
    specialize (forall_r0 _ Hr2 (Δ ,, vass na M') (Δ' ,, vass na M'0)).
    forward forall_r0. constructor; auto.
    forward forall_r0. constructor; auto.
    destruct forall_r0 as [body' [bodyl bodyr]].
    exists (tLambda na T' body'); intuition eauto.
    econstructor. eauto. eauto.
    econstructor. eauto. eauto.

  - (* Application *)
    depelim Hr...
    + (* / Beta *)
      depelim X...
      specialize (forall_r0 _ Hr2 _ _ predΔ predΔ') as [arg' [larg rarg]].
      specialize (forall_r (tLambda na t b1)).
      forward forall_r. auto with pcuic.
      specialize (forall_r _ _ predΔ predΔ') as [body' [bl br]].
      depelim bl...
      depelim br...
      now apply mkApps_eq_decompose in x0.
      exists (N'0 {0 := arg'}). split; eauto with pcuic.
      eapply substitution0_pred1; eauto.

    + (* / Fix *)
      destruct args0 using rev_ind; noconf x.
      rewrite <- mkApps_nested in x. noconf x.
      clear IHargs0.
      destruct args1 using rev_ind. depelim a. destruct args0; discriminate.
      clear IHargs1.
      unfold is_constructor in e0.
      destruct nth_error eqn:Heq; noconf e0.
      pose proof a as a0. eapply All2_nth_error_Some_right in a0 as [a' [Hnth Hred]]; eauto.
      admit.
      (* destruct (eq_dec narg #|args1|). subst narg. *)
      (* assert (x = t) by admit. *)
      (* assert (N0 = a') by admit. *)
      (* subst. *)


      (* eapply pred1_mkApps_tFix_inv in X as [[mfix2 [args1' [[Happ H1] Hredargs]]]|]. *)
      (* subst M1. *)
      (* unfold unfold_fix in e. *)
      (* destruct (nth_error mfix idx) eqn:Heqidx; noconf e. *)
      (* simpl in H. noconf H. *)

      (* pose proof a as a''. apply All2_app_inv in a'' as [Hargs HN0x]; auto. *)
      (* depelim HN0x. *)
      (* specialize (forall_r0 _ p _ _ predΔ predΔ') as [arg' [larg' rarg']]. clear HN0x. *)
      (* rewrite <- mkApps_nested. *)
      (* simpl. *)
      (* eapply All2_nth_error_Some in a as [arg3 [Hfn3 Hred3]]; eauto. *)
      (* rewrite Hfn3 in Heq. injection Heq. intros <-. clear Heq. *)

    + (* App Congruence *)
      clear X X1.
      repeat apply_hyp.
      eexists. split; constructor; eauto.

  - (* LetIn *)
    depelim Hr...
    + specialize (forall_r _ Hr1 _ _ predΔ predΔ') as [d4 [d4l d4r]].
      specialize (forall_r1 _ Hr2 (Δ,, vdef na d1 t1) (Δ',, vdef na d3 t1)).
      forward forall_r1. constructor; simpl; auto using pred1_refl.
      forward forall_r1. constructor; simpl; auto.
      destruct forall_r1 as [body' [lbody rbody]].
      exists (body' {0 := d4}). split. econstructor; eauto.
      eapply substitution0_let_pred1; eauto.

    + specialize (forall_r _ Hr1 _ _ predΔ predΔ') as [d4 [d4l d4r]].
      specialize (forall_r0 _ Hr2 _ _ predΔ predΔ') as [d5 [d5l d5r]].
      specialize (forall_r1 _ Hr3 (Δ,, vdef na d1 t1) (Δ',, vdef na d3 t3)).
      forward forall_r1. constructor; simpl; auto using pred1_refl.
      forward forall_r1. constructor; simpl; auto.
      destruct forall_r1 as [body' [lbody rbody]].
      eexists (tLetIn na d4 d5 body'). split; econstructor; eauto.

  - (* Case *)
    depelim Hr...
    + (* / Iota *)
      eapply All2_prop_eq_All2 in X3; eauto.
      eapply (All2_join_eq snd fst (fun x y => (y, x)) predΔ predΔ') in X3 as [brs' [brsl brsr]]; eauto.
      eapply pred1_mkApps_tConstruct in X1 as [args' [-> redc]].
      specialize (forall_r0 (mkApps (tConstruct ind0 c u) args1)).
      forward forall_r0. eapply pred_mkApps. constructor. constructor. auto.
      specialize (forall_r0 _ _ predΔ predΔ') as [args'' [largs'' rargs'']].
      eapply pred1_mkApps_tConstruct in largs'' as [args2 [-> redc2]].
      exists (iota_red pars c args2 brs').
      split. econstructor. eauto. eauto.
      unfold iota_red. eapply pred_mkApps.
      eauto using pred_snd_nth with pcuic.
      eapply All2_skipn.
      now apply pred1_mkApps_refl_tConstruct in rargs''.

    + (* / Cofix reduction *)
      eapply All2_prop_eq_All2 in X3; eauto.
      eapply (All2_join_eq snd fst (fun x y => (y, x)) predΔ predΔ') in X3 as [brs' [brsl brsr]]; eauto.
      specialize (forall_r _ Hr2 _ _ predΔ predΔ') as [p' [Hp' Hredp']].

      eapply pred1_mkApps_tCoFix_inv in X1 as [mfix' [args0' [[-> Hargs'] Hred']]].
      pose proof (forall_r0 (mkApps (tCoFix mfix' idx) args1)).
      forward X0.
      { eapply pred_mkApps; auto. (* Lemma *) admit. }
      specialize (X0 _ _ predΔ predΔ') as [c' [Hc' Hredc']].

      eapply pred1_mkApps_tCoFix_inv in Hc' as [mfix'' [args0'' [[-> Hargs''] Hred'']]].
      eapply pred1_mkApps_tCoFix_refl_inv in Hredc' as [H10 H10'].

      unfold unfold_cofix in e.
      destruct nth_error eqn:Heq; noconf e.
      red in Hargs', Hargs'', H10.
      eapply All2_nth_error_Some in Hargs' as [? [? [? ?]]]; eauto.
      eexists (tCase ind p' (mkApps (subst0 (cofix_subst mfix'') (dbody x)) args0'') _).
      split.
      econstructor. unfold unfold_cofix. rewrite e. reflexivity. eauto.
      pose (substitution_let_pred1 Σ Δ (fix_context mfix) [] (cofix_subst mfix') (cofix_subst mfix'')
                                   (dbody x) (dbody x) wfΣ).
      forward p. admit. forward p. simpl. eapply pred1_refl.
      destruct o0. simpl in *. apply p. eauto. eauto.

      econstructor; eauto. eapply pred_mkApps.
      (* Stuck. Remove reductions on fns from parallel reduction? *)
      admit.
      eauto.

    + (* Congruence / Congruence *)
      eapply All2_prop_eq_All2 in X3; eauto.
      eapply (All2_join_eq snd fst (fun x y => (y, x)) predΔ predΔ') in X3 as [brs' [brsl brsr]]; eauto.
      clear X X1. repeat apply_hyp.
      exists (tCase ind v v0 brs'). split; intuition eauto with pcuic.

  - (* Proj Congruence *)
    depelim Hr...
    + (* CoFix unfolding *)
      eapply pred1_mkApps_tCoFix_inv in X as [mfix' [args' [[-> Hmfix'] ?]]].
      unfold unfold_cofix in e. destruct (nth_error mfix idx) eqn:Heq.
      noconf e. red in Hmfix'.
      eapply All2_nth_error_Some in Hmfix' as [d' [? [? [? ?]]]]; eauto.
      unfold on_Trel_eq, on_Trel in *.
      (* exists (tProj p (subst0 (cofix_subst mfix') (dbody d'))). *)
      (* split. econstructor. *)
      (* specialize (forall_r (mkApps (tCoFix mfix idx) args1)). *)
      (* forward forall_r. eapply pred_mkApps; auto with pcuic. *)
      (* specialize (forall_r _ _ predΔ predΔ') as [v [vl vr]]. *)
      (* specialize (forall_r (mkApps (tCoFix mfix' idx) args')). *)
      (* forward forall_r. eapply pred_mkApps; auto with pcuic. *)
      (* constructor; eauto with pcuic. *)
      (* specialize (forall_r _ _ predΔ predΔ') as [v [vl vr]]. *)
      pose (substitution_let_pred1 Σ Γ (fix_context mfix) [] (cofix_subst mfix) (cofix_subst mfix')
                                   (dbody d) (dbody d') wfΣ).
      forward p0. admit.
      forward p0. apply o0.
      simpl in p0.
      (* If only we could join thoses two, but we don't have
         an hypothesis for joining the substituted bodies of the
         cofixpoints, only for something which is an application
         of the fixpoint.  *)
      all:admit.

    + (* / Constructor Reduction *)
      eapply pred1_mkApps_tConstruct in X as [args' [-> Hargs']].
      specialize (forall_r (mkApps (tConstruct i k u) args1)).
      forward forall_r. eapply pred_mkApps; eauto with pcuic.
      specialize (forall_r _ _ predΔ predΔ') as [j [jl jr]].
      eapply pred1_mkApps_tConstruct in jl as [args'' [-> Hargs'']].
      eapply pred1_mkApps_tConstruct in jr as [args''' [Heq Hargsj]].
      eapply mkApps_eq_inj in Heq; eauto. destruct Heq. noconf H0.
      eapply All2_nth_error_Some in Hargsj as [t' [heq' ?]]; eauto.
      exists t'. split; eauto with pcuic.

    + (* / Congruence *)
      clear X; apply_hyp.
      exists (tProj p v). intuition auto with pcuic.

  - (* Fix *)
    depelim Hr...
    depelim a.
    + destruct narg; try discriminate.
    + (* Joinable *)
      admit.
      (* eapply (All2_join_eq snd fst (fun x y => (y, x)) _ _ predΔ predΔ') in X0 as [brs' [brsl brsr]]; eauto. *)

  - (* CoFix *)
    depelim Hr...
    revert X a.
    (* same *)
    all:admit.

  - (* Product *)
    depelim Hr...
    specialize (forall_r _ Hr1 _ _ predΔ predΔ') as [M' [Ml Mr]].
    specialize (forall_r0 _ Hr2 (Δ ,, vass na M1) (Δ' ,, vass na M3)).
    forward forall_r0. constructor; auto.
    forward forall_r0. constructor; auto.
    destruct forall_r0 as [b' [bl br]].
    exists (tProd na M' b'); intuition; eauto with pcuic.

  - (* Evar *)
    depelim Hr...
    eapply All2_prop_All2 in X; eauto.
    eapply (All2_join predΔ predΔ') in X as [l'' [leftl'' rightr'']].
    exists (tEvar ev l''); intuition eauto with pcuic.

  - (* Atom *)
    depelim Hr...
    + exists t. split; eapply pred1_refl.
Admitted.

End ParallelSubstitution.