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

Lemma mkApps_eq_decompose {f args t} :
  mkApps f args = t ->
  isApp f = false ->
  fst (decompose_app t) = f.
Proof.
  intros H Happ; apply (f_equal decompose_app) in H.
  rewrite decompose_app_mkApps in H. auto. rewrite <- H. reflexivity.
Qed.

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

Ltac finish_discr :=
  repeat match goal with
         | [ H : ?x = ?x |- _ ] => clear H
         | [ H : mkApps _ _ = mkApps _ _ |- _ ] =>
           let H0 := fresh in let H1 := fresh in
                              specialize (mkApps_eq_inj H eq_refl eq_refl) as [H0 H1];
                              try (congruence || (noconf H0; noconf H1))
         | [ H : atom (mkApps _ _) |- _ ] => apply atom_mkApps in H; intuition subst
         | [ H : pred_atom (mkApps _ _) |- _ ] => apply pred_atom_mkApps in H; intuition subst
         | [ H : mkApps _ _ = _ |- _ ] => apply mkApps_eq_head in H
         end.

Ltac prepare_discr :=
  repeat match goal with
         | [ H : mkApps ?f ?l = tApp ?y ?r |- _ ] => change (mkApps f l = mkApps y [r]) in H
         | [ H : tApp ?f ?l = mkApps ?y ?r |- _ ] => change (mkApps f [l] = mkApps y r) in H
         | [ H : mkApps ?x ?l = ?y |- _ ] =>
           match y with
           | mkApps _ _ => fail 1
           | _ => change (mkApps x l = mkApps y []) in H
           end
         | [ H : ?x = mkApps ?y ?l |- _ ] =>
           match x with
           | mkApps _ _ => fail 1
           | _ => change (mkApps x [] = mkApps y l) in H
           end
         end.

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
  (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
  (try (match goal with
        | [ H : is_true (application_atom _) |- _ ] => discriminate
        | [ H : is_true (atom _) |- _ ] => discriminate
        | [ H : is_true (atom (mkApps _ _)) |- _ ] => destruct (atom_mkApps H); subst; try discriminate
        | [ H : is_true (pred_atom _) |- _ ] => discriminate
        | [ H : is_true (pred_atom (mkApps _ _)) |- _ ] => destruct (pred_atom_mkApps H); subst; try discriminate
        | [ H : is_true (application_atom (mkApps _ _)) |- _ ] =>
          destruct (application_atom_mkApps H); subst; try discriminate
        end)).

Section Confluence.

  Lemma pred_mkApps Σ Γ Δ M0 M1 N0 N1 :
    pred1 Σ Γ Δ M0 M1 ->
    All2 (pred1 Σ Γ Δ) N0 N1 ->
    pred1 Σ Γ Δ (mkApps M0 N0) (mkApps M1 N1).
  Proof.
    intros.
    induction X0 in M0, M1, X |- *. auto.
    simpl. eapply IHX0. now eapply pred_app.
  Qed.

  Lemma pred_snd_nth:
    ∀ (Σ : global_context) (Γ Δ : context) (c : nat) (brs1 brs' : list (nat * term)),
      All2
        (on_Trel (pred1 Σ Γ Δ) snd) brs1
        brs' ->
        pred1_ctx Σ Γ Δ ->
      pred1 Σ Γ Δ
              (snd (nth c brs1 (0, tDummy)))
              (snd (nth c brs' (0, tDummy))).
  Proof.
    intros Σ Γ Δ c brs1 brs' brsl. intros.
    induction brsl in c |- *; simpl. destruct c; now apply pred1_refl_gen.
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

  Lemma pred1_mkApps_tConstruct (Σ : global_context) (Γ Δ : context)
        ind pars k (args : list term) c :
    pred1 Σ Γ Δ (mkApps (tConstruct ind pars k) args) c ->
    {args' : list term & (c = mkApps (tConstruct ind pars k) args') * (All2 (pred1 Σ Γ Δ) args args') }%type.
  Proof with solve_discr.
    revert c. induction args using rev_ind; intros; simpl in *.
    depelim X... exists []. intuition auto.
    intros. rewrite <- mkApps_nested in X.
    depelim X... prepare_discr. apply mkApps_eq_decompose_app in x.
    rewrite !decompose_app_rec_mkApps in x. noconf x.
    destruct (IHargs _ X1) as [args' [-> Hargs']].
    exists (args' ++ [N1])%list.
    rewrite <- mkApps_nested. intuition auto.
    eapply All2_app; auto. 
  Qed.

  Lemma pred1_mkApps_refl_tConstruct (Σ : global_context) Γ Δ i k u l l' :
    pred1 Σ Γ Δ (mkApps (tConstruct i k u) l) (mkApps (tConstruct i k u) l') ->
    All2 (pred1 Σ Γ Δ) l l'.
  Proof.
    intros.
    eapply pred1_mkApps_tConstruct in X. destruct X.
    destruct p. now eapply mkApps_eq_inj in e as [_ <-].
  Qed.

  Lemma pred1_mkApps_tFix_inv (Σ : global_context) (Γ Δ : context)
        mfix0 idx (args0 : list term) c :
    pred1 Σ Γ Δ (mkApps (tFix mfix0 idx) args0) c ->
    ({ mfix1 & { args1 : list term &
                         (c = mkApps (tFix mfix1 idx) args1) *
                         All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1)
                                       dtype dbody
                                    (fun x => (dname x, rarg x))
                                    (pred1 Σ) mfix0 mfix1 *
                         (All2 (pred1 Σ Γ Δ) ) args0 args1 } }%type) +
    ({ args1 & { narg & { fn0 & { fn1 &
     ((unfold_fix mfix0 idx = Some (narg, fn0)) *
      (is_constructor narg args1 = true) *
      (All2 (pred1 Σ Γ Δ) args0 args1) *
      (pred1 Σ Γ Δ fn0 fn1) * (c = mkApps fn1 args1)) } } } })%type.

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
    - subst t. solve_discr.
  Qed.

  Lemma pred1_mkApps_tCoFix_inv (Σ : global_context) (Γ Δ : context)
        mfix0 idx (args0 : list term) c :
    pred1 Σ Γ Δ (mkApps (tCoFix mfix0 idx) args0) c ->
    ∃ mfix1 args1,
      (c = mkApps (tCoFix mfix1 idx) args1) *
      All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1) dtype dbody
                    (fun x => (dname x, rarg x))
                    (pred1 Σ) mfix0 mfix1 *
      (All2 (pred1 Σ Γ Δ) ) args0 args1.
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
    - subst t; solve_discr.
  Qed.

  Lemma pred1_mkApps_tCoFix_refl_inv (Σ : global_context) (Γ Δ : context)
        mfix0 mfix1 idx (args0 args1 : list term) :
    pred1 Σ Γ Δ (mkApps (tCoFix mfix0 idx) args0) (mkApps (tCoFix mfix1 idx) args1) ->
      All2_prop2_eq Γ Δ (Γ ,,, fix_context mfix0) (Δ ,,, fix_context mfix1) dtype dbody
                    (fun x => (dname x, rarg x))
                    (pred1 Σ) mfix0 mfix1 *
      (All2 (pred1 Σ Γ Δ)) args0 args1.
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
    - repeat finish_discr.
      unfold All2_prop2_eq. intuition (simpl; auto).
    - subst t; solve_discr.
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

  Hint Constructors pred1 : pcuic.

  Lemma All2_prop_eq_All2 {A B} {Σ Γ Δ} {f : A -> term} {g : A -> B} args0 args1 args3 :
    All2_prop_eq Γ Δ f g
     (λ (Γ Δ : context) (x y : term),
      (pred1 Σ Γ Δ x y *
       (∀ Δ' r, pred1 Σ Γ Δ' x r →
        ∃ Δ'' v, pred1 Σ Δ Δ'' y v * pred1 Σ Δ' Δ'' r v))%type)
     args0 args1 ->
    All2 (on_Trel_eq (pred1 Σ Γ Δ) f g) args0 args3 ->
    All2 (fun x y =>
            (∃ Δ'' v, (pred1 Σ Δ Δ'' (f x) v * pred1 Σ Δ Δ'' (f y) v)) * (g x = g y))%type args1 args3.
  Proof.
    intros HP H. red in HP.
    induction HP in args3, H |- *; depelim H; constructor; eauto.
    unfold on_Trel_eq, on_Trel in *. destruct r as [[pr Hr] Heq].
    destruct r0 as [pr0 eq0]. !intros.
    destruct (Hr _ _ pr0). split. exists x0. destruct s. exists x1. intuition auto.
    now rewrite <- Heq.
  Qed.

  Lemma All2_prop_All2 {Σ Γ Δ} args0 args1 args3 :
    All2_prop Γ
     (λ (Γ : context) (x y : term),
      (pred1 Σ Γ Δ x y *
       (∀ Δ' r, pred1 Σ Γ Δ' x r →
        ∃ Δ'' v, pred1 Σ Δ Δ'' y v * pred1 Σ Δ' Δ'' r v))%type)
     args0 args1 ->
    All2 (pred1 Σ Γ Δ) args0 args3 ->
    All2 (fun x y =>
        ∃ Δ'' v, pred1 Σ Δ Δ'' x v * pred1 Σ Δ Δ'' y v)%type args1 args3.
  Proof.
    intros HP H. red in HP.
    induction HP in args3, H |- *; depelim H; constructor; eauto.
    unfold on_Trel_eq, on_Trel in *.
    !intros.
    destruct r as [r Hr].
    exact (Hr _ _ p).
  Qed.

  Definition on_Trel2 {A B} (R : A -> A -> Type) (f : B -> A) : B -> A -> Type :=
    fun x y => R (f x) y.

  Lemma All2_on_Trel_eq_impl {A B} Σ Γ Δ {f : A -> term} {g : A -> B} {x y} :
    All2 (on_Trel_eq (pred1 Σ Γ Δ) f g) x y ->
    All2 (on_Trel (pred1 Σ Γ Δ) f) x y.
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

  Equations construct_cofix_discr (t : term) : bool :=
    construct_cofix_discr (tConstruct _ _ _) => true;
    construct_cofix_discr (tCoFix _ _) => true;
    construct_cofix_discr _ => false.
  Transparent construct_cofix_discr.

  Equations discr_construct_cofix (t : term) : Prop :=
    { | tConstruct _ _ _ => False;
      | tCoFix _ _ => False;
      | _ => True }.
  Transparent discr_construct_cofix.

  Inductive construct_cofix_view : term -> Set :=
  | construct_cofix_construct c u i : construct_cofix_view (tConstruct c u i)
  | construct_cofix_cofix mfix idx : construct_cofix_view (tCoFix mfix idx)
  | construct_cofix_other t : discr_construct_cofix t -> construct_cofix_view t.

  Equations view_construct_cofix (t : term) : construct_cofix_view t :=
    { | tConstruct ind u i => construct_cofix_construct ind u i;
      | tCoFix mfix idx => construct_cofix_cofix mfix idx;
      | t => construct_cofix_other t I }.

  Lemma decompose_app_rec_inv {t l' f l} :
    decompose_app_rec t l' = (f, l) ->
    mkApps t l' = mkApps f l.
  Proof.
    induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
    simpl. apply/IHt1.
  Qed.

  Lemma decompose_app_inv {t f l} :
    decompose_app t = (f, l) -> t = mkApps f l.
  Proof. by apply/decompose_app_rec_inv. Qed.

  Lemma eq_ind_spec i i' : reflect (i = i') (AstUtils.eq_ind i i').
  Proof.
    unfold AstUtils.eq_ind.
    destruct i, i'. simpl.
  Admitted.
  (* Lemma All2_join_eq {A B} (f : A -> term) (g : A -> B) (h : term -> B -> A) {Σ Γ x y} : *)
  (*   ∀ {Δ Δ' : context}, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' → *)
  (*   (forall x y, f (h x y) = x) -> *)
  (*   (forall x y, g (h x y) = y) -> *)
  (*   All2 (fun x y => *)
  (*           (∃ Δ'' v, (pred1 Σ Δ Δ'' (f x) v * pred1 Σ Δ Δ'' (f y) v)) * (g x = g y))%type x y -> *)
  (*   { l : list A & (All2 (on_Trel_eq (pred1 Σ Δ (map f l)) f g) x l * All2 (on_Trel_eq (pred1 Σ Δ') f g) y l)%type }. *)
  (* Proof. *)
  (*   intros * redΔ redΔ' Hfh Hgh. induction 1. exists []. split; auto. *)
  (*   destruct (r _ _ redΔ redΔ') as [r' [[rl rr] req]]. *)
  (*   destruct IHX as [IHl [ll lr]]. *)
  (*   exists (h r' (g x) :: IHl). intuition auto. constructor; auto. *)
  (*   red. intuition auto. red. now rewrite Hfh. *)
  (*   constructor; auto. *)
  (*   red. intuition auto. red. now rewrite Hfh. *)
  (*   rewrite <- req. auto. *)
  (* Qed. *)

  (* Lemma All2_join {Σ Γ Δ x y} : *)
  (*   ∀ {Δ Δ' : context}, pred1_ctx Σ Γ Δ → pred1_ctx Σ Γ Δ' → *)
  (*   All2 (λ x y, *)
  (*         forall Δ'', pred1_ctx Σ Δ Δ'' -> *)
  (*                     ∃ R, pred1_ctx Σ Δ' R * pred1_ctx Σ Δ'' R). *)
  (*       {v : term & pred1 Σ Δ x v * pred1 Σ Δ' y v}))%type x y -> *)
  (*   { l : list term & (All2 (pred1 Σ Δ) x l * All2 (pred1 Σ Δ') y l)%type }. *)
  (* Proof. *)
  (*   intros * redΔ redΔ'. induction 1. exists []. split; auto. *)
  (*   destruct (r _ _ redΔ redΔ') as [r' [rl rr]]. *)
  (*   destruct IHX as [IHl [ll lr]]. *)
  (*   exists (r' :: IHl). intuition auto. *)
  (* Qed. *)
  Lemma lookup_env_cst_inv {Σ c k cst} :
    lookup_env Σ c = Some (ConstantDecl k cst) -> c = k.
  Proof.
    induction Σ. simpl. discriminate.
    simpl. destruct AstUtils.ident_eq eqn:Heq. intros [= ->]. simpl in Heq.
    now destruct (AstUtils.ident_eq_spec c k). auto.
  Qed.

  Section TriangleFn.
    Context (Σ : global_context).

    Section TriangleFix.
      Context (rho : context -> term -> term).
      Context (Γ : context).

      Fixpoint fold_fix_context acc m :=
        match m with
        | [] => acc
        | def :: fixd =>
          fold_fix_context (vass def.(dname) (lift0 #|acc| (rho Γ def.(dtype))) :: acc) fixd
        end.
    End TriangleFix.

    Definition map_fix (rho : context -> term -> term) Γ mfixctx (mfix : mfixpoint term) :=
      (map (map_def (rho Γ) (rho (Γ ,,, mfixctx))) mfix).

    Fixpoint rho Γ t : term :=
    match t with
    | tApp (tLambda na T b) u => (rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ u}
    | tLetIn na d t b => (subst10 (rho Γ d) (rho (vdef na (rho Γ d) (rho Γ t) :: Γ) b))
    | tRel i =>
      match option_map decl_body (nth_error Γ i) with
      | Some (Some body) => (lift0 (S i) body)
      | Some None => tRel i
      | None => tRel i
      end
    | tCase (ind, pars) p x brs =>
      let p' := rho Γ p in
      let x' := rho Γ x in
      let brs' := List.map (fun x => (fst x, rho Γ (snd x))) brs in
      match decompose_app x, decompose_app x' with
      | (tConstruct ind' c u, args), (tConstruct ind'' c' u', args') =>
        if AstUtils.eq_ind ind ind' then
          iota_red pars c args' brs'
        else tCase (ind, pars) p' x' brs'
      | (tCoFix mfix idx, args), (tCoFix mfix' idx', args') =>
        match unfold_cofix mfix' idx with
        | Some (narg, fn) =>
          tCase (ind, pars) p' (mkApps fn args') brs'
        | None => tCase (ind, pars) p' (mkApps (tCoFix mfix' idx) args') brs'
        end
      | _, _ => tCase (ind, pars) p' x' brs'
      end
    | tProj ((i, pars, narg) as p) x =>
      let x' := rho Γ x in
      match decompose_app x, decompose_app x' with
      | (tConstruct ind c u, args), (tConstruct ind' c' u', args') =>
        match nth_error args' (pars + narg) with
        | Some arg1 =>
          if AstUtils.eq_ind i ind' then arg1
          else tProj p x'
        | None => tProj p x'
        end
      | (tCoFix mfix idx, args), (tCoFix mfix' idx', args') =>
        match unfold_cofix mfix' idx with
        | Some (narg, fn) => tProj p (mkApps fn args')
        | None => tProj p (mkApps (tCoFix mfix' idx') args')
        end
      | _, _ => tProj p x'
      end
        (* missing Fix + CoFix *)
    | tConst c u =>
      match lookup_env Σ c with
      | Some (ConstantDecl id decl) =>
        match decl.(cst_body) with
        | Some body => subst_instance_constr u body
        | None => tConst c u
        end
      | _ => tConst c u
      end
    | tApp t u => tApp (rho Γ t) (rho Γ u)
    | tLambda na t u => tLambda na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u)
    | tProd na t u => tProd na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u)
    | tVar i => tVar i
    | tEvar n l => tEvar n (map (rho Γ) l)
    | tMeta n => tMeta n
    | tSort s => tSort s
    | tFix mfix idx =>
      let mfixctx := fold_fix_context rho Γ [] mfix in
      tFix (map_fix rho Γ mfixctx mfix) idx
    | tCoFix mfix idx =>
      let mfixctx := fold_fix_context rho Γ [] mfix in
      tCoFix (map_fix rho Γ mfixctx mfix) idx
    | tInd _ _ | tConstruct _ _ _ => t
    end.

    Lemma rho_mkApps {Γ f l} : isLambda f = false ->
                               rho Γ (mkApps f l) = mkApps (rho Γ f) (map (rho Γ) l).
    Proof.
      induction l in f |- *; auto. simpl. rewrite IHl. simpl. reflexivity.
      intros. destruct f; simpl in *; congruence.
    Qed.

    Section rho_ctx.
      Context (Δ : context).
      Fixpoint rho_ctx_over Γ :=
        match Γ with
        | [] => []
        | {| decl_name := na; decl_body := None; decl_type := T |} :: Γ =>
          let Γ' := rho_ctx_over Γ in
          vass na (rho (Δ ,,, Γ') T) :: Γ'
        | {| decl_name := na; decl_body := Some b; decl_type := T |} :: Γ =>
          let Γ' := rho_ctx_over Γ in
          vdef na (rho (Δ ,,, Γ') b) (rho (Δ ,,, Γ') T) :: Γ'
        end.
    End rho_ctx.

    Definition rho_ctx Γ := (rho_ctx_over [] Γ).

    Lemma rho_ctx_over_length Δ Γ : #|rho_ctx_over Δ Γ| = #|Γ|.
    Proof.
      induction Γ; simpl; auto. destruct a. destruct decl_body; simpl; auto with arith.
    Qed.

    Lemma rho_ctx_over_app Γ' Γ Δ :
      rho_ctx_over Γ' (Γ ,,, Δ) =
      rho_ctx_over Γ' Γ ,,, rho_ctx_over (Γ' ,,, rho_ctx_over Γ' Γ) Δ.
    Proof.
      induction Δ; simpl; auto.
      destruct a as [na [b|] ty]. simpl. f_equal; auto.
      now rewrite IHΔ app_context_assoc.
      now rewrite IHΔ app_context_assoc.
    Qed.

    Lemma rho_ctx_app Γ Δ : rho_ctx (Γ ,,, Δ) = rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) Δ.
    Proof.
      induction Δ; simpl; auto.
      destruct a as [na [b|] ty]. simpl. f_equal.
      rewrite app_context_nil_l. now rewrite IHΔ. auto.
      rewrite app_context_nil_l. now rewrite IHΔ.
    Qed.

    Ltac pcuic := try repeat red; cbn in *;
                  try solve [eauto with pcuic].

    (* Lemma rho_triangle_ctx_ind: *)
    (*   ∀ (Γ : context) (l0 : list term) (l : list (nat * term)), *)
    (*     pred1_ctx Σ Γ (rho_ctx Γ) → *)
    (*     All (λ x : nat * term, pred1_ctx Σ Γ (rho_ctx Γ) → *)
    (*                            pred1 Σ Γ (rho_ctx Γ) (snd x) (rho (rho_ctx Γ) (snd x))) l → *)
    (*     All2 (pred1 Σ Γ (rho_ctx Γ)) l0 (map (rho (rho_ctx Γ)) l0). *)
    (* Proof. *)
    (*   intros Γ l0 l. *)
    (*   intros.  *)
    Lemma rho_triangle_All_All2_ind:
      ∀ (Γ : context) (brs : list (nat * term)),
        pred1_ctx Σ Γ (rho_ctx Γ) →
        All (λ x : nat * term, pred1_ctx Σ Γ (rho_ctx Γ) → pred1 Σ Γ (rho_ctx Γ) (snd x) (rho (rho_ctx Γ) (snd x)))
            brs →
        All2 (on_Trel_eq (pred1 Σ Γ (rho_ctx Γ)) snd fst) brs
             (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs).
    Proof.
      intros. rewrite - {1}(map_id brs). eapply All2_map, All_All2; eauto.
      simpl; intros; auto.
      red. split; auto. red. auto.
    Qed.

    Lemma rho_All_All2_local_env :
      ∀ Γ : context, pred1_ctx Σ Γ (rho_ctx Γ) → ∀ Δ : context,
          All_local_env
            (on_local_decl
               (λ (Γ' : context) (t : term), pred1_ctx Σ (Γ ,,, Γ') (rho_ctx (Γ ,,, Γ'))
                                             → pred1 Σ (Γ ,,, Γ')
                                                     (rho_ctx (Γ ,,, Γ')) t
                                                     (rho (rho_ctx (Γ ,,, Γ')) t))) Δ
          → All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ (rho_ctx Γ))) Δ
                           (rho_ctx_over (rho_ctx Γ) Δ).
    Proof.
      intros.
      induction X0; simpl; constructor; auto.
      red in t0 |- *. red. rewrite rho_ctx_app in t0.
      apply t0. now apply All2_local_env_app_inv.
      red in t0 |- *. rewrite rho_ctx_app in t0.
      intuition red; auto using All2_local_env_app_inv.
    Qed.

    Hint Resolve pred_mkApps : pcuic.

    Lemma rho_lift Γ Δ Γ' t : lift #|Δ| #|Γ'| (rho (Γ ,,, Γ') t) = rho (Γ ,,, Δ ,,, Γ') (lift #|Δ| #|Γ'| t).
    Proof.
      induction t; simpl; auto.
    Admitted.

    Lemma rho_lift0 Γ Δ t : lift0 #|Δ| (rho Γ t) = rho (Γ ,,, Δ) (lift0 #|Δ| t).
    Proof. apply (rho_lift Γ Δ []). Qed.

    Lemma fold_fix_context_over_acc Γ m acc :
      rho_ctx_over (rho_ctx Γ ,,, acc)
                   (List.rev (mapi_rec (λ (i : nat) (d : def term), vass (dname d) ((lift0 i) (dtype d))) m #|acc|))
                   ++ acc =
      fold_fix_context rho (rho_ctx Γ) acc m.
    Proof.
      induction m in Γ, acc |- *; simpl; auto.
      rewrite rho_ctx_over_app. simpl.
      unfold app_context. unfold app_context in IHm.
      erewrite <- IHm.
      rewrite - app_assoc. cbn. f_equal. f_equal.
      f_equal. f_equal.
      rewrite rho_lift0. reflexivity.
      repeat f_equal. rewrite rho_lift0. reflexivity.
    Qed.

    Lemma fold_fix_context_over Γ m :
      rho_ctx_over (rho_ctx Γ) (fix_context m) =
      fold_fix_context rho (rho_ctx Γ) [] m.
    Proof.
      rewrite <- fold_fix_context_over_acc.
      now rewrite app_nil_r.
    Qed.

    Definition fold_fix_context_alt Γ m :=
      mapi (fun k def => vass def.(dname) (lift0 k (rho Γ def.(dtype)))) m.

    (* Lemma fold_fix_context_alt_eq acc Γ m : *)
    (*   fold_fix_context rho Γ acc m = rev_append (fold_fix_context_alt Γ (List.rev m)) acc. *)
    (* Proof. *)
    (*   induction m in Γ, acc |- *; simpl; auto. *)
    (*   unfold fold_fix_context_alt. unfold mapi. simpl. rewrite rev_append_rev. *)
    (*   rewrite IHm. simpl. unfold fold_fix_context_alt. *)
    (*   simpl. unfold mapi. rewrite mapi_rec_app. simpl. *)
    (*   rewrite rev_append_rev. simpl. *)
    (*   rewrite List.rev_app_distr. simpl. *)
    (*   f_equal. *)

    Lemma mapi_ext_size {A B} (f g : nat -> A -> B) l k :
      (forall k' x, k' < k + #|l| -> f k' x = g k' x) ->
      mapi_rec f l k = mapi_rec g l k.
    Proof.
      intros Hl. generalize (le_refl k). generalize k at 1 3 4.
      induction l in k, Hl |- *. simpl. auto.
      intros. simpl in *. erewrite Hl; try lia.
      f_equal. eapply (IHl (S k)); try lia. intros. apply Hl. lia.
    Qed.

    Lemma map_ext_size {A B} (f g : nat -> A -> B) l :
      (forall k x, k < #|l| -> f k x = g k x) ->
      mapi f l = mapi g l.
    Proof.
      intros Hl. unfold mapi. apply mapi_ext_size. simpl. auto.
    Qed.

    Lemma fold_fix_context_rev_mapi {Γ l m} :
      fold_fix_context rho (rho_ctx Γ) l m =
      List.rev (mapi (λ (i : nat) (x : def term),
                      vass (dname x) ((lift0 (#|l| + i)) (rho (rho_ctx Γ) (dtype x)))) m) ++ l.
    Proof.
      unfold mapi.
      rewrite rev_mapi.
      induction m in l |- *. simpl. auto.
      intros. simpl. rewrite mapi_app. simpl.
      rewrite IHm. cbn.
      rewrite - app_assoc. simpl. rewrite List.rev_length.
      rewrite Nat.add_0_r. rewrite minus_diag. simpl.
      f_equal. apply mapi_ext_size. simpl; intros.
      rewrite List.rev_length in H.
      f_equal. f_equal. lia. f_equal. f_equal. f_equal. lia.
    Qed.

    Lemma fix_context_fold Γ m :
      fix_context (map (map_def (rho (rho_ctx Γ))
                                    (rho (rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) (fix_context m)))) m) =
      rho_ctx_over (rho_ctx Γ) (fix_context m).
    Proof.
      unfold fix_context. rewrite mapi_map. simpl.
      rewrite fold_fix_context_over.
      rewrite fold_fix_context_rev_mapi. simpl.
      now rewrite app_nil_r.
    Qed.

    Lemma rho_fix_context_All2_local_env (Γ : context) (m : mfixpoint term) :
      All_local_env
        (on_local_decl
           (λ (Γ' : context) (t : term), pred1_ctx Σ
                                                   (Γ ,,, Γ')
                                                   (rho_ctx (Γ ,,, Γ'))
                                         → pred1 Σ (Γ ,,, Γ')
                                                 (rho_ctx (Γ ,,, Γ')) t
                                                 (rho (rho_ctx (Γ ,,, Γ')) t)))
        (fix_context m)
      → pred1_ctx Σ Γ (rho_ctx Γ)
      → All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ (rho_ctx Γ)))
                       (fix_context m)
                       (fix_context
                          (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] m)
                                   m)).
    Proof.
      intros X X1.
      rewrite - fold_fix_context_over.
      rewrite fix_context_fold.
      revert X. generalize (fix_context m). intros c. induction 1. constructor.
      simpl. constructor. apply IHX. red. red in t0.
      red. rewrite rho_ctx_app in t0. apply t0.
      apply All2_local_env_app_inv; auto.
      simpl.
      constructor. apply IHX.
      red in t0. intuition auto.
      rewrite rho_ctx_app in a, b0. red. split; eauto.
      red. apply a. now apply All2_local_env_app_inv.
      apply b0. now apply All2_local_env_app_inv.
    Qed.

    Lemma All2_prop2_eq_split (Γ Γ' Γ2 Γ2' : context) (A B : Type) (f g : A → term)
          (h : A → B) (rel : context → context → term → term → Type) x y :
      All2_prop2_eq Γ Γ' Γ2 Γ2' f g h rel x y ->
      All2 (on_Trel (rel Γ Γ') f) x y *
      All2 (on_Trel (rel Γ2 Γ2') g) x y *
      All2 (on_Trel eq h) x y.
    Proof.
      induction 1; intuition.
    Qed.

    Lemma rho_triangle (wf : wf Σ) Γ t :
      let Γ' := rho_ctx Γ in
      pred1_ctx Σ Γ Γ' ->
      pred1 Σ Γ Γ' t (rho Γ' t).
    Proof.
      revert Γ t. refine (term_forall_ctx_list_ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
                    simpl; !intros; rename_all_hyps.
      all:eauto 3 with pcuic.

      - destruct (option_map _ _) eqn:Heq.
        destruct o; noconf Heq.
        constructor; auto.
        constructor; auto.
        constructor; auto.

      - econstructor; eauto. rewrite - {1}(map_id l). eapply All2_map.
        eapply All_All2; eauto.

      - econstructor. eauto. unfold snoc.
        rewrite app_context_nil_l in forall_z0.
        apply forall_z0; simpl; eauto. constructor; simpl; intuition eauto.

      - econstructor. eauto. eauto. unfold snoc.
        rewrite app_context_nil_l in forall_z0.
        apply forall_z0; simpl; eauto. constructor; simpl; intuition eauto.

      - eapply pred_zeta; eauto.
        rewrite app_context_nil_l in forall_z1.
        apply forall_z1.
        econstructor; simpl; eauto.

      - destruct t; try constructor; auto.
        cbn in *. specialize (forall_z X1).
        depelim forall_z. solve_discr.
        eapply pred_beta; eauto.

      - destruct lookup_env eqn:Heq; pcuic. destruct g. pose proof (lookup_env_cst_inv Heq). subst k.
        destruct c as [ty [b|] un]; cbn in *;
        econstructor; pcuic. simpl. econstructor; pcuic.

      - destruct p. rename l into brs. red in X1.
        specialize (forall_z X2). specialize (forall_z0 X2).
        apply rho_triangle_All_All2_ind in X1.
        destruct decompose_app eqn:Heq.
        destruct (construct_cofix_discr t1) eqn:Heq'.
        destruct t1; try discriminate.
        -- (* Case Construct *)
          apply decompose_app_inv in Heq.
          subst t0. simpl.
          rewrite rho_mkApps in forall_z0 |- *; auto.
          eapply pred1_mkApps_refl_tConstruct in forall_z0.
          simpl. destruct decompose_app eqn:Heq''.
          rewrite decompose_app_mkApps in Heq''; auto.
          injection Heq'' as <- <-. destruct (eq_ind_spec i i0). subst i0.
          econstructor; auto.
          constructor; pcuic.
        -- (* Case CoFix *)
          apply decompose_app_inv in Heq.
          subst t0. simpl.
          rewrite rho_mkApps in forall_z0 |- *; auto.
          eapply pred1_mkApps_tCoFix_inv in forall_z0 as [mfix1 [idx1 [[? ?] ?]]].
          simpl in e. solve_discr. admit.
        -- destruct t1; try discriminate; constructor; eauto.
        -- auto.

      - (* Projection *)
        destruct s as [[ind pars] arg].
        destruct decompose_app eqn:Heq.
        destruct (construct_cofix_discr t0) eqn:Heq'.
        destruct t0; try discriminate.
        -- (* Proj Construct *)
          apply decompose_app_inv in Heq. subst t.
          rewrite rho_mkApps; auto. rewrite decompose_app_mkApps; auto.
          simpl.
          specialize (forall_z X0).
          rewrite rho_mkApps in forall_z; auto.
          eapply pred1_mkApps_refl_tConstruct in forall_z.
          destruct nth_error eqn:Hnth.
          destruct (eq_ind_spec ind i). subst i.
          eapply pred_proj; pcuic.
          pcuic. pcuic.

        -- (* Proj CoFix *)
          apply decompose_app_inv in Heq. subst t. specialize (forall_z X0).
          rewrite rho_mkApps; auto. rewrite decompose_app_mkApps; auto. simpl.
          rewrite rho_mkApps in forall_z; auto.
          eapply pred1_mkApps_tCoFix_inv in forall_z as [mfix' [l' [[? ?] ?]]]; simpl in e.
          solve_discr.
          unfold unfold_cofix.
          rewrite nth_error_map.
          destruct (nth_error m n) eqn:Hnth; simpl.
          ---
            econstructor. unfold unfold_cofix. rewrite Hnth. reflexivity.
            auto.
            rewrite - fold_fix_context_over in a |- *.
            eapply All2_prop2_eq_split in a. intuition.

            pose (substitution_let_pred1 Σ Γ (fix_context m) [] (rho_ctx Γ)
                                         (rho_ctx_over (rho_ctx Γ) (fix_context m)) []
                                         (cofix_subst m)).
            simpl in p. eapply p; auto. admit. unfold rho_ctx. now rewrite rho_ctx_over_length.
            admit. (* Fix context *)
            admit.

          ---
            eapply pred_proj_congr.
            eapply pred_mkApps. constructor; auto.
            rewrite - fold_fix_context_over.
            rewrite fix_context_fold.
            rewrite - fold_fix_context_over in a.
            rewrite fix_context_fold in a.
            red in a. admit. (* fix context *)
            auto.

        -- (* Proj Congruence *)
          destruct t0; try discriminate; constructor; eauto.

      - econstructor; eauto.
        apply rho_fix_context_All2_local_env; auto.
        red in X0.
        red.
        rewrite -{4}(map_id m).
        eapply All2_map.
        solve_all. red. split; simpl; auto.
        red. simpl.
        forward b. rewrite rho_ctx_app.
        apply All2_local_env_app_inv; auto.
        now apply rho_All_All2_local_env.
        rewrite rho_ctx_app in b.
        rewrite - fold_fix_context_over.
        now rewrite !fix_context_fold.

      - econstructor; eauto.
        apply rho_fix_context_All2_local_env; auto.
        red in X0. red.
        rewrite -{4}(map_id m).
        eapply All2_map.
        solve_all. red. split; simpl; auto.
        red. simpl.
        forward b. rewrite rho_ctx_app.
        apply All2_local_env_app_inv; auto.
        now apply rho_All_All2_local_env.
        rewrite rho_ctx_app in b.
        rewrite - fold_fix_context_over.
        now rewrite !fix_context_fold.
    Admitted.

    Lemma rho_triangle_ctx (wf : wf Σ) Γ :
      pred1_ctx Σ Γ (rho_ctx Γ).
    Proof.
      induction Γ; simpl; try constructor.
      destruct a as [? [?|] ?]; simpl; constructor;
        rewrite ?app_context_nil_l; simpl; eauto using rho_triangle.
    Qed.

    Lemma All2_sym {A} (P : A -> A -> Type) l l' :
      All2 P l l' -> All2 (fun x y => P y x) l' l.
    Proof.
      induction 1; constructor; auto.
    Qed.

    Derive NoConfusion for bool.

    Lemma rho_triangle_All_All2_ind_noeq:
      ∀ (Γ Γ' : context) (brs0 brs1 : list (nat * term)),
        pred1_ctx Σ Γ Γ' →
        All2 (on_Trel_eq (λ x y : term, (pred1 Σ Γ Γ' x y * pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type) snd
                         fst) brs0 brs1 ->
        All2 (on_Trel (pred1 Σ Γ' (rho_ctx Γ)) snd) brs1 (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs0).
    Proof.
      intros. rewrite - {1}(map_id brs1). eapply All2_map, All2_sym, All2_impl; eauto.
      pcuic. unfold on_Trel_eq, on_Trel. intuition.
    Qed.

    Lemma rho_cofix_subst Γ   mfix d  :
      (subst0
         (cofix_subst
            (map (map_def (rho (rho_ctx Γ)) (rho (rho_ctx Γ ,,, fold_fix_context rho (rho_ctx Γ) [] mfix))) mfix)))
        (rho (rho_ctx Γ ,,, fold_fix_context rho (rho_ctx Γ) [] mfix) (dbody d)) =
      (rho (rho_ctx Γ) ((subst0 (cofix_subst mfix)) (dbody d))).
    Proof.
    Admitted.

    Lemma fix_context_map_fix Γ mfix :
      fix_context (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix) =
      rho_ctx_over (rho_ctx Γ) (fix_context mfix).
    Proof.
      rewrite - fix_context_fold.
      unfold map_fix. f_equal.
      f_equal. f_equal. now rewrite fix_context_fold.
    Qed.

    Lemma All2_local_env_pred_fix_ctx (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) :
      All2_local_env
        (on_decl
           (on_decl_over (λ (Γ0 Γ'0 : context) (t t0 : term), pred1 Σ Γ'0 (rho_ctx Γ0) t0 (rho (rho_ctx Γ0) t)) Γ Γ'))
        (fix_context mfix0) (fix_context mfix1)
      → All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ' (rho_ctx Γ))) (fix_context mfix1)
                       (fix_context (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix0)) mfix0)).
    Proof.
      intros.
      rewrite fix_context_map_fix.
      revert X. generalize (fix_context mfix0) (fix_context mfix1).
      induction 1; simpl; constructor; auto.
      unfold on_decl, on_decl_over in p |- *.
      now rewrite rho_ctx_app in p.
      unfold on_decl, on_decl_over in p |- *.
      now rewrite rho_ctx_app in p.
    Qed.

    Lemma All2_map_left {A B} (P : A -> A -> Type) l l' (f : B -> A) :
      All2 (fun x y => P (f x) y) l l' -> All2 P (map f l) l'.
    Proof. intros. rewrite - (map_id l'). eapply All2_map; eauto. Qed.

    Lemma triangle Γ Δ t u : wf Σ ->
                             let Pctx :=
                                 fun (Γ Δ : context) => pred1_ctx Σ Δ (rho_ctx Γ) in
                             pred1 Σ Γ Δ t u -> pred1 Σ Δ (rho_ctx Γ) u (rho (rho_ctx Γ) t).
    Proof with solve_discr.
      intros wfΣ Pctx H. revert Γ Δ t u H.
      (* refine (pred1_ind_all Σ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *. *)
      (* all:try intros **; rename_all_hyps; *)
      (*   try solve [specialize (forall_Γ _ X3); eauto]; eauto; *)
      (*     try solve [eexists; split; constructor; eauto]. *)
      (* intros. *)

      refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); subst Pctx; intros *.
      all:try intros **; rename_all_hyps;
        try solve [specialize (forall_Γ _ X3); eauto]; eauto;
          try solve [simpl; econstructor; simpl; eauto].

      simpl.
      - induction X0; simpl; depelim predΓ'; constructor; rewrite ?app_context_nil_l; eauto.

      - simpl.
        eapply (substitution0_pred1); simpl in *. eauto. eauto.
        rewrite app_context_nil_l in X0.
        eapply X0.
      - simpl.
        eapply (substitution0_let_pred1); simpl in *. eauto. eauto.
        rewrite app_context_nil_l in X4.
        eapply X4.

      - simpl.
        destruct nth_error eqn:Heq.
        pose proof Heq. apply nth_error_Some_length in Heq.
        destruct c as [na [?|] ?]; noconf heq_option_map.
        simpl in X0.
        eapply (f_equal (option_map decl_body)) in H.
        eapply nth_error_pred1_ctx_l in H; eauto.
        destruct H. intuition. rewrite a.
        rewrite -{1}(firstn_skipn (S i) Γ').
        rewrite -{1}(firstn_skipn (S i) (rho_ctx Γ)).
        pose proof (All2_local_env_length X0).
        assert (S i = #|firstn (S i) Γ'|).
        rewrite !firstn_length_le; try lia.
        assert (S i = #|firstn (S i) (rho_ctx Γ)|).
        rewrite !firstn_length_le; try lia.
        rewrite {5}H0 {6}H1.
        eapply weakening_pred1_pred1; eauto.
        eapply All2_local_env_over_firstn_skipn. auto.
        noconf heq_option_map.

      - simpl. simpl in *.
        destruct option_map eqn:Heq.
        destruct o. constructor; auto.
        constructor. auto.
        constructor. auto.

      - simpl in X0. cbn. rewrite decompose_app_mkApps; auto.
        rewrite rho_mkApps // decompose_app_mkApps; auto.
        simpl. destruct (eq_ind_spec ind ind); try discriminate.
        unfold iota_red. eapply pred_mkApps; eauto.
        eapply pred_snd_nth. red in X2.
        now eapply rho_triangle_All_All2_ind_noeq. auto.
        eapply All2_skipn. eapply All2_sym.
        rewrite - {1} (map_id args1). eapply All2_map, All2_impl; eauto. simpl. intuition.
        congruence.

      - admit. (* fix *)
      - simpl. destruct ip.
        rewrite decompose_app_mkApps; auto.
        rewrite rho_mkApps // decompose_app_mkApps; auto.
        simpl. unfold unfold_cofix in heq_unfold_cofix |- *.
        rewrite nth_error_map.
        destruct nth_error eqn:Heq; noconf heq_unfold_cofix. simpl.
        eapply pred_case. eauto. eapply pred_mkApps.
        now rewrite rho_cofix_subst.
        eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. intuition eauto.
        eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. unfold on_Trel_eq, on_Trel in *.
        intuition eauto.

      - simpl.
        destruct p as [[ind pars] arg].
        rewrite decompose_app_mkApps. auto.
        rewrite rho_mkApps // decompose_app_mkApps // /=.
        unfold unfold_cofix in heq_unfold_cofix |- *.
        destruct nth_error eqn:Heq; noconf heq_unfold_cofix.
        unfold map_fix. rewrite nth_error_map Heq /=.
        econstructor. eapply pred_mkApps; eauto.
        now rewrite rho_cofix_subst.
        eapply All2_sym, All2_map_left, All2_impl; eauto; simpl; intuition eauto.

      - simpl. simpl in X0. red in H. rewrite H heq_cst_body. now eapply pred1_refl_gen.

      - simpl in *. destruct (lookup_env Σ c) eqn:Heq; pcuic. destruct g; pcuic.
        destruct cst_body eqn:Heq'; pcuic. econstructor; eauto. red.
        pose proof (lookup_env_cst_inv Heq). subst. eapply Heq.

      - simpl in *. rewrite decompose_app_mkApps; auto.
        rewrite rho_mkApps; auto.
        rewrite decompose_app_mkApps; auto.
        simpl. rewrite nth_error_map.
        eapply All2_nth_error_Some_right in heq_nth_error as [t' [? ?]]; eauto.
        simpl in y. rewrite e. simpl.
        destruct (eq_ind_spec i i) => //.

      - simpl. eapply pred_abs; auto. unfold snoc in *. simpl in X2.
        rewrite app_context_nil_l in X2. apply X2.

      - simpl. destruct M0; (try solve [ constructor; auto ]).
        depelim X. solve_discr. simpl in *.
        depelim X0...
        econstructor; eauto.
        simpl in i. discriminate.

      - simpl. eapply pred_zeta; eauto.
        now simpl in X4; rewrite app_context_nil_l in X4.

      - (* Case reduction *)
        red in X3.
        destruct ind. destruct (decompose_app c0) eqn:Heq. simpl.
        destruct (construct_cofix_discr t) eqn:Heq'; rewrite Heq.
        destruct t; noconf Heq'.
        + (* Iota *)
          apply decompose_app_inv in Heq.
          subst c0. simpl.
          rewrite rho_mkApps; auto.
          rewrite decompose_app_mkApps; auto.
          simpl. rewrite rho_mkApps in X2; auto.
          destruct (eq_ind_spec i i0). subst i0.
          eapply pred1_mkApps_tConstruct in X1 as [args' [? ?]]. subst c1.
          eapply pred1_mkApps_refl_tConstruct in X2.
          econstructor; eauto. pcuic.
          eapply All2_sym, All2_map_left, All2_impl; eauto.
          intros. red in X1. destruct X1. unfold on_Trel_eq, on_Trel in *.
          intuition pcuic.
          econstructor; pcuic.
          eapply All2_sym, All2_map_left, All2_impl; eauto.
          intros. unfold on_Trel_eq, on_Trel in *. intuition pcuic.

        + (* CoFix *)
          apply decompose_app_inv in Heq.
          subst c0. simpl.
          rewrite rho_mkApps; auto.
          rewrite decompose_app_mkApps; auto.
          simpl. rewrite rho_mkApps in X2; auto.
          eapply pred1_mkApps_tCoFix_inv in X1 as [mfix' [idx' [[? ?] ?]]].
          subst c1.
          simpl in X2. eapply pred1_mkApps_tCoFix_refl_inv in X2.
          intuition.
          eapply All2_prop2_eq_split in a1. intuition.
          unfold on_Trel_eq, on_Trel in *.
          unfold unfold_cofix. rewrite nth_error_map.
          destruct nth_error eqn:Heq. simpl.
          * (* CoFix unfolding *)
            eapply All2_nth_error_Some in Heq; eauto. destruct Heq; intuition auto.
            unfold on_Trel_eq, on_Trel in *.
            econstructor; eauto. unfold unfold_cofix.
            rewrite a2. reflexivity.
            rewrite rho_cofix_subst. intuition.
            admit. (* a1 *)
            rewrite - (map_id brs1).
            eapply All2_map, All2_sym, All2_impl; eauto.
            unfold on_Trel_eq, on_Trel in *.
            intros. intuition pcuic.

          * eapply pred_case; eauto.
            eapply pred_mkApps. constructor. pcuic.
            rewrite - fold_fix_context_over.
            rewrite fix_context_map_fix.
            admit. (* Fix contexts reduce *)
            red.
            admit. (* easy recombination *)
            intuition.
            eapply All2_sym, All2_map_left, All2_impl; eauto.
            unfold on_Trel_eq, on_Trel in *.
            intros. intuition pcuic.

        + apply decompose_app_inv in Heq. subst c0.
          assert (All2 (on_Trel_eq (pred1 Σ Γ' (rho_ctx Γ)) snd fst) brs1
                       (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs0)).
          { eapply All2_sym, All2_map_left, All2_impl; eauto.
            unfold on_Trel_eq, on_Trel in *.
            intros. intuition pcuic. }
          destruct t; try discriminate; simpl; pcuic.

      - simpl.
        destruct p as [[ind pars] arg].
        destruct decompose_app eqn:Heq.
        destruct (view_construct_cofix t).
        + apply decompose_app_inv in Heq.
          subst c. simpl.
          rewrite rho_mkApps; auto.
          rewrite decompose_app_mkApps; auto.
          simpl. rewrite rho_mkApps in X0; auto.
          simpl in X0.
          pose proof (pred1_pred1_ctx _ X0).
          eapply pred1_mkApps_tConstruct in X as [args' [? ?]]; subst.
          eapply pred1_mkApps_refl_tConstruct in X0.
          destruct nth_error eqn:Heq.
          destruct (eq_ind_spec ind c0); subst.
          econstructor; eauto.
          eapply pred_proj_congr, pred_mkApps; auto with pcuic. constructor; auto.
          eapply pred_mkApps; auto.
          econstructor; eauto.

        + apply decompose_app_inv in Heq.
          subst c. simpl.
          rewrite rho_mkApps; auto.
          rewrite decompose_app_mkApps; auto.
          simpl. rewrite rho_mkApps in X0; auto. simpl in X0.
          eapply pred1_mkApps_tCoFix_inv in X as [mfix' [idx' [[? ?] ?]]].
          subst c'.
          simpl in a.
          pose proof X0.
          eapply pred1_mkApps_tCoFix_refl_inv in X0.
          intuition.
          unfold unfold_cofix. rewrite nth_error_map.
          destruct nth_error eqn:Heq. simpl.
          * red in a.
            pose proof Heq. eapply All2_nth_error_Some in Heq. 2:eapply a.
            destruct Heq. intuition. red in a3, b1. intuition.
            econstructor.
            unfold unfold_cofix. rewrite a2. reflexivity. auto.
            rewrite rho_cofix_subst. red in a4.
            eapply pred1_mkApps_tCoFix_refl_inv in X.
            intuition.
            eapply All2_prop2_eq_split in a1.
            intuition.
            admit. (* a1 *)

          * pose proof X. eapply pred1_mkApps_tCoFix_refl_inv in X.
            eapply pred_proj_congr, pred_mkApps.
            constructor. pcuic.
            apply All2_prop2_eq_split in a1; intuition.
            apply All2_prop2_eq_split in a2; intuition.
            clear -a2.
            rewrite - fold_fix_context_over.
            rewrite fix_context_fold.
            revert a2.
            rewrite - fold_fix_context_over.
            (* TODO: lemmas about fix contexts *)
            admit.
            intuition. intuition.

               (* Lemma map_fix_id Γ Δ m : map_fix (fun _ t => t) Γ Δ m = m. *)
               (* Proof. *)
               (*   unfold map_fix. now rewrite map_def_id map_id. *)
               (* Qed. *)
               (* rewrite - {1}(map_fix_id (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix')) mfix'). *)


               (* generalize (rho_ctx_over (rho_ctx Γ) (fix_context m)). *)
               (* intros. *)
               (* induction 1. simpl. unfold fix_context. simpl. econstructor. *)

               (* rewrite - {1}(map_id mfix'). *)
               (* intros H. apply All2_map_inv in H. unfold on_Trel in H. *)
               (* induction H. simpl. constructor. *)

        + eapply decompose_app_inv in Heq. subst c.
          destruct t; noconf d; econstructor; eauto.

      - simpl.
        rewrite - fold_fix_context_over.
        constructor; eauto.
        now eapply All2_local_env_pred_fix_ctx. red. red in X3.
        eapply All2_sym, All2_map_left, All2_impl; eauto.
        simpl. unfold on_Trel_eq, on_Trel; intuition pcuic.
        rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.


      - simpl.
        rewrite - fold_fix_context_over.
        constructor; eauto.
        now eapply All2_local_env_pred_fix_ctx. red. red in X3.
        eapply All2_sym, All2_map_left, All2_impl; eauto.
        simpl. unfold on_Trel_eq, on_Trel; intuition pcuic.
        rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

      - simpl; econstructor; eauto. simpl in X2. now rewrite !app_context_nil_l in X2.
      - simpl in *. constructor. eauto. eapply All2_sym, All2_map_left, All2_impl. eauto.
        intros. simpl in X. intuition.
      - destruct t; noconf H; simpl; constructor; eauto.
    Admitted.

  End TriangleFn.
  (* Checked that we can prove confluence in presence of let-reductions in the context *)

  Ltac apply_hyp :=
    match reverse goal with
    | [ H : forall _ r, pred1 _ _ _ ?s _ -> _, H' : pred1 _ _ _ ?s _ |- _ ] =>
      let target := fresh "v" in specialize (H _ _ H') as [target [? ?]]
    end.

  (* Checked that we can prove confluence in presence of let-reductions in the context *)

  Corollary confluence : forall Σ Γ Δ Δ' t u v, wf Σ ->
    pred1 Σ Γ Δ t u ->
    pred1 Σ Γ Δ' t v ->
    pred1 Σ Δ (rho_ctx Σ Γ) u (rho Σ (rho_ctx Σ Γ) t) *
    pred1 Σ Δ' (rho_ctx Σ Γ) v (rho Σ (rho_ctx Σ Γ) t).
  Proof.
    intros.
    split; eapply triangle; auto.
  Qed.

End Confluence.