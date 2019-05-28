(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega Utf8 String Lia.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
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

Section FoldFix.
  Context (rho : context -> term -> term).
  Context (Γ : context).

  Fixpoint fold_fix_context acc m :=
    match m with
    | [] => acc
    | def :: fixd =>
      fold_fix_context (vass def.(dname) (lift0 #|acc| (rho Γ def.(dtype))) :: acc) fixd
    end.

  Fixpoint fold_ctx_over Γ' :=
    match Γ' with
    | [] => []
    | {| decl_name := na; decl_body := None; decl_type := T |} :: Γ' =>
      let Γ'' := fold_ctx_over Γ' in
      vass na (rho (Γ ,,, Γ'') T) :: Γ''
    | {| decl_name := na; decl_body := Some b; decl_type := T |} :: Γ' =>
      let Γ'' := fold_ctx_over Γ' in
      vdef na (rho (Γ ,,, Γ'') b) (rho (Γ ,,, Γ'') T) :: Γ''
    end.

End FoldFix.

Lemma term_forall_ctx_list_ind :
  forall (P : context -> term -> Type) (f : context -> term -> term),
    (* (Pctx : context -> Type), *)
    (* (forall Γ Γ', All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) Γ' -> Pctx Γ') -> *)

    (forall Γ (n : nat), P Γ (tRel n)) ->
    (forall Γ (i : ident), P Γ (tVar i)) ->
    (forall Γ (n : nat) (l : list term), All (P Γ) l -> P Γ (tEvar n l)) ->
    (forall Γ s, P Γ (tSort s)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n (f Γ t) :: Γ) t0 -> P Γ (tProd n t t0)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n (f Γ t) :: Γ) t0 -> P Γ (tLambda n t t0)) ->
    (forall Γ (n : name) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall t1 : term, P (vdef n (f Γ t) (f Γ t0) :: Γ) t1 ->
                                                   P Γ (tLetIn n t t0 t1)) ->
    (forall Γ (t u : term), P Γ t -> P Γ u -> P Γ (tApp t u)) ->
    (forall Γ (s : String.string) (u : list Level.t), P Γ (tConst s u)) ->
    (forall Γ (i : inductive) (u : list Level.t), P Γ (tInd i u)) ->
    (forall Γ (i : inductive) (n : nat) (u : list Level.t), P Γ (tConstruct i n u)) ->
    (forall Γ (p : inductive * nat) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall l : list (nat * term),
            tCaseBrsProp (P Γ) l -> P Γ (tCase p t t0 l)) ->
    (forall Γ (s : projection) (t : term), P Γ t -> P Γ (tProj s t)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fold_fix_context f Γ [] m)) m -> P Γ (tFix m n)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, fold_ctx_over f Γ Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fold_fix_context f Γ [] m)) m -> P Γ (tCoFix m n)) ->
    forall Γ (t : term), P Γ t.
Proof.
  intros.
  revert Γ t. set(foo:=Tactics.the_end_of_the_section). intros.
  Subterm.rec_wf_rel aux t (MR lt size). simpl. clear H1.
  assert (auxl : forall Γ {A} (l : list A) (f : A -> term), list_size (fun x => size (f x)) l < size pr0 ->
                                                            All (fun x => P Γ (f x)) l).
  { induction l; constructor. eapply aux. red. simpl in H. lia. apply IHl. simpl in H. lia. }
  assert (forall mfix, context_size size (fix_context mfix) <= mfixpoint_size size mfix).
  { induction mfix. simpl. auto. simpl. unfold fix_context.
    unfold context_size.
    rewrite list_size_rev /=. cbn.
    rewrite size_lift. unfold context_size in IHmfix.
    epose (list_size_mapi_rec_le (def_size size) (decl_size size) mfix
                                 (fun (i : nat) (d : def term) => vass (dname d) ((lift0 i) (dtype d))) 1).
    forward l. intros. destruct x; cbn; rewrite size_lift. lia.
    unfold def_size, mfixpoint_size. lia. }
  assert (auxl' : forall Γ mfix,
             mfixpoint_size size mfix < size pr0 ->
             All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context mfix)).
  { move=> Γ mfix H0.
    move: (fix_context mfix) {H0} (le_lt_trans _ _ _ (H mfix) H0).
    induction fix_context; cbn.
    - constructor.
    - case: a => [na [b|] ty] /=; rewrite {1}/decl_size /context_size /= => Hlt; constructor; auto.
      + eapply IHfix_context. unfold context_size. lia.
      + simpl. eapply aux. red. lia.
      + simpl. split.
        * apply aux. red. lia.
        * apply aux; red; lia.
      + apply IHfix_context; unfold context_size; lia.
      + apply aux. red. lia.
  }
  assert (auxl'' : forall Γ mfix,
             mfixpoint_size size mfix < size pr0 ->
             All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, fold_ctx_over f Γ Γ') t)) (fix_context mfix)).
  { move=> Γ mfix H0.
    move: (fix_context mfix) {H0} (le_lt_trans _ _ _ (H mfix) H0).
    induction fix_context; cbn.
    - constructor.
    - case: a => [na [b|] ty] /=; rewrite {1}/decl_size /context_size /= => Hlt; constructor; auto.
      + eapply IHfix_context. unfold context_size. lia.
      + simpl. apply aux. red. lia.
      + simpl. split.
        * apply aux. red. lia.
        * apply aux; red; lia.
      + apply IHfix_context; unfold context_size; lia.
      + apply aux. red. lia.
  }
  assert (forall m, list_size (fun x : def term => size (dtype x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }
  assert (forall m, list_size (fun x : def term => size (dbody x)) m < S (mfixpoint_size size m)).
  { clear. unfold mfixpoint_size, def_size. induction m. simpl. auto. simpl. lia. }

  move aux at top. move auxl at top. move auxl' at top.

  !destruct pr0; eauto;
    try match reverse goal with
          |- context [tFix _ _] => idtac
        | H : _ |- _ => solve [apply H; (eapply aux || eapply auxl); red; simpl; try lia]
        end.

  eapply X12; try (apply aux; red; simpl; lia).
  apply auxl'. simpl. lia.
  red. apply All_pair. split; apply auxl; simpl; auto.

  eapply X13; try (apply aux; red; simpl; lia).
  apply auxl''. simpl. lia.
  red. apply All_pair. split; apply auxl; simpl; auto.
Defined.


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
      now exists ind, n, ui, [].
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

  Section All2_telescope.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).

    Definition telescope := context.

    Inductive All2_telescope (Γ Γ' : context) : telescope -> telescope -> Type :=
    | telescope2_nil : All2_telescope Γ Γ' [] []
    | telescope2_cons_abs na t t' Δ Δ' :
        P Γ Γ' None t t' ->
        All2_telescope (Γ ,, vass na t) (Γ' ,, vass na t') Δ Δ' ->
        All2_telescope Γ Γ' (vass na t :: Δ) (vass na t' :: Δ')
    | telescope2_cons_def na b b' t t' Δ Δ' :
        P Γ Γ' (Some (b, b')) t t' ->
        All2_telescope (Γ ,, vdef na b t) (Γ' ,, vdef na b' t') Δ Δ' ->
        All2_telescope Γ Γ' (vdef na b t :: Δ) (vdef na b' t' :: Δ').
  End All2_telescope.

  Section All2_telescope_n.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).
    Context (f : nat -> term -> term).

    Inductive All2_telescope_n (Γ Γ' : context) (n : nat) : telescope -> telescope -> Type :=
    | telescope_n_nil : All2_telescope_n Γ Γ' n [] []
    | telescope_n_cons_abs na t t' Δ Δ' :
        P Γ Γ' None (f n t) (f n t') ->
        All2_telescope_n (Γ ,, vass na (f n t)) (Γ' ,, vass na (f n t')) (S n) Δ Δ' ->
        All2_telescope_n Γ Γ' n (vass na t :: Δ) (vass na t' :: Δ')
    | telescope_n_cons_def na b b' t t' Δ Δ' :
        P Γ Γ' (Some (f n b, f n b')) (f n t) (f n t') ->
        All2_telescope_n (Γ ,, vdef na (f n b) (f n t)) (Γ' ,, vdef na (f n b') (f n t'))
                         (S n) Δ Δ' ->
        All2_telescope_n Γ Γ' n (vdef na b t :: Δ) (vdef na b' t' :: Δ').

  End All2_telescope_n.

  Lemma All2_telescope_mapi {P} Γ Γ' Δ Δ' (f : nat -> term -> term) k :
    All2_telescope_n (on_decl P) f Γ Γ' k Δ Δ' ->
    All2_telescope (on_decl P) Γ Γ' (mapi_rec (fun n => map_decl (f n)) Δ k)
                   (mapi_rec (fun n => map_decl (f n)) Δ' k).
  Proof.
    induction 1; simpl; constructor; auto.
  Qed.

  Lemma local_env_telescope P Γ Γ' Δ Δ' :
    All2_telescope (on_decl P) Γ Γ' Δ Δ' ->
    All2_local_env_over P Γ Γ' (List.rev Δ) (List.rev Δ').
  Proof.
    induction 1. simpl. constructor.
    - simpl. eapply All2_local_env_over_app. constructor. constructor.
      simpl. apply p.
      revert IHX.
      generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
      constructor. auto. red in p0. red. red. red. red in p0.
      rewrite !app_context_assoc. cbn. apply p0.
      constructor. auto. destruct p0. unfold on_decl_over in *. simpl.
      rewrite !app_context_assoc. cbn. intuition.
    - simpl. eapply All2_local_env_over_app. constructor. constructor.
      simpl. unfold on_decl_over, on_decl in *. destruct p. split; intuition auto.
      revert IHX.
      generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
      constructor. auto. red in p0. red. red. red. red in p0.
      rewrite !app_context_assoc. cbn. apply p0.
      constructor. auto. destruct p0. unfold on_decl_over in *. simpl.
      rewrite !app_context_assoc. cbn. intuition.
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

    Definition map_fix (rho : context -> term -> term) Γ mfixctx (mfix : mfixpoint term) :=
      (map (map_def (rho Γ) (rho (Γ ,,, mfixctx))) mfix).

   (*  Equations rho (Γ : context) (t : term) : term by struct t := *)
   (*    { rho Γ (tApp t u) with t := *)
   (*        { | tLambda na T b := (rho (vass na (rho Γ T) :: Γ) b) {0 := rho Γ u}; *)
   (*          | _ => tApp (rho Γ t) (rho Γ u) }; *)
   (*    rho Γ (tLetIn na d t b) => (subst10 (rho Γ d) (rho (vdef na (rho Γ d) (rho Γ t) :: Γ) b)); *)
   (*    rho Γ (tRel i) with option_map decl_body (nth_error Γ i) := { *)
   (*      | Some (Some body) => (lift0 (S i) body); *)
   (*      | Some None => tRel i; *)
   (*      | None => tRel i }; *)
   (*    rho Γ (tCase (ind, pars) p x brs) with decompose_app x, decompose_app (rho Γ x) := *)
   (*      { | (tConstruct ind' c u, args) | (tConstruct ind'' c' u', args') *)
   (*       with AstUtils.eq_ind ind ind' := *)
   (*       { | true => *)
   (*           let p' := rho Γ p in *)
   (*           let x' := rho Γ x in *)
   (*           let brs' := map_brs Γ brs in *)
   (*           iota_red pars c args' brs'; *)
   (*         | false => *)
   (*           let p' := rho Γ p in *)
   (*           let x' := rho Γ x in *)
   (*           let brs' := map_brs Γ brs in *)
   (*           tCase (ind, pars) p' x' brs' }; *)
   (*    | (tCoFix mfix idx, args) | (tCoFix mfix' idx', args') with unfold_cofix mfix' idx := { *)
   (*      | Some (narg, fn) => *)
   (*        let p' := rho Γ p in *)
   (*        let x' := rho Γ x in *)
   (*        let brs' := map_brs Γ brs in *)
   (*        tCase (ind, pars) p' (mkApps fn args') brs'; *)
   (*      | None => *)
   (*        let p' := rho Γ p in *)
   (*        let x' := rho Γ x in *)
   (*        let brs' := map_brs Γ brs in *)
   (*        tCase (ind, pars) p' (mkApps (tCoFix mfix' idx) args') brs' }; *)
   (*    | _ | _ => *)
   (*          let p' := rho Γ p in *)
   (*          let x' := rho Γ x in *)
   (*          let brs' := map_brs Γ brs in *)
   (*          tCase (ind, pars) p' x' brs' }; *)
   (*  rho Γ (tProj (i, pars, narg) x) with decompose_app x, decompose_app (rho Γ x) := { *)
   (*    | (tConstruct ind c u, args) | (tConstruct ind' c' u', args') with *)
   (*      nth_error args' (pars + narg) := { *)
   (*      | Some arg1 => *)
   (*        if AstUtils.eq_ind i ind' then arg1 *)
   (*        else tProj (i, pars, narg) (rho Γ x); *)
   (*      | None => tProj (i, pars, narg) (rho Γ x) }; *)
   (*    | (tCoFix mfix idx, args) | (tCoFix mfix' idx', args') with unfold_cofix mfix' idx := { *)
   (*      | Some (narg, fn) => tProj (i, pars, narg) (mkApps fn args'); *)
   (*      | None => tProj (i, pars, narg) (mkApps (tCoFix mfix' idx') args') }; *)
   (*    | _ | _ => tProj (i, pars, narg) (rho Γ x) }; *)
   (* rho Γ (tConst c u) with lookup_env Σ c := { *)
   (*    | Some (ConstantDecl id decl) with decl.(cst_body) := { *)
   (*      | Some body => subst_instance_constr u body; *)
   (*      | None => tConst c u }; *)
   (*    | _ => tConst c u }; *)
   (*  rho Γ (tLambda na t u) => tLambda na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u); *)
   (*  rho Γ (tProd na t u) => tProd na (rho Γ t) (rho (vass na (rho Γ t) :: Γ) u); *)
   (*  rho Γ (tVar i) => tVar i; *)
   (*  rho Γ (tEvar n l) => tEvar n (map_terms Γ l); *)
   (*  rho Γ (tSort s) => tSort s; *)
   (*  rho Γ (tFix mfix idx) => *)
   (*    let mfixctx := fold_fix_context rho Γ [] mfix in *)
   (*    tFix (map_fix rho Γ mfixctx mfix) idx; *)
   (*  rho Γ (tCoFix mfix idx) => *)
   (*    let mfixctx := fold_fix_context rho Γ [] mfix in *)
   (*    tCoFix (map_fix rho Γ mfixctx mfix) idx; *)
   (*    rho Γ x => x } *)

   (*  where map_terms (Γ : context) (l : list term) : list term by struct l := *)
   (*          { map_terms Γ nil := nil; *)
   (*            map_terms Γ (cons p l) := cons (rho Γ p) (map_terms Γ l) } *)


   (*  where map_brs (Γ : context) (l : list (nat * term)) : list (nat * term) by struct l := *)
   (*          { map_brs Γ nil := nil; *)
   (*            map_brs Γ (cons p l) := (fst p, rho Γ (snd p)) :: map_brs Γ l }. *)


    (* Lemma map_terms_map Γ l : map_terms Γ l = map (rho Γ) l. *)
    (* Proof. induction l; simpl; rewrite ?IHl; auto. Qed. *)
    (* Hint Rewrite map_terms_map : rho. *)


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
    | tSort s => tSort s
    | tFix mfix idx =>
      let mfixctx := fold_fix_context rho Γ [] mfix in
      tFix (map_fix rho Γ mfixctx mfix) idx
    | tCoFix mfix idx =>
      let mfixctx := fold_fix_context rho Γ [] mfix in
      tCoFix (map_fix rho Γ mfixctx mfix) idx
    | tInd _ _ | tConstruct _ _ _ => t
    end.
    Transparent rho.

    Lemma rho_mkApps {Γ f l} : isLambda f = false ->
                               rho Γ (mkApps f l) = mkApps (rho Γ f) (map (rho Γ) l).
    Proof.
      induction l in f |- *; auto. simpl. rewrite IHl. simpl. reflexivity.
      intros. destruct f; simpl in *; try congruence.
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
               (λ (Γ' : context) (t : term),
                pred1_ctx Σ (Γ ,,, Γ') (rho_ctx (Γ ,,, Γ')) →
                pred1 Σ (Γ ,,, Γ')
                      (rho_ctx (Γ ,,, Γ')) t
                      (rho (rho_ctx (Γ ,,, Γ')) t))
            ) Δ
          → All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ (rho_ctx Γ))) Δ
                           (rho_ctx_over (rho_ctx Γ) Δ).
    Proof.
      intros.
      induction X0; simpl; constructor; auto.
      - red in t0 |- *. red. rewrite rho_ctx_app in t0.
        apply t0. now apply All2_local_env_app_inv.
      - red in t1 |- *. rewrite rho_ctx_app in t1.
        intuition red; auto using All2_local_env_app_inv.
    Qed.

    Lemma rho_All_All2_local_env' :
      ∀ Γ : context, pred1_ctx Σ Γ (rho_ctx Γ) → ∀ Δ Δ' : context,
          All2_local_env
            (on_decl
               (λ (Γ' Γ'' : context) (t t' : term), pred1_ctx Σ (Γ ,,, Γ') (rho_ctx (Γ ,,, Γ''))
                                             → pred1 Σ (Γ ,,, Γ')
                                                     (rho_ctx (Γ ,,, Γ'')) t
                                                     (rho (rho_ctx (Γ ,,, Γ'')) t'))) Δ Δ'
          → All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ (rho_ctx Γ))) Δ
                           (rho_ctx_over (rho_ctx Γ) Δ').
    Proof.
      intros.
      induction X0; simpl; constructor; auto.
      red in p |- *. red. rewrite !rho_ctx_app in p.
      apply p. now apply All2_local_env_app_inv.
      red in p |- *. rewrite rho_ctx_app in p.
      intuition red; auto using All2_local_env_app_inv.
    Qed.


    Lemma rho_All_All2_local_env_inv :
      ∀ Γ Γ' : context, pred1_ctx Σ Γ' (rho_ctx Γ) → ∀ Δ Δ' : context,
          All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ' (rho_ctx Γ))) Δ
                         (rho_ctx_over (rho_ctx Γ) Δ') ->
          All2_local_env
            (on_decl
               (λ (Δ Δ' : context) (t t' : term), pred1 Σ (Γ' ,,, Δ)
                                                        (rho_ctx (Γ ,,, Δ')) t
                                                        (rho (rho_ctx (Γ ,,, Δ')) t'))) Δ Δ'.

    Proof.
      intros. induction Δ in Δ', X0 |- *. depelim X0. destruct Δ'; noconf x. constructor.
      cbn in x. destruct c as [? [?|] ?]; noconf x.
      depelim X0.
      - destruct Δ'. noconf x. destruct c as [? [?|] ?]; noconf x.
        simpl in H. noconf H. simpl in H. noconf H.
        constructor. eapply IHΔ. auto. red. red in p. intros.
        red in p. rewrite !rho_ctx_app. eapply p.
      - destruct Δ'. noconf x. destruct c as [? [?|] ?]; noconf x.
        simpl in H. noconf H. red in p. destruct p.
        constructor. eapply IHΔ. auto. red. red in o, o0. intros.
        rewrite !rho_ctx_app. split; eauto.
        simpl in H. noconf H.
    Qed.

    Hint Resolve pred_mkApps : pcuic.

    Lemma nth_error_rho_ctx {Γ n c} :
      nth_error Γ n = Some c ->
      nth_error (rho_ctx Γ) n = Some (map_decl (rho (rho_ctx (skipn (S n) Γ))) c).
    Proof.
      induction Γ in n, c |- *; destruct n; try (simpl; congruence).
      intros [= ->].
      destruct c as [? [?|] ?]; simpl.
      unfold map_decl. simpl. unfold skipn.
      now rewrite app_context_nil_l.
      now rewrite app_context_nil_l.
      intros. simpl in H. specialize (IHΓ _ _ H).
      destruct a as [? [?|] ?]; simpl; now rewrite IHΓ.
    Qed.

    Lemma map_eq_inj {A B} (f g : A -> B) l: map f l = map g l ->
                                            All (fun x => f x = g x) l.
    Proof.
      induction l. simpl. constructor. simpl. intros [=]. constructor; auto.
    Qed.

    Lemma map_cofix_subst (f : context -> term -> term)
          (f' : context -> context -> term -> term) mfix Γ Γ' :
      (forall n, tCoFix (map (map_def (f Γ) (f' Γ Γ')) mfix) n = f Γ (tCoFix mfix n)) ->
      cofix_subst (map (map_def (f Γ) (f' Γ Γ')) mfix) =
      map (f Γ) (cofix_subst mfix).
    Proof.
      unfold cofix_subst. intros.
      rewrite map_length. generalize (#|mfix|). induction n. simpl. reflexivity.
      simpl. rewrite - IHn. f_equal. apply H.
    Qed.

    Derive NoConfusion for def.

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
      fold_fix_context rho Γ l m =
      List.rev (mapi (λ (i : nat) (x : def term),
                      vass (dname x) ((lift0 (#|l| + i)) (rho Γ (dtype x)))) m) ++ l.
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

    Lemma fold_fix_context_rev {Γ m} :
      fold_fix_context rho Γ [] m =
      List.rev (mapi (λ (i : nat) (x : def term),
                      vass (dname x) (lift0 i (rho Γ (dtype x)))) m).
    Proof.
      pose proof (@fold_fix_context_rev_mapi Γ [] m).
      now rewrite app_nil_r in H.
    Qed.

    Lemma nth_error_map_fix i f Γ Δ m :
      nth_error (map_fix f Γ Δ m) i = option_map (map_def (f Γ) (f (Γ ,,, Δ))) (nth_error m i).
    Proof.
      now rewrite /map_fix nth_error_map.
    Qed.

    Axiom todo : forall {A}, A.
    Ltac todo := apply todo.

    Lemma fold_fix_context_length f Γ l m : #|fold_fix_context f Γ l m| = #|m| + #|l|.
    Proof.
      induction m in l |- *; simpl; auto. rewrite IHm. simpl. auto with arith.
    Qed.


    Lemma All_rev (A : Type) (P : A → Type) (l : list A) : All P l → All P (List.rev l).
    Proof.
      induction l using rev_ind. constructor. rewrite rev_app_distr.
      simpl. intros X; apply All_app in X as [? ?]. depelim a0; intuition auto.
    Qed.

    Lemma skipn_S {A} a (l : list A) n : skipn (S n) (a :: l) = skipn n l.
    Proof. reflexivity. Qed.

    Lemma Alli_nth_error {A} (P : nat -> A -> Type) k ctx :
      (forall i x, nth_error ctx i = Some x -> P (k + i) x) ->
      Alli P k ctx.
    Proof.
      intros. induction ctx in k, X |- *. constructor.
      constructor. specialize (X 0 a eq_refl). now rewrite Nat.add_0_r in X.
      apply IHctx. intros. specialize (X (S i) x H).
      simpl. now replace (S (k + i)) with (k + S i) by lia.
    Qed.


    Lemma All_local_env_Alli P ctx :
      All_local_env (on_local_decl P) ctx ->
      Alli (fun n decl =>
          P (skipn (S n) ctx) (decl_type decl)) 0 ctx.
    Proof.
      (* rewrite -{1}(List.rev_length m). *)
      intros.
      eapply Alli_nth_error. intros.
      eapply All_local_env_lookup in H; eauto.  red in H.
      destruct x as [? [?|] ?]. simpl in *. intuition.
      now simpl in H.
    Qed.

    Lemma Alli_mapi {A B} {P : nat -> B -> Type} (f : nat -> A -> B) k l :
      Alli (fun n a => P n (f n a)) k l <~>
      Alli P k (mapi_rec f l k).
    Proof.
      split.
      { induction 1. simpl. constructor.
        simpl. constructor; eauto. }
      { induction l in k |- *. simpl. constructor.
        simpl. intros. depelim X. constructor; eauto. }
    Qed.

    Lemma All_local_env_fix_Alli P m :
      All_local_env (on_local_decl P) (fix_context m) ->
      Alli (fun n def =>
      P (skipn (S n) (fix_context m)) (lift0 (Nat.pred #|m| - n) (dtype def)))%type 0 (List.rev m).
    Proof.
      intros.
      eapply All_local_env_Alli in X.
      unfold fix_context in X.
      rewrite rev_mapi in X. eapply Alli_mapi in X.
      simpl in X. eapply Alli_impl. eauto. intros.
      simpl in X0. rewrite - (rev_mapi (fun k x => vass (dname x) (lift0 k (dtype x)))) in X0.
      now fold (fix_context m) in X0.
    Qed.

    Lemma Alli_shift {A} {P : nat -> A -> Type} k l :
      Alli (fun x => P (S x)) k l ->
      Alli P (S k) l.
    Proof.
      induction 1; simpl; constructor; auto.
    Qed.

    Lemma Alli_rev {A} {P : nat -> A -> Type} k l :
      Alli P k l ->
      Alli (fun k' => P (Nat.pred #|l| - k' + k)) 0 (List.rev l).
    Proof.
      revert k.
      induction l using rev_ind; simpl; intros; try constructor.
      eapply Alli_app in X. intuition.
      rewrite rev_app_distr. rewrite app_length.
      simpl. constructor.
      replace (Nat.pred (#|l| + 1) - 0) with #|l| by lia.
      depelim b. eauto. specialize (IHl _ a).
      eapply Alli_shift. eapply Alli_impl. eauto.
      simpl; intros.
      now replace (Nat.pred (#|l| + 1) - S n) with (Nat.pred #|l| - n) by lia.
    Qed.

    Lemma Alli_All_mix {A} {P : nat -> A -> Type} (Q : A -> Type) k l :
      Alli P k l -> All Q l -> Alli (fun k x => (P k x) * Q x)%type k l.
    Proof.
      induction 1; constructor; try depelim X0; intuition auto.
    Qed.

    Context (wfΣ : wf Σ).

    (*
             eapply (rho_elim
              (fun ctx t rhot =>
                   ∀ (Γ : context) (Δ Γ' : list context_decl), ctx = Γ ,,, rho_ctx_over Γ Γ'
                                              → lift #|Δ| #|Γ'| rhot =
                                                rho
                                                  (Γ ,,, Δ ,,,
                                                   lift_context #|Δ| 0 (rho_ctx_over Γ Γ'))
                                                  (lift #|Δ| #|Γ'| t))
              (fun ctx l l' =>
                 ∀ (Γ : context) (Δ Γ' : list context_decl),
                   ctx = Γ ,,, rho_ctx_over Γ Γ' →
                   map (lift #|Δ| #|Γ'|) l' =
                   map (rho (Γ ,,, Δ ,,, lift_context #|Δ| 0 (rho_ctx_over Γ Γ'))
                                    ∘ lift #|Δ| #|Γ'|) l)
              (fun ctx brs brs' =>
                 ∀ (Γ : context) (Δ Γ' : list context_decl),
                   ctx = Γ ,,, rho_ctx_over Γ Γ' →
                   map (on_snd (lift #|Δ| #|Γ'|)) brs' =
                   map (on_snd (rho (Γ ,,, Δ ,,, lift_context #|Δ| 0 (rho_ctx_over Γ Γ'))
                                    ∘ lift #|Δ| #|Γ'|)) brs)); clear; simpl; intros;
        subst Γ; auto.
*)

    Lemma fold_ctx_over_eq Γ Γ' : rho_ctx_over Γ Γ' = fold_ctx_over rho Γ Γ'.
    Proof.
      induction Γ'; auto.
    Qed.

    Section foldover.
      Context (Γ Γ' : context).

      Fixpoint fold_fix_context_over acc m :=
        match m with
        | [] => acc
        | def :: fixd =>
          fold_fix_context_over
            (vass def.(dname) (lift #|acc| #|Γ'| (rho (Γ ,,, Γ') def.(dtype))) :: acc) fixd
        end.
    End foldover.

    Lemma fold_fix_context_over2 Γ acc m :
      fold_fix_context_over Γ [] acc m =
      fold_fix_context rho Γ acc m.
    Proof.
      induction m in acc |- *; simpl. reflexivity.
      now rewrite IHm.
    Qed.

    Lemma fold_fix_context_over_acc' Γ Δ m :
      (* (forall Γ t acc', rho (acc' ++ acc ++ Γ) ((lift0 #|acc' ++ acc|) t) = *)
      (*       (lift0 #|acc' ++ acc|) (rho Γ t)) -> *)
      (All (fun d =>
              forall Δ,
              rho ((* Γ' ++ *) Δ ++ Γ) ((lift #|Δ| 0 (* #|Γ'| *)) (dtype d)) =
                          (lift #|Δ| (* #|Γ'| *) 0) (rho (Γ (* ,,, Γ' *)) (dtype d))) m) ->

      rho_ctx_over (Γ ,,, Δ (* ,,, Γ' *))
                   ((List.rev (mapi_rec (λ (i : nat) (d : def term),
                                         vass (dname d) ((lift i 0(* #|Γ'| *)) (dtype d))) m #|Δ|)))
                   ++ Δ =
      fold_fix_context_over Γ [] Δ m.
    Proof.
      induction m in Γ, Δ |- *. simpl; auto. intros.
      simpl.
      rewrite rho_ctx_over_app. simpl.
      unfold app_context. unfold app_context in IHm.
      erewrite <- IHm. simpl. cbn.
      depelim H. rewrite -e.
      rewrite - app_assoc.
      f_equal. now depelim H.
    Qed.

    Lemma fold_fix_context_over' Γ m :
      (* (forall Γ t acc', rho (acc' ++ acc ++ Γ) ((lift0 #|acc' ++ acc|) t) = *)
      (*       (lift0 #|acc' ++ acc|) (rho Γ t)) -> *)
      (All (fun d =>
              forall Δ,
              rho (Δ ++ Γ) ((lift0 #|Δ|) (dtype d)) =
                          (lift0 #|Δ|) (rho Γ (dtype d))) m) ->

      rho_ctx_over Γ (fix_context m) =
      fold_fix_context rho Γ [] m.
    Proof.
      intros.
      rewrite - fold_fix_context_over2.
      rewrite - fold_fix_context_over_acc'. auto.
      simpl. now rewrite app_nil_r.
    Qed.

    Lemma fold_fix_context_app Γ l acc acc' :
      fold_fix_context rho Γ l (acc ++ acc') =
      fold_fix_context rho Γ (fold_fix_context rho Γ l acc) acc'.
    Proof.
      induction acc in l, acc' |- *. simpl. auto.
      simpl. rewrite IHacc. reflexivity.
    Qed.

    Local Open Scope sigma_scope.

    Definition ctxmap (Γ Δ : context) (s : nat -> term) :=
      forall x d, nth_error Γ x = Some d ->
                  match decl_body d return Type with
                  | Some b => s x = b.[↑^(S x) ∘ s]
                  | None => Σ ;;; Δ |- s x : d.(decl_type).[↑^(S x) ∘ s]
                  end.

    Lemma simpl_pred Γ Γ' t t' u u' : t = t' -> u = u' -> pred1 Σ Γ Γ' t' u' -> pred1 Σ Γ Γ' t u.
    Proof. now intros -> ->. Qed.

    Hint Rewrite @subst_consn_nil @subst_consn_tip : sigma.

    Ltac simpl_pred :=
      eapply simpl_pred;
      rewrite ?up_Upn;
      unfold Upn, Up, idsn;
      [autorewrite with sigma; reflexivity|
                          autorewrite with sigma; reflexivity|].

    Lemma subst10_inst a b τ : b {0 := a}.[τ] = (b.[⇑ τ] {0 := a.[τ]}).
    Proof.
      unfold subst10. simpl. rewrite !subst_inst.
      now unfold Upn, Up; autorewrite with sigma.
    Qed.

    Lemma lift_renaming_0 k : ren (lift_renaming k 0) = ren (Nat.add k).
    Proof. reflexivity. Qed.

    Lemma pred_atom_inst t σ : pred_atom t -> t.[σ] = t.
    Proof.
      destruct t; simpl; intros; try discriminate; auto.
    Qed.

    Lemma strong_substitutivity Γ Γ' Δ Δ' s t σ τ :
      pred1 Σ Γ Γ' s t ->
      ctxmap Γ Δ σ ->
      ctxmap Γ' Δ' τ ->
      (forall x, pred1 Σ Δ Δ' (σ x) (τ x)) ->
      pred1 Σ Δ Δ' s.[σ] t.[τ].
    Proof.
      intros redst.
      revert Δ Δ' σ τ.
      induction redst; autorewrite with sigma; intros.
      all:eauto 2 with pcuic.

      1:{ autorewrite with sigma.
          specialize (IHredst1 _ _ _ _ X X0 X1).
          specialize (IHredst2 (Δ ,, vass na t0.[σ]) (Δ' ,, vass na t1.[τ]) (⇑ σ) (⇑ τ)).
          forward IHredst2. admit.
          forward IHredst2. admit.
          forward IHredst2.
          intros. simpl_pred.
          destruct x; simpl. eapply pred1_refl_gen. constructor; eauto with pcuic.
          unfold subst_compose. admit. (* Closure under renaming *)
          specialize (IHredst3 _ _ _ _ X X0 X1).
          pose proof (pred_beta _ _ _ _ _ _ _ _ _ _ IHredst1 IHredst2 IHredst3).
          now rewrite subst10_inst. }

      2:{ rewrite lift_rename rename_inst.
          simpl. rewrite lift_renaming_0. red in X0.
          destruct (nth_error Γ' i) eqn:Heq; noconf e. simpl in H.
          specialize (X0 _ _ Heq). rewrite H in X0.
          specialize (X1 i). rewrite X0 in X1.
          now simpl_pred. }

      18:{ rewrite !pred_atom_inst; auto. eapply pred1_refl_gen; auto with pcuic.
           specialize (X1 0). auto with pcuic. }
    Admitted.

    Lemma All2_prop2_eq_split (Γ Γ' Γ2 Γ2' : context) (A B : Type) (f g : A → term)
          (h : A → B) (rel : context → context → term → term → Type) x y :
      All2_prop2_eq Γ Γ' Γ2 Γ2' f g h rel x y ->
      All2 (on_Trel (rel Γ Γ') f) x y *
      All2 (on_Trel (rel Γ2 Γ2') g) x y *
      All2 (on_Trel eq h) x y.
    Proof.
      induction 1; intuition.
    Qed.

    Lemma All2_sym {A} (P : A -> A -> Type) l l' :
      All2 P l l' -> All2 (fun x y => P y x) l' l.
    Proof.
      induction 1; constructor; auto.
    Qed.

    Definition rho_ctxmap (Γ Δ : context) (s : nat -> term) :=
      forall x d, nth_error Γ x = Some d ->
                  match decl_body d return Type with
                  | Some b => { i : _ & (s x = tRel i) *
                                        (option_map decl_body (nth_error Δ i) = Some (Some b.[↑^(S x) ∘ s])) }%type
                  | None => Σ ;;; Δ |- s x : d.(decl_type).[↑^(S x) ∘ s]
                  end.

    Lemma lift0_inst n t : lift0 n t = t.[↑^n].
    Proof. by rewrite lift_rename rename_inst lift_renaming_0 -ren_shiftk. Qed.

    Lemma rho_inst Γ Δ s t :
      forall (Hs : rho_ctxmap Γ Δ s),
      (rho Γ t).[s] = rho Δ t.[s].
    Proof.
      revert Γ t Δ s.
      refine (term_forall_ctx_list_ind _ (fun ctx t => rho ctx t) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        simpl; intros; try subst Γ; try rename Γ0 into Γ(* ; rename_all_hyps *).
      all:eauto 2 with pcuic.
      all:(try change_Sk;
           try solve [f_equal;
           rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def,
                    ?map_length, ?Nat.add_assoc;
             eauto; solve_all; eauto]).

      - destruct (nth_error Γ n) as [c|] eqn:Heq.
        -- pose proof Heq as Heq'.
           eapply nth_error_Some_length in Heq'.
           simpl. destruct decl_body eqn:Heq''.
           rewrite lift0_inst.
           specialize (Hs _ _ Heq). rewrite Heq'' in Hs.
           destruct Hs as [i [sni Hb']]. rewrite sni. simpl. rewrite Hb'.
           rewrite lift0_inst. autorewrite with sigma.



  (*          rewrite app_context_length rho_ctx_over_length in Heq'. simpl. *)
  (*          elim (leb_spec_Set). intros. simpl. *)
  (*          --- rewrite nth_error_app_ge. rewrite lift_context_length rho_ctx_over_length; lia. *)
  (*              simpl. *)
  (*              rewrite nth_error_app_ge in Heq; rewrite ?rho_ctx_over_length; try lia. *)
  (*              rewrite rho_ctx_over_length in Heq. *)
  (*              rewrite nth_error_app_ge ?lift_context_length ?rho_ctx_over_length. lia. *)
  (*              assert ((#|Δ| + n - #|Γ'| - #|Δ|) = n - #|Γ'|) as -> by lia. *)
  (*              rewrite Heq. simpl. *)
  (*              destruct c as [? [?|] ?]; simpl. *)
  (*              rewrite simpl_lift; try f_equal; lia. *)
  (*              elim leb_spec_Set; intros; auto; elimtype False; try lia. *)
  (*          --- intros. *)
  (*              simpl. *)
  (*              rewrite nth_error_app_lt in Heq |- *; rewrite ?rho_ctx_over_length; try lia. *)
  (*              rewrite nth_error_app_lt // ?lift_context_length ?rho_ctx_over_length //. *)
  (*              erewrite nth_error_lift_context; eauto. *)
  (*              rewrite ?rho_ctx_over_length; eauto. simpl. *)
  (*              rewrite Nat.add_0_r. *)
  (*              destruct c as [? [?|] ?]; simpl. *)
  (*              rewrite (permute_lift _ #|Δ| (#|Γ'| - S n) (S n) 0). lia. *)
  (*              f_equal. lia. *)
  (*              elim leb_spec_Set; intros; auto; elimtype False; try lia. *)
  (*              now rewrite rho_ctx_over_length. *)
  (*       -- simpl. *)
  (*          pose proof Heq as Heq'. *)
  (*          eapply nth_error_None in Heq'. *)
  (*          rewrite app_context_length in Heq'. *)
  (*          elim (leb_spec_Set). intros. simpl. *)
  (*          --- rewrite nth_error_app_ge. rewrite !lift_context_length; lia. simpl. *)
  (*              rewrite nth_error_app_ge rho_ctx_over_length in Heq; try lia. *)
  (*              rewrite nth_error_app_ge ?lift_context_length ?rho_ctx_over_length. lia. *)
  (*              assert ((#|Δ| + n - #|Γ'| - #|Δ|) = n - #|Γ'|) as -> by lia. *)
  (*              rewrite Heq. simpl. reflexivity. *)
  (*          --- intros. *)
  (*              simpl. *)
  (*              rewrite rho_ctx_over_length in Heq'. *)
  (*              rewrite nth_error_app_lt in Heq |- *; try lia. *)




  (*   Lemma rho_lift Γ Δ Γ' t : *)
  (*     lift #|Δ| #|Γ'| (rho (Γ ,,, rho_ctx_over Γ Γ') t) = *)
  (*     rho (Γ ,,, Δ ,,, lift_context #|Δ| 0 (rho_ctx_over Γ Γ')) (lift #|Δ| #|Γ'| t). *)
  (*   Proof. *)
  (*     remember (Γ ,,, rho_ctx_over Γ Γ') as ctx. revert Γ Δ Γ' Heqctx. *)
  (*     revert ctx t. *)
  (*     refine (term_forall_ctx_list_ind _ (fun ctx t => rho ctx t) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); *)
  (*       simpl; !intros; try subst Γ; rename Γ0 into Γ; rename_all_hyps. *)
  (*     all:eauto 2 with pcuic. *)
  (*     all:(try change_Sk; *)
  (*          try solve [f_equal; *)
  (*          rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, *)
  (*                   ?map_length, ?Nat.add_assoc; *)
  (*            eauto; solve_all; eauto]). *)

  (*     - destruct (nth_error (Γ ,,, (rho_ctx_over Γ Γ')) n) as [c|] eqn:Heq. *)
  (*       -- pose proof Heq as Heq'. *)
  (*          eapply nth_error_Some_length in Heq'. *)
  (*          rewrite app_context_length rho_ctx_over_length in Heq'. simpl. *)
  (*          elim (leb_spec_Set). intros. simpl. *)
  (*          --- rewrite nth_error_app_ge. rewrite lift_context_length rho_ctx_over_length; lia. *)
  (*              simpl. *)
  (*              rewrite nth_error_app_ge in Heq; rewrite ?rho_ctx_over_length; try lia. *)
  (*              rewrite rho_ctx_over_length in Heq. *)
  (*              rewrite nth_error_app_ge ?lift_context_length ?rho_ctx_over_length. lia. *)
  (*              assert ((#|Δ| + n - #|Γ'| - #|Δ|) = n - #|Γ'|) as -> by lia. *)
  (*              rewrite Heq. simpl. *)
  (*              destruct c as [? [?|] ?]; simpl. *)
  (*              rewrite simpl_lift; try f_equal; lia. *)
  (*              elim leb_spec_Set; intros; auto; elimtype False; try lia. *)
  (*          --- intros. *)
  (*              simpl. *)
  (*              rewrite nth_error_app_lt in Heq |- *; rewrite ?rho_ctx_over_length; try lia. *)
  (*              rewrite nth_error_app_lt // ?lift_context_length ?rho_ctx_over_length //. *)
  (*              erewrite nth_error_lift_context; eauto. *)
  (*              rewrite ?rho_ctx_over_length; eauto. simpl. *)
  (*              rewrite Nat.add_0_r. *)
  (*              destruct c as [? [?|] ?]; simpl. *)
  (*              rewrite (permute_lift _ #|Δ| (#|Γ'| - S n) (S n) 0). lia. *)
  (*              f_equal. lia. *)
  (*              elim leb_spec_Set; intros; auto; elimtype False; try lia. *)
  (*              now rewrite rho_ctx_over_length. *)
  (*       -- simpl. *)
  (*          pose proof Heq as Heq'. *)
  (*          eapply nth_error_None in Heq'. *)
  (*          rewrite app_context_length in Heq'. *)
  (*          elim (leb_spec_Set). intros. simpl. *)
  (*          --- rewrite nth_error_app_ge. rewrite !lift_context_length; lia. simpl. *)
  (*              rewrite nth_error_app_ge rho_ctx_over_length in Heq; try lia. *)
  (*              rewrite nth_error_app_ge ?lift_context_length ?rho_ctx_over_length. lia. *)
  (*              assert ((#|Δ| + n - #|Γ'| - #|Δ|) = n - #|Γ'|) as -> by lia. *)
  (*              rewrite Heq. simpl. reflexivity. *)
  (*          --- intros. *)
  (*              simpl. *)
  (*              rewrite rho_ctx_over_length in Heq'. *)
  (*              rewrite nth_error_app_lt in Heq |- *; try lia. *)

  (*     - specialize (h_forall_Γ Γ Δ Γ' eq_refl). *)
  (*       specialize (h_forall_Γ0 Γ Δ (Γ' ,, vass n t) eq_refl). *)
  (*       simpl in *. *)
  (*       now rewrite h_forall_Γ0 -h_forall_Γ lift_context_snoc Nat.add_0_r rho_ctx_over_length. *)

  (*     - specialize (h_forall_Γ Γ Δ Γ' eq_refl). *)
  (*       specialize (h_forall_Γ0 Γ Δ (Γ' ,, vass n t) eq_refl). *)
  (*       simpl in *. *)
  (*       now rewrite h_forall_Γ0 -h_forall_Γ lift_context_snoc Nat.add_0_r rho_ctx_over_length. *)

  (*     - specialize (h_forall_Γ Γ Δ Γ' eq_refl). *)
  (*       specialize (h_forall_Γ0 Γ Δ Γ' eq_refl). *)
  (*       specialize (h_forall_Γ1 Γ Δ (Γ' ,, vdef n t t0) eq_refl). *)
  (*       simpl in *. *)
  (*       rewrite - !h_forall_Γ - !h_forall_Γ0. *)
  (*       rewrite !distr_lift_subst h_forall_Γ1. simpl. *)
  (*       unfold subst10. f_equal. *)
  (*       now rewrite lift_context_snoc Nat.add_0_r rho_ctx_over_length. *)

  (*     - specialize (h_forall_Γ Γ Δ Γ' eq_refl). *)
  (*       specialize (h_forall_Γ0 Γ Δ Γ' eq_refl). *)
  (*       rewrite -h_forall_Γ0 -h_forall_Γ. *)
  (*       destruct t; try reflexivity. *)
  (*       simpl. *)
  (*       elim leb_spec_Set; reflexivity. *)
  (*       simpl. *)
  (*       rewrite distr_lift_subst. *)
  (*       unfold subst10. simpl. f_equal. *)
  (*       simpl in h_forall_Γ. noconf h_forall_Γ. *)
  (*       auto. *)

  (*     - destruct lookup_env eqn:Heq. destruct g as [? [? [?|] ?]|]; simpl in *; auto. *)
  (*       rewrite lift_subst_instance_constr. *)
  (*       pose proof (lookup_env_cst_inv Heq). subst s. *)
  (*       eapply lift_declared_constant in Heq. *)
  (*       unfold map_constant_body in Heq. injection Heq. intros <-; auto. *)
  (*       auto. *)
  (*       simpl. auto. *)

  (*     - specialize (h_forall_Γ Γ Δ Γ' eq_refl). *)
  (*       specialize (h_forall_Γ0 Γ Δ Γ' eq_refl). *)
  (*       assert (Hl :map (on_snd (lift #|Δ| #|Γ'|)) *)
  (*                   (map (λ x : nat * term, (fst x, rho (Γ ,,, rho_ctx_over Γ Γ') (snd x))) l) = *)
  (*               map (fun x => (fst x, rho (Γ ,,, Δ ,,, lift_context #|Δ| 0 *)
  (*                     (rho_ctx_over Γ Γ')) (snd x))) *)
  (*                     (map (on_snd (lift #|Δ| #|Γ'|)) l)). *)
  (*       { rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, *)
  (*         ?map_length, ?Nat.add_assoc. solve_all. } *)
  (*       destruct decompose_app eqn:Heq. *)
  (*       destruct (view_construct_cofix t1). *)
  (*       red in X. *)
  (*       + apply decompose_app_inv in Heq. *)
  (*         subst t0. simpl. *)
  (*         rewrite rho_mkApps; auto. *)
  (*         rewrite decompose_app_mkApps; auto. *)
  (*         simpl. rewrite lift_mkApps rho_mkApps in h_forall_Γ0. auto. *)
  (*         rewrite lift_mkApps decompose_app_mkApps. auto. simpl. *)
  (*         rewrite rho_mkApps // decompose_app_mkApps // /=. *)
  (*         rewrite lift_mkApps rho_mkApps in h_forall_Γ0; auto. *)
  (*         simpl in h_forall_Γ0. *)
  (*         eapply mkApps_eq_inj in h_forall_Γ0; intuition eauto. *)
  (*         destruct (AstUtils.eq_ind a c). *)
  (*         -- rewrite lift_iota_red. *)
  (*            f_equal. auto. *)
  (*            rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, *)
  (*            ?map_length, ?Nat.add_assoc. solve_all. *)
  (*         -- simpl. f_equal; auto. *)
  (*            rewrite lift_mkApps. simpl. f_equal; auto. *)

  (*       + apply decompose_app_inv in Heq. *)
  (*         subst t0. simpl. *)
  (*         rewrite rho_mkApps; auto. *)
  (*         rewrite decompose_app_mkApps; auto. *)
  (*         simpl. rewrite lift_mkApps rho_mkApps in h_forall_Γ0. auto. *)
  (*         rewrite lift_mkApps decompose_app_mkApps. auto. simpl. *)
  (*         rewrite rho_mkApps // decompose_app_mkApps // /=. *)
  (*         rewrite lift_mkApps rho_mkApps in h_forall_Γ0; auto. *)
  (*         simpl in h_forall_Γ0. *)
  (*         eapply mkApps_eq_inj in h_forall_Γ0; intuition eauto. *)
  (*         noconf H. simpl in H. revert H; simplify *. *)
  (*         intros. *)
  (*         unfold unfold_cofix. rewrite !nth_error_map_fix !nth_error_map. *)
  (*         destruct nth_error eqn:Heq. *)
  (*         -- simpl. f_equal; auto. *)
  (*            rewrite lift_mkApps. simpl. f_equal; auto. *)
  (*            rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, *)
  (*            ?map_length, ?Nat.add_assoc. *)
  (*            unfold map_fix in H. *)
  (*            rewrite !map_length !map_map_compose /compose /= /map_def in H. *)
  (*            eapply map_eq_inj in H. *)
  (*            simpl. *)
  (*            rewrite (map_cofix_subst (fun Γ => rho Γ) (fun Γ Γ' => rho (Γ ,,, Γ'))). *)
  (*            { intros. simpl. f_equal. } *)
  (*            rewrite distr_lift_subst !/map_fix !map_length !map_map_compose !/compose. *)
  (*            erewrite <- *)
  (*                     (map_cofix_subst *)
  (*                        (fun Γ x => lift #|Δ| #|Γ'| (rho (Γ ,,, rho_ctx_over Γ Γ') x)) *)
  (*                        (fun Γ Γ'' x => lift #|Δ| (#|Γ''| + _) *)
  (*                                                (rho (Γ ,,, _ ,,, fold_fix_context rho (Γ ,,, rho_ctx_over Γ Γ') [] mfix) x)) *)
  (*                        mfix Γ *)
  (*                        (fix_context mfix)). *)
  (*            simpl in *. *)

  (*            f_equal. f_equal. *)
  (*            { solve_all. noconf H. *)
  (*              unfold map_def; destruct x; simpl in *. f_equal; auto. rewrite - H2. *)
  (*              rewrite fix_context_length. eauto. } *)

  (*            rewrite cofix_subst_length. *)
  (*            eapply nth_error_all in Heq. 2:eapply H. simpl in Heq. *)
  (*            noconf Heq. rewrite H3. reflexivity. *)
  (*            intros. simpl. f_equal. unfold map_fix. *)
  (*            rewrite !map_map_compose. solve_all. noconf H. *)
  (*            unfold compose. *)
  (*            unfold map_def; simpl; f_equal; simpl. now rewrite map_length fix_context_length. *)
  (*         -- simpl. f_equal; eauto. *)
  (*            rewrite !lift_mkApps. simpl. *)
  (*            f_equal; eauto. f_equal. eauto. *)

  (*       + destruct p. epose proof (decompose_app_lift #|Δ| #|Γ'| _ _ _ Heq). *)
  (*         apply decompose_app_inv in Heq. subst t0. rewrite H. *)
  (*         destruct t1; simpl in *; try discriminate; try contradiction; try congruence. *)
  (*         elim leb_spec_Set; intros; auto; try congruence. *)

  (*     - destruct s. destruct p. *)
  (*       specialize (h_forall_Γ Γ Δ Γ' eq_refl). *)
  (*       destruct decompose_app eqn:Heq. *)
  (*       destruct (view_construct_cofix t0). *)
  (*       + apply decompose_app_inv in Heq. *)
  (*         subst t. simpl. *)
  (*         rewrite rho_mkApps; auto. *)
  (*         rewrite decompose_app_mkApps; auto. *)
  (*         simpl. rewrite lift_mkApps rho_mkApps in h_forall_Γ. auto. *)
  (*         rewrite lift_mkApps decompose_app_mkApps. auto. simpl. *)
  (*         rewrite rho_mkApps // decompose_app_mkApps // /=. *)
  (*         rewrite lift_mkApps rho_mkApps in h_forall_Γ; auto. *)
  (*         simpl in h_forall_Γ. *)
  (*         eapply mkApps_eq_inj in h_forall_Γ; intuition eauto. *)
  (*         rewrite !nth_error_map. destruct nth_error eqn:Heq; simpl. *)
  (*         -- destruct (eq_ind_spec i c); subst. *)
  (*            rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, *)
  (*            ?map_length, ?Nat.add_assoc in H0. *)
  (*            apply map_eq_inj in H0. *)
  (*            now eapply nth_error_all in Heq; eauto. *)
  (*            simpl. f_equal. rewrite lift_mkApps. f_equal. *)
  (*            now rewrite !map_map_compose in H0 |- *. *)
  (*         -- simpl. f_equal; auto. *)
  (*            rewrite lift_mkApps. simpl. f_equal; auto. *)

  (*       + apply decompose_app_inv in Heq. *)
  (*         subst t. simpl. *)
  (*         rewrite rho_mkApps; auto. *)
  (*         rewrite decompose_app_mkApps; auto. *)
  (*         simpl. rewrite lift_mkApps rho_mkApps in h_forall_Γ. auto. *)
  (*         rewrite lift_mkApps decompose_app_mkApps. auto. simpl. *)
  (*         rewrite rho_mkApps // decompose_app_mkApps // /=. *)
  (*         rewrite lift_mkApps rho_mkApps in h_forall_Γ; auto. *)
  (*         simpl in h_forall_Γ. *)
  (*         eapply mkApps_eq_inj in h_forall_Γ; intuition eauto. *)
  (*         noconf H. simpl in H. revert H; simplify *. *)
  (*         intros. *)
  (*         unfold unfold_cofix, map_fix. *)
  (*         rewrite !nth_error_map. destruct nth_error eqn:Heq. *)
  (*         -- simpl. f_equal; auto. *)
  (*            rewrite lift_mkApps. simpl. f_equal; auto. *)
  (*            rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, *)
  (*            ?map_length, ?Nat.add_assoc. solve_all. *)
  (*            simpl. *)
  (*            unfold map_fix in H. *)
  (*            rewrite !map_length !map_map_compose /compose /= /map_def in H. *)
  (*            eapply map_eq_inj in H. *)
  (*            simpl. *)
  (*            rewrite (map_cofix_subst (fun Γ => rho Γ) (fun Γ Γ' => rho (Γ ,,, Γ'))). *)
  (*            { intros. simpl. f_equal. } *)
  (*            rewrite distr_lift_subst !/map_fix !map_length !map_map_compose !/compose. *)
  (*            erewrite <- *)
  (*                     (map_cofix_subst *)
  (*                        (fun Γ x => lift #|Δ| #|Γ'| (rho (Γ ,,, rho_ctx_over Γ Γ') x)) *)
  (*                        (fun Γ Γ'' x => lift #|Δ| (#|Γ''| + _) *)
  (*                                                (rho (Γ ,,, _ ,,, fold_fix_context rho (Γ ,,, rho_ctx_over Γ Γ') [] mfix) x)) *)
  (*                        mfix Γ *)
  (*                        (fix_context mfix)). *)
  (*            simpl in *. *)

  (*            f_equal. f_equal. *)
  (*            { solve_all. noconf H. *)
  (*              unfold map_def; destruct x; simpl in *. f_equal; auto. rewrite - H2. *)
  (*              rewrite fix_context_length. eauto. } *)

  (*            rewrite cofix_subst_length. *)
  (*            eapply nth_error_all in Heq. 2:eapply H. simpl in Heq. *)
  (*            noconf Heq. rewrite H3. reflexivity. *)
  (*            intros. simpl. f_equal. unfold map_fix. *)
  (*            rewrite !map_map_compose. solve_all. noconf H. *)
  (*            unfold compose. *)
  (*            unfold map_def; simpl; f_equal; simpl. now rewrite map_length fix_context_length. *)
  (*         -- simpl. f_equal; eauto. *)
  (*            rewrite !lift_mkApps. simpl. *)
  (*            f_equal; eauto. f_equal. eauto. *)

  (*       + epose proof (decompose_app_lift #|Δ| #|Γ'| _ _ _ Heq). *)
  (*         apply decompose_app_inv in Heq. subst t. rewrite H. *)
  (*         destruct t0; simpl in *; try discriminate; try contradiction; try congruence. *)
  (*         elim leb_spec_Set; intros; auto; try congruence. *)

  (*     - todo. (* Fix *) *)
  (*     - f_equal. unfold map_fix. *)
  (*       rewrite -> ?map_map_compose, ?compose_on_snd, ?compose_map_def, *)
  (*       ?map_length, ?Nat.add_assoc. cbn in *. *)
  (*       assert (All (fun x => *)
  (*                      (∀ Δ, lift #|Δ| #|Γ'| (rho (Γ ,,, rho_ctx_over Γ Γ') (dtype x)) = *)
  (*                 rho (Γ ,,, Δ ,,, lift_context #|Δ| 0 (rho_ctx_over Γ Γ')) *)
  (*                     (lift #|Δ| #|Γ'| (dtype x)))) m). *)
  (*       { solve_all. } *)
  (*       assert (rho_ctx_over (Γ ,,, rho_ctx_over Γ Γ') (fix_context m) = *)
  (*               fold_fix_context rho (Γ ,,, rho_ctx_over Γ Γ') [] m). *)
  (*       { rewrite - fold_fix_context_over'. *)
  (*         solve_all. *)
  (*         specialize (a0 (Γ ,,, rho_ctx_over Γ Γ') Δ0 [] eq_refl). *)
  (*         simpl in a0. now rewrite a0. reflexivity. } *)
  (*       rewrite - H0. *)

  (*       eapply tfix_map_spec. eauto. simpl; intros. *)
  (*       apply (H1 Γ Δ Γ' eq_refl). *)
  (*       intros. simpl in *. *)

  (*       specialize (H1 Γ Δ (Γ' ,,, fix_context m)) as H'. *)
  (*       rewrite rho_ctx_over_app app_context_assoc in H'. *)
  (*       rewrite -H0 in H'. *)
  (*       specialize (H' eq_refl). *)
  (*       rewrite app_context_length fix_context_length in H'. *)
  (*       rewrite lift_context_app app_context_assoc in H'. unfold compose. *)
  (*       rewrite H'. rewrite rho_ctx_over_length Nat.add_0_r. *)
  (*       f_equal. f_equal. *)

  (*       (* The use of [lift0 n] in fix_context renders the commutation *)
  (*          with lifting unclear. *) *)
  (*       assert (lift_context #|Δ| #|Γ'| (rho_ctx_over (Γ ,,, rho_ctx_over Γ Γ') (fix_context m)) = *)
  (* rho_ctx_over (Γ ,,, Δ ,,, lift_context #|Δ| 0 (rho_ctx_over Γ Γ')) *)
  (*   (lift_context #|Δ| #|Γ'| (fix_context m))). *)
  (*       { clear -X. *)
  (*         induction X. simpl. reflexivity. *)
  (*         red in t0. *)
  (*         rewrite lift_context_snoc. simpl. *)
  (*         specialize (t0 Γ Δ (Γ' ,,, Γ0)). *)
  (*         rewrite -fold_ctx_over_eq in t0. *)
  (*         rewrite rho_ctx_over_app app_context_assoc in t0. specialize (t0 eq_refl). *)
  (*         rewrite -IHX. rewrite lift_context_snoc0. *)
  (*         unfold snoc. f_equal. unfold vass, lift_decl, map_decl. simpl. *)
  (*         rewrite rho_ctx_over_length. rewrite app_context_length in t0. *)
  (*         rewrite t0. rewrite lift_context_app Nat.add_0_r app_context_assoc *)
  (*                             rho_ctx_over_length. reflexivity. admit. } *)

  (*       rewrite H2. *)
  (*       clear x H1 H'. *)

  (*       rewrite - fold_fix_context_over'. *)
  (*       { eapply All_map. red in X0. *)
  (*         solve_all. unfold compose. simpl. intros. *)
  (*         specialize (a0 Γ Δ Γ' eq_refl) as a0'. *)
  (*         rewrite -a0'. *)
  (*         rewrite b. unfold app_context in *. admit. } *)
  (*       now rewrite lift_fix_context. *)
  (*   Admitted. *)

    (* Lemma rho_lift0 Γ Δ t : lift0 #|Δ| (rho Γ t) = rho (Γ ,,, Δ) (lift0 #|Δ| t). *)
    (* Proof. apply (rho_lift Γ Δ []). Qed. *)

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
      f_equal. f_equal. rewrite !lift_rename !rename_inst. lift_renaming.
      rewrite rho_lift0. auto.
      repeat f_equal. rewrite rho_lift0; auto.
    Qed.

    (* Lemma fold_fix_context_rho_ctx Γ m : *)
    (*   rho_ctx_over (rho_ctx Γ) (fix_context m) = *)
    (*   fold_fix_context rho (rho_ctx Γ) [] m. *)
    (* Proof. *)
    (*   rewrite <- fold_fix_context_over_acc; now rewrite ?app_nil_r. *)
    (* Qed. *)

    Definition fold_fix_context_alt Γ m :=
      mapi (fun k def => vass def.(dname) (lift0 k (rho Γ def.(dtype)))) m.

    Lemma fix_context_fold Γ m :
      fix_context (map (map_def (rho (rho_ctx Γ))
                                    (rho (rho_ctx Γ ,,, rho_ctx_over (rho_ctx Γ) (fix_context m)))) m) =
      rho_ctx_over (rho_ctx Γ) (fix_context m).
    Proof.
      unfold fix_context. rewrite mapi_map. simpl.
      rewrite fold_fix_context_rho_ctx; auto.
      rewrite fold_fix_context_rev_mapi. simpl.
      now rewrite app_nil_r.
    Qed.

    Lemma fix_context_map_fix Γ mfix :
      fix_context (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix) =
      rho_ctx_over (rho_ctx Γ) (fix_context mfix).
    Proof.
      rewrite - fix_context_fold.
      unfold map_fix. f_equal.
      f_equal. f_equal. now rewrite fix_context_fold.
    Qed.

    Lemma rho_ctx_over_rev_mapi {Γ m} :
      List.rev (mapi (λ (i : nat) (x : def term),
                      vass (dname x) (lift0 i (rho (rho_ctx Γ) (dtype x)))) m) =
      rho_ctx_over (rho_ctx Γ) (fix_context m).
    Proof.
      rewrite - fold_fix_context_rev.
      now rewrite fold_fix_context_rho_ctx.
    Qed.

    Lemma rho_fix_context_All2_local_env (Γ Γ' : context) (m : mfixpoint term) :
      All_local_env
        (on_local_decl
           (λ (Δ : context) (t : term), pred1_ctx Σ
                                                   (Γ' ,,, Δ)
                                                   (rho_ctx (Γ ,,, Δ))
                                         → pred1 Σ (Γ' ,,, Δ)
                                                 (rho_ctx (Γ ,,, Δ)) t
                                                 (rho (rho_ctx (Γ ,,, Δ)) t)))
        (fix_context m)
      → pred1_ctx Σ Γ' (rho_ctx Γ)
      → All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ' (rho_ctx Γ)))
                       (fix_context m)
                       (fix_context
                          (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] m)
                                   m)).
    Proof.
      intros X X1.
      rewrite - fold_fix_context_rho_ctx.
      rewrite fix_context_fold.
      revert X. generalize (fix_context m). intros c. induction 1.
      - constructor.
      - simpl. constructor.
        + apply IHX.
        + red. red in t0.
          red. rewrite rho_ctx_app in t0. apply t0.
          apply All2_local_env_app_inv; auto.
      - simpl.
        constructor.
        + apply IHX.
        + red in t1. intuition auto.
          rewrite rho_ctx_app in a, b0. red. split; eauto.
          * red. apply a. now apply All2_local_env_app_inv.
          * apply b0. now apply All2_local_env_app_inv.
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

    Lemma All2_local_env_pred_fix_ctx P (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) :
      All2_local_env
        (on_decl
           (on_decl_over (λ (Γ0 Γ'0 : context) (t t0 : term), P Γ'0 (rho_ctx Γ0) t0 (rho (rho_ctx Γ0) t)) Γ Γ'))
        (fix_context mfix0) (fix_context mfix1)
      → All2_local_env (on_decl (on_decl_over P Γ' (rho_ctx Γ))) (fix_context mfix1)
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

    Lemma All2_app_r {A} (P : A -> A -> Type) l l' r r' : All2 P (l ++ [r]) (l' ++ [r']) ->
                                                        (All2 P l l') * (P r r').
    Proof. induction l in l', r |- *. simpl. intros. destruct l'. simpl in *.
           depelim X; intuition auto.
           depelim X. destruct l'; depelim X.
           intros.
           depelim l'; depelim X. destruct l; depelim X.
           specialize (IHl _ _ X). intuition auto.
    Qed.

    Lemma All2_map_left {A B} (P : A -> A -> Type) l l' (f : B -> A) :
      All2 (fun x y => P (f x) y) l l' -> All2 P (map f l) l'.
    Proof. intros. rewrite - (map_id l'). eapply All2_map; eauto. Qed.

    Lemma All2_map_right {A B} (P : A -> A -> Type) l l' (f : B -> A) :
      All2 P l (map f l') ->  All2 (fun x y => P x (f y)) l l'.
    Proof.
      induction l in l' |- *. intros. depelim X. destruct l'; try discriminate.
      constructor.
      destruct l'; intros H; depelim H; try discriminate.
      specialize (IHl _ H). constructor; auto.
    Qed.

    Lemma mapi_rec_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) k l :
      mapi_rec g (mapi_rec f l k) k = mapi_rec (fun k x => g k (f k x)) l k.
    Proof.
      induction l in k |- *; simpl; auto. now rewrite IHl.
    Qed.

    Lemma mapi_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) l :
      mapi g (mapi f l) = mapi (fun k x => g k (f k x)) l.
    Proof. apply mapi_rec_compose. Qed.


    Lemma All2_refl_All {A} (P : A -> A -> Type) l : All2 P l l -> All (fun x => P x x) l.
    Proof.
      induction l; intros H; depelim H. constructor. constructor; auto.
    Qed.
    Lemma mapi_cst_map {A B} (f : A -> B) l : mapi (fun _ => f) l = map f l.
    Proof. unfold mapi. generalize 0. induction l; cbn; auto. intros. now rewrite IHl. Qed.

    Lemma All_All2_telescopei_gen (Γ Γ' Δ Δ' : context) (m m' : mfixpoint term) :
      #|Δ| = #|Δ'| ->
      All2
        (λ (x y : def term), (pred1 Σ Γ'
                                 (rho_ctx Γ)
                                 (dtype x)
                                 (rho (rho_ctx Γ) (dtype y))) * (dname x = dname y))%type m m' ->
      All2_local_env_over (pred1 Σ) Γ' (rho_ctx Γ) Δ (rho_ctx_over (rho_ctx Γ) Δ') ->
      All2_telescope_n (on_decl (pred1 Σ)) (λ n : nat, lift0 n)
                       (Γ' ,,, Δ) (rho_ctx (Γ ,,, Δ'))
                       #|Δ|
    (map (λ def : def term, vass (dname def) (dtype def)) m)
      (map (λ def : def term, vass (dname def) (rho (rho_ctx Γ) (dtype def))) m').
    Proof.
      intros Δlen.
      induction 1 in Δ, Δ', Δlen |- *; cbn. constructor.
      intros. destruct r. rewrite e. constructor.
      red. rewrite rho_ctx_app.
      assert (#|Δ| = #|rho_ctx_over (rho_ctx Γ) Δ'|) by now rewrite rho_ctx_over_length.
      rewrite {2}H. eapply weakening_pred1_pred1; eauto.
      specialize (IHX (vass (dname y) (lift0 #|Δ| (dtype x)) :: Δ)
                      (vass (dname y) (lift0 #|Δ'| (dtype y)) :: Δ')%list).
      assert (#|Δ| = #|rho_ctx_over (rho_ctx Γ) Δ'|) by now rewrite rho_ctx_over_length.
      rewrite {2}H.
      rewrite rho_lift0.
      unfold snoc. forward IHX. simpl. lia.
      forward IHX. cbn. constructor. apply X0.
      red. red.
      assert (#|Δ'| = #|rho_ctx_over (rho_ctx Γ) Δ'|) by now rewrite rho_ctx_over_length.
      rewrite H0.
      rewrite - (rho_lift (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) Δ') []). simpl.
      eapply weakening_pred1_pred1; eauto.
      rewrite rho_ctx_app in IHX.
      simpl in IHX. rewrite -H. rewrite {2}Δlen.
      rewrite rho_ctx_app. apply IHX.
    Qed.

    Lemma All_All2_telescopei (Γ Γ' : context) (m m' : mfixpoint term) :
      All2 (λ (x y : def term), (pred1 Σ Γ' (rho_ctx Γ) (dtype x) (rho (rho_ctx Γ) (dtype y))) *
                                (dname x = dname y))%type m m' ->
      All2_telescope_n (on_decl (pred1 Σ)) (λ n : nat, lift0 n)
                       Γ' (rho_ctx Γ)
                       0
                       (map (λ def : def term, vass (dname def) (dtype def)) m)
                       (map (λ def : def term, vass (dname def) (rho (rho_ctx Γ) (dtype def))) m').
    Proof.
      specialize (All_All2_telescopei_gen Γ Γ' [] [] m m'). simpl.
      intros. specialize (X eq_refl X0). forward X. constructor.
      apply X.
    Qed.

    Lemma rho_All2_All_local_env :
      ∀ Γ Γ' : context, pred1_ctx Σ Γ (rho_ctx Γ') →
      ∀ Δ : context,
          All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ (rho_ctx Γ'))) Δ
                         (rho_ctx_over (rho_ctx Γ') Δ) ->
          All_local_env
            (on_local_decl
               (λ (Δ : context) (t : term), pred1_ctx Σ (Γ ,,, Δ) (rho_ctx (Γ' ,,, Δ))
                                             → pred1 Σ (Γ ,,, Δ)
                                                     (rho_ctx (Γ' ,,, Δ)) t
                                                     (rho (rho_ctx (Γ' ,,, Δ)) t))) Δ.
    Proof.
      intros.
      induction Δ; simpl; try constructor.
      destruct a as [? [?|] ?].
      - depelim X0.
        constructor; auto.
        + red. red in p. destruct p.
          unfold on_decl_over in *. intuition pcuic.
          now rewrite rho_ctx_app.
        + red. red in p. destruct p.
          unfold on_decl_over in *. intuition pcuic.
          * now rewrite rho_ctx_app.
          * now rewrite rho_ctx_app.
      - depelim X0. constructor; eauto.
        red. do 2 red in p. intros.
        now rewrite rho_ctx_app.
    Qed.

    Lemma pred1_rho_fix_context (Γ Γ' : context) (m : mfixpoint term) :
      pred1_ctx Σ Γ' (rho_ctx Γ) ->
      All2 (on_Trel (pred1 Σ Γ' (rho_ctx Γ)) dtype) m
           (map_fix rho (rho_ctx Γ)
                    (fold_fix_context rho (rho_ctx Γ) [] m) m) ->
      All2_local_env
        (on_decl (on_decl_over (pred1 Σ) Γ' (rho_ctx Γ)))
        (fix_context m)
        (fix_context (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] m) m)).
    Proof.
      intros HΓ a.
      eapply rho_fix_context_All2_local_env; eauto.
      rewrite - fold_fix_context_rho_ctx in a.
      unfold map_fix in a.
      eapply All2_map_right in a.
      eapply All2_refl_All in a. simpl.
      eapply rho_All2_All_local_env; eauto.
      rewrite fold_fix_context_rho_ctx.
      rewrite fold_fix_context_rev_mapi.
      unfold fix_context. rewrite app_nil_r.
      eapply local_env_telescope.
      cbn.
      rewrite - (mapi_compose
                   (fun n decl => lift_decl n 0 decl)
                   (fun n def => vass (dname def) (dtype def))).
      rewrite - (mapi_compose
                   (fun n decl => lift_decl n 0 decl)
                   (fun n def => vass (dname def) (rho (rho_ctx Γ) (dtype def)))).
      eapply All2_telescope_mapi.
      rewrite !mapi_cst_map.
      eapply All_All2_telescopei; eauto. eapply All_All2; eauto.
    Qed.

    Lemma pred1_rho_fix_context_2 (Γ Γ' : context) (m m' : mfixpoint term) :
      pred1_ctx Σ Γ' (rho_ctx Γ) ->
      All2 (on_Trel_eq (pred1 Σ Γ' (rho_ctx Γ)) dtype dname) m
           (map_fix rho (rho_ctx Γ)
                    (fold_fix_context rho (rho_ctx Γ) [] m') m') ->
      All2_local_env
        (on_decl (on_decl_over (pred1 Σ) Γ' (rho_ctx Γ)))
        (fix_context m)
        (fix_context (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] m') m')).
    Proof.
      intros HΓ a.
      rewrite - fold_fix_context_rho_ctx in a.
      unfold map_fix in a.
      eapply All2_map_right in a.
      rewrite - fold_fix_context_rho_ctx.
      unfold fix_context. unfold map_fix.
      eapply local_env_telescope.
      cbn.
      rewrite - (mapi_compose
                   (fun n decl => lift_decl n 0 decl)
                   (fun n def => vass (dname def) (dtype def))).
      rewrite mapi_map. simpl.
      rewrite - (mapi_compose
                   (fun n decl => lift_decl n 0 decl)
                   (fun n def => vass (dname def) (rho (rho_ctx Γ) (dtype def)))).
      eapply All2_telescope_mapi.
      rewrite !mapi_cst_map.
      eapply All_All2_telescopei; eauto.
    Qed.

    Lemma fold_fix_context_id_rec Γ Δ m :
      fold_fix_context (fun _ t => t) Γ Δ m =
      List.rev (mapi_rec (λ (i : nat) (d : def term), vass (dname d) ((lift0 i) (dtype d))) m #|Δ|) ++ Δ.
    Proof.
      induction m in Δ |- *. simpl. auto. simpl. rewrite IHm. simpl.
      now rewrite - app_assoc.
    Qed.

    Lemma fold_fix_context_id Γ m :
      fold_fix_context (fun _ t => t) Γ [] m = fix_context m.
    Proof.
      now rewrite fold_fix_context_id_rec app_nil_r.
    Qed.

    Lemma fold_ctx_over_id Γ Δ : fold_ctx_over (fun _ t => t) Γ Δ = Δ.
    Proof. induction Δ; simpl; auto. destruct a as [? [?|] ?].
           now rewrite IHΔ.
           now rewrite IHΔ.
    Qed.

    Lemma rho_triangle Γ t :
      let Γ' := rho_ctx Γ in
      pred1_ctx Σ Γ Γ' ->
      pred1 Σ Γ Γ' t (rho Γ' t).
    Proof.
      revert Γ t. refine (term_forall_ctx_list_ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
                    simpl; !intros; rename_all_hyps.
      all:eauto 2 with pcuic.

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
          injection Heq'' as <- <-. destruct (eq_ind_spec i ind). subst i.
          econstructor; auto.
          constructor; pcuic.
        -- (* Case CoFix *)
          apply decompose_app_inv in Heq.
          subst t0. simpl.
          rewrite rho_mkApps in forall_z0 |- *; auto.
          eapply pred1_mkApps_tCoFix_inv in forall_z0 as [mfix1 [idx1 [[? ?] ?]]].
          simpl in e. solve_discr.
          rewrite decompose_app_mkApps; auto.
          simpl. unfold unfold_cofix.
          rewrite nth_error_map.
          destruct (nth_error mfix idx) eqn:Heq.
          simpl.
          econstructor; eauto.
          --- eapply All2_prop2_eq_split in a. intuition.
              now eapply pred1_rho_fix_context.
          --- unfold unfold_cofix.
              rewrite /unfold_cofix nth_error_map Heq /=. reflexivity.
          --- simpl. eapply pred_case; eauto.
              eapply pred_mkApps; eauto. eapply pred_cofix_congr; eauto.
              eapply All2_prop2_eq_split in a. intuition.
              now eapply pred1_rho_fix_context.

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
          destruct (eq_ind_spec ind ind0). subst ind.
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
          destruct (nth_error mfix idx) eqn:Hnth; simpl.
          econstructor; eauto.
          --- eapply All2_prop2_eq_split in a. intuition.
              now eapply pred1_rho_fix_context.
          --- unfold unfold_cofix.
              rewrite /unfold_cofix nth_error_map Hnth /=. reflexivity.
          --- simpl. eapply pred_proj_congr; eauto.
              eapply pred_mkApps; eauto. eapply pred_cofix_congr; eauto.
              eapply All2_prop2_eq_split in a. intuition.
              now eapply pred1_rho_fix_context.

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
        apply rho_All_All2_local_env. auto.
        now rewrite fold_fix_context_id.
        rewrite rho_ctx_app in b.
        rewrite - fold_fix_context_rho_ctx.
        rewrite !fix_context_fold.
        now rewrite fold_fix_context_id in b.

      - assert (All_local_env
                  (on_local_decl
                     (λ (Δ : context) (t : term), pred1_ctx Σ (Γ ,,, Δ) (rho_ctx (Γ ,,, Δ))
                                                  → pred1 Σ (Γ ,,, Δ) (rho_ctx (Γ ,,, Δ)) t
                                                          (rho (rho_ctx (Γ ,,, Δ)) t)))
                  (fix_context m)).
        { red in X0. eapply All_local_env_impl. eauto.
          simpl; intros. red in X2 |- *.
          rewrite !fold_ctx_over_id in X2. auto. } clear X.
        rewrite fold_fix_context_id in X0.

        econstructor; eauto.
        apply rho_fix_context_All2_local_env; auto.
        rewrite -{4}(map_id m).
        eapply All2_map.
        solve_all.
        red. split; simpl; auto.
        red. simpl.
        forward b. rewrite rho_ctx_app.
        apply All2_local_env_app_inv; auto.
        apply rho_All_All2_local_env; auto.
        rewrite rho_ctx_app in b.
        rewrite - fold_fix_context_rho_ctx.
        now rewrite !fix_context_fold.
    Qed.

    Lemma rho_triangle_ctx Γ :
      pred1_ctx Σ Γ (rho_ctx Γ).
    Proof.
      induction Γ; simpl; try constructor.
      destruct a as [? [?|] ?]; simpl; constructor;
        rewrite ?app_context_nil_l; simpl; eauto using rho_triangle.
    Qed.

    Lemma substitution_pred1 Γ Δ Γ' Δ' s s' N N' :
      psubst Σ Γ Γ' s s' Δ Δ' ->
      pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') N N' ->
      pred1 Σ Γ Γ' (subst s 0 N) (subst s' 0 N').
    Proof.
      intros redM redN.
      pose proof (substitution_let_pred1 Σ Γ Δ [] Γ' Δ' [] s s' N N' wfΣ) as H.
      assert (#|Γ| = #|Γ'|).
      { eapply psubst_length in redM. intuition auto.
        apply pred1_pred1_ctx in redN. eapply All2_local_env_length in redN.
        rewrite !app_context_length in redN. lia. }
      forward H by auto.
      forward H by pcuic.
      specialize (H eq_refl). forward H.
      apply pred1_pred1_ctx in redN; pcuic.
      eapply All2_local_env_app in redN; auto.
      destruct redN. apply a0.
      simpl in H. now apply H.
    Qed.

    Lemma All2_mix {A} {P Q : A -> A -> Type} {l l'} :
      All2 P l l' -> All2 Q l l' -> All2 (fun x y => (P x y * Q x y))%type l l'.
    Proof.
      induction 1; intros HQ; depelim HQ; constructor; eauto.
    Qed.

    Lemma All2_mix_inv {A} {P Q : A -> A -> Type} {l l'} :
      All2 (fun x y => (P x y * Q x y))%type l l' ->
      (All2 P l l' * All2 Q l l').
    Proof.
      induction 1; split; constructor; intuition eauto.
    Qed.

    Definition swap {A B : Type} (x : A * B) : B * A :=
      (snd x, fst x).

    Lemma All2_local_env_sym P Γ Γ' Δ Δ' :
      All2_local_env (on_decl (on_decl_over (fun Γ Γ' t t' => P Γ' Γ t' t) Γ' Γ)) Δ' Δ ->
      All2_local_env (on_decl (on_decl_over P Γ Γ')) Δ Δ'.
    Proof.
      induction 1; constructor; eauto.
    Qed.

    Lemma All2_local_env_over_impl {P Q : context -> context -> term -> term -> Type}
          {Γ Γ' par par'} :
      All2_local_env (on_decl (on_decl_over P Γ Γ')) par par' ->
      (forall par par' x y, P (Γ ,,, par) (Γ' ,,, par') x y -> Q (Γ ,,, par) (Γ' ,,, par') x y) ->
      All2_local_env (on_decl (on_decl_over Q Γ Γ')) par par'.
    Proof.
      intros H aux.
      induction H; constructor. auto. red in p. apply aux, p.
      apply IHAll2_local_env. red. split.
      apply aux. apply p. apply aux. apply p.
    Defined.

    Lemma All2_local_env_over_impl_f_g {P Q : context -> context -> term -> term -> Type}
          f g {Γ Γ' par par'} :
      All2_local_env (on_decl (on_decl_over P Γ (f Γ'))) par par' ->
      (forall par par' x y, P (Γ ,,, par) (f Γ' ,,, par') x y ->
                       Q (Γ ,,, par)
                         (f (Γ' ,,, par')) x (g (Γ' ,,, par') y)) ->
      All2_local_env (on_decl (on_decl_over (fun Γ Γ' t t' => Q Γ (f Γ') t (g Γ' t')) Γ Γ')) par par'.
    Proof.
      intros H aux.
      induction H; constructor. auto. red in p. red in p |- *. red. apply aux, p.
      apply IHAll2_local_env. red. split.
      apply aux. apply p. apply aux. apply p.
    Defined.

    Hint Extern 40 => progress unfold on_Trel, on_Trel_eq, on_decl, on_decl_over in * : pcuic.

    Lemma All2_rev (A : Type) (P : A -> A → Type) (l l' : list A) :
      All2 P l l' → All2 P (List.rev l) (List.rev l').
    Proof.
      induction 1. constructor.
      simpl. eapply All2_app; auto.
    Qed.

    Lemma weakening_pred1_lengths (Γ Δ Γ' Δ' : context)
          (M N : term) m n :
      m = #|Γ'| -> n = #|Δ'| ->
      All2_local_env_over
        (pred1 Σ) Γ Δ Γ' Δ'
      → pred1 Σ Γ Δ M N
      → pred1 Σ
              (Γ ,,, Γ')
              (Δ ,,, Δ')
              ((lift0 m) M)
              ((lift0 n) N).
    Proof.
      intros -> ->. now eapply weakening_pred1_pred1.
    Qed.


    Lemma wf_fix_subst Γ Γ' mfix0 mfix1 :
      #|mfix0| = #|mfix1| ->
      pred1_ctx Σ Γ Γ' ->
      All2_local_env (on_decl (on_decl_over (pred1 Σ) Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                    (λ x0 : def term, (dname x0, rarg x0)) (pred1 Σ) mfix0 mfix1 ->
      psubst Σ Γ Γ' (cofix_subst mfix0) (cofix_subst mfix1)
             (fix_context mfix0) (fix_context mfix1).
    Proof.
      intros Hlen Hred Hctxs a0. pose proof Hctxs as Hctxs'.
      pose proof a0 as a0'. apply All2_rev in a0'.
      revert Hctxs.
      unfold cofix_subst, fix_context. simpl.
      revert a0'. rewrite -Hlen -(@List.rev_length _ mfix0).
      rewrite !rev_mapi. unfold mapi.
      assert (#|mfix0| >= #|List.rev mfix0|) by (rewrite List.rev_length; lia).
      assert (#|mfix1| >= #|List.rev mfix1|) by (rewrite List.rev_length; lia).
      assert (He :0 = #|mfix0| - #|List.rev mfix0|) by (rewrite List.rev_length; auto with arith).
      assert (He' :0 = #|mfix1| - #|List.rev mfix1|) by (rewrite List.rev_length; auto with arith).
      rewrite {2 6}He {3 6}He'. clear He He'. revert H H0.
      generalize (List.rev mfix0) (List.rev mfix1).
      intros l l' Hlen' Hlen'' H. induction H. simpl. constructor.
      simpl.
      simpl in *.
      replace (S (#|mfix0| - S #|l|)) with (#|mfix0| - #|l|) by lia.
      replace (S (#|mfix1| - S #|l'|)) with (#|mfix1| - #|l'|) by lia.
      assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l|)) = #|l|) by lia.
      assert ((Nat.pred #|mfix1| - (#|mfix1| - S #|l'|)) = #|l'|) by lia.
      rewrite H0 H1.
      intros. depelim Hctxs. red in o. rewrite -x.
      constructor. unfold mapi in IHAll2.
      forward IHAll2 by lia.
      forward IHAll2 by lia.
      apply IHAll2. apply Hctxs.
      clear IHAll2. destruct r.
      destruct o1.
      simpl in *.
      eapply (weakening_pred1_lengths Γ Γ' _ _); eauto.
      now rewrite mapi_rec_length.
      now rewrite mapi_rec_length.
      econstructor. eauto. eauto.
      eauto.
    Qed.

    Lemma wf_rho_fix_subst Γ Γ' mfix0 mfix1 :
      #|mfix0| = #|mfix1| ->
      pred1_ctx Σ Γ' (rho_ctx Γ) ->
      All2_local_env
         (on_decl
            (on_decl_over
               (λ (Γ Γ' : context) (t t0 : term), pred1 Σ Γ' (rho_ctx Γ) t0 (rho (rho_ctx Γ) t)) Γ
               Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
         (λ x : def term, (dname x, rarg x))
         (λ (Γ Γ' : context) (x y : term), (pred1 Σ Γ Γ' x y *
                                            pred1 Σ Γ' (rho_ctx Γ) y (rho (rho_ctx Γ) x))%type)
         mfix0 mfix1 ->
      psubst Σ Γ' (rho_ctx Γ) (cofix_subst mfix1) (map (rho (rho_ctx Γ)) (cofix_subst mfix0))
             (fix_context mfix1) (rho_ctx_over (rho_ctx Γ) (fix_context mfix0)).
    Proof.
      intros Hlen Hred Hctxs a0. pose proof Hctxs as Hctxs'.
      pose proof a0 as a0'. apply All2_rev in a0'.
      revert Hctxs.
      unfold cofix_subst, fix_context. simpl.
      revert a0'. rewrite -Hlen -(@List.rev_length _ mfix0).
      rewrite !rev_mapi. unfold mapi.
      assert (#|mfix0| >= #|List.rev mfix0|) by (rewrite List.rev_length; lia).
      assert (#|mfix1| >= #|List.rev mfix1|) by (rewrite List.rev_length; lia).
      assert (He :0 = #|mfix0| - #|List.rev mfix0|) by (rewrite List.rev_length; auto with arith).
      assert (He' :0 = #|mfix1| - #|List.rev mfix1|) by (rewrite List.rev_length; auto with arith).
      rewrite {2 6}He {3 6}He'. clear He He'. revert H H0.
      assert (#|List.rev mfix0| = #|List.rev mfix1|) by (rewrite !List.rev_length; lia).
      revert H.
      generalize (List.rev mfix0) (List.rev mfix1).
      intros l l' Heqlen Hlen' Hlen'' H. induction H. simpl. constructor.
      simpl.
      simpl in *.
      replace (S (#|mfix0| - S #|l|)) with (#|mfix0| - #|l|) by lia.
      replace (S (#|mfix1| - S #|l'|)) with (#|mfix1| - #|l'|) by lia.
      rewrite -Hlen.
      assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l|)) = #|l|) by lia.
      assert ((Nat.pred #|mfix0| - (#|mfix0| - S #|l'|)) = #|l'|) by lia.
      rewrite H0 H1.
      intros. depelim Hctxs. red in p. rewrite -x.
      constructor. unfold mapi in IHAll2.
      forward IHAll2 by lia.
      forward IHAll2 by lia.
      forward IHAll2 by lia. rewrite -Hlen in IHAll2.
      apply IHAll2; clear IHAll2. apply Hctxs; clear Hctxs.
      clear IHAll2 Hctxs. destruct r.
      destruct o0. red in o, o0. destruct o, o0.
      simpl in *. red in p. noconf Heqlen. simpl in H.
      rewrite H in p |- *. rewrite rho_ctx_app in p. apply p.
      econstructor. eauto. clear Hctxs p IHAll2.
      rewrite -fold_fix_context_rho_ctx.
      eapply All2_local_env_pred_fix_ctx. eapply Hctxs'.
      eapply All2_mix. rewrite -fold_fix_context_rho_ctx.
      all:clear IHAll2 Hctxs H p r.
      { eapply All2_mix_inv in a0. destruct a0.
        eapply All2_sym. unfold on_Trel.
        eapply All2_mix_inv in a. destruct a.
        eapply All2_map_left. simpl. auto. }
      { eapply All2_mix_inv in a0. destruct a0.
        eapply All2_sym. unfold on_Trel.
        eapply All2_mix_inv in a0. destruct a0.
        eapply All2_mix_inv in a0. destruct a0.
        eapply All2_mix.
        rewrite -fold_fix_context_rho_ctx.
        rewrite fix_context_map_fix. simpl.
        rewrite rho_ctx_app in a2. unfold on_Trel.
        eapply All2_map_left. simpl. eapply a2.
        eapply All2_map_left. simpl. solve_all. }
    Qed.

    Lemma rho_cofix_subst Γ mfix :
      cofix_subst (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ) (fix_context mfix)) mfix)
      = (map (rho (rho_ctx Γ)) (cofix_subst mfix)).
    Proof.
      unfold cofix_subst. unfold map_fix at 2. rewrite !map_length.
      induction #|mfix|. reflexivity. simpl.
      rewrite - fold_fix_context_rho_ctx. f_equal. apply IHn.
    Qed.

    Lemma triangle Γ Δ t u :
                             let Pctx :=
                                 fun (Γ Δ : context) => pred1_ctx Σ Δ (rho_ctx Γ) in
                             pred1 Σ Γ Δ t u -> pred1 Σ Δ (rho_ctx Γ) u (rho (rho_ctx Γ) t).
    Proof with solve_discr.
      intros Pctx H. revert Γ Δ t u H.
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
        eapply All2_prop2_eq_split in X3. intuition.
        eapply All2_nth_error_Some_right in Heq; eauto.
        destruct Heq as [t' [Ht' Hrel]]. rewrite Ht'. simpl.
        eapply pred_case. eauto. eapply pred_mkApps.
        red in Hrel. destruct Hrel.
        rewrite rho_ctx_app in p2.
        rewrite - fold_fix_context_rho_ctx.
        eapply substitution_pred1; eauto.
        rewrite rho_cofix_subst.
        { eapply wf_rho_fix_subst; eauto.
          now eapply All2_length in b.
          eapply All2_mix. eauto.
          eapply All2_mix. eauto.
          eauto. }
        eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. intuition eauto.
        eapply All2_sym, All2_map_left, All2_impl; eauto. simpl. unfold on_Trel_eq, on_Trel in *.
        intuition eauto.

      - simpl.
        destruct p as [[ind pars] arg].
        rewrite decompose_app_mkApps. auto.
        rewrite rho_mkApps // decompose_app_mkApps // /=.
        unfold unfold_cofix in heq_unfold_cofix |- *.
        destruct nth_error eqn:Heq; noconf heq_unfold_cofix.
        eapply All2_nth_error_Some_right in Heq; eauto.
        destruct Heq as [t' [Hnth Hrel]]. destruct Hrel as [[Hty Hrhoty] [[Hreleq0 Hreleq1] Heq]].
        unfold map_fix. rewrite nth_error_map Hnth /=.
        econstructor. eapply pred_mkApps; eauto.
        rewrite - fold_fix_context_rho_ctx.
        rewrite rho_ctx_app in Hreleq1.
        eapply substitution_pred1; eauto.
        rewrite rho_cofix_subst.
        { eapply wf_rho_fix_subst; eauto.
          now eapply All2_length in X3. }
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
          destruct (eq_ind_spec i ind). subst ind.
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
          unfold unfold_cofix. rewrite nth_error_map.
          assert (All2 (on_Trel eq dname) mfix'
                       (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] mfix) mfix)).
          { eapply All2_impl; [eapply b0|]; pcuic. intros.
            red in X1. now noconf X1. }
          pose proof (All2_mix a1 X1).
          eapply pred1_rho_fix_context_2 in X2; pcuic.
          rewrite - fold_fix_context_rho_ctx in X2.
          rewrite fix_context_map_fix in X2.
          eapply rho_All_All2_local_env_inv in X2; pcuic.
          rewrite - fold_fix_context_rho_ctx in a1.

          destruct nth_error eqn:Heq. simpl.
          * (* CoFix unfolding *)
            pose proof Heq.
            eapply All2_nth_error_Some in Heq; eauto. destruct Heq; intuition auto.

            eapply pred_cofix_case with (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ)
                                                                               (fix_context mfix)) mfix)
                                        (rarg d); pcuic.

            --- eapply All2_local_env_pred_fix_ctx; eauto.
                eapply All2_prop2_eq_split in a. intuition auto.
                eapply All2_local_env_sym.
                pcuic.

            --- eapply All2_mix; pcuic.
                rewrite - fold_fix_context_rho_ctx in b1.
                eapply All2_mix. eauto.
                now rewrite - fold_fix_context_rho_ctx in b0.
            --- unfold unfold_cofix.
                rewrite nth_error_map.
                rewrite H. simpl. f_equal. f_equal.
                unfold map_fix.
                rewrite fold_fix_context_rho_ctx. auto.
            --- eapply All2_map_right. rewrite map_id. apply All2_sym.
                eapply All2_map_left. eapply All2_impl; eauto.
                unfold on_Trel_eq, on_Trel in *.
                intros. intuition pcuic.

          * eapply pred_case; eauto.
            eapply pred_mkApps. constructor. pcuic.
            --- rewrite - fold_fix_context_rho_ctx.
                eapply All2_local_env_pred_fix_ctx.
                eapply All2_prop2_eq_split in a. intuition auto.
                eapply All2_local_env_sym.
                pcuic.

            --- eapply All2_mix; pcuic.
                rewrite - fold_fix_context_rho_ctx in b1.
                now rewrite - fold_fix_context_rho_ctx.
                eapply All2_mix; pcuic.
            --- pcuic.
            --- eapply All2_sym, All2_map_left, All2_impl; eauto.
                unfold on_Trel_eq, on_Trel in *.
                intros. intuition pcuic.

        + apply decompose_app_inv in Heq. subst c0.
          assert (All2 (on_Trel_eq (pred1 Σ Γ' (rho_ctx Γ)) snd fst) brs1
                       (map (λ x : nat * term, (fst x, rho (rho_ctx Γ) (snd x))) brs0)).
          { eapply All2_sym, All2_map_left, All2_impl; eauto.
            unfold on_Trel_eq, on_Trel in *.
            intros. intuition pcuic. }
          destruct t; try discriminate; simpl; pcuic.

      - (* Proj *)
        simpl.
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
          destruct X0.
          unfold unfold_cofix. rewrite nth_error_map.
          eapply All2_prop2_eq_split in a1. intuition auto.
          assert (All2 (on_Trel eq dname) mfix'
                       (map_fix rho (rho_ctx Γ) (fold_fix_context rho (rho_ctx Γ) [] mfix) mfix)).
          { eapply All2_impl; [eapply b|]; pcuic. intros.
            red in X0. now noconf X0. }
          pose proof (All2_mix a1 X0) as X2.
          eapply pred1_rho_fix_context_2 in X2; pcuic.
          rewrite - fold_fix_context_rho_ctx in X2.
          rewrite fix_context_map_fix in X2.
          eapply rho_All_All2_local_env_inv in X2; pcuic.
          rewrite - fold_fix_context_rho_ctx in a1.
          intuition auto.
          destruct nth_error eqn:Heq. simpl.
          (* Proj cofix *)
          * (* CoFix unfolding *)
            pose proof Heq.
            eapply All2_nth_error_Some in Heq; eauto. destruct Heq; intuition auto.

            eapply pred_cofix_proj with (map_fix rho (rho_ctx Γ) (rho_ctx_over (rho_ctx Γ)
                                                                               (fix_context mfix)) mfix)
                                        (rarg d); pcuic.

            --- eapply All2_local_env_pred_fix_ctx; eauto.
                eapply All2_prop2_eq_split in a. intuition auto.
                eapply All2_local_env_sym.
                pcuic.

            --- eapply All2_mix; pcuic.
                rewrite - fold_fix_context_rho_ctx in b0.
                eapply All2_mix. eauto.
                now rewrite - fold_fix_context_rho_ctx in b.
            --- unfold unfold_cofix.
                rewrite nth_error_map.
                rewrite H. simpl. f_equal. f_equal.
                unfold map_fix.
                rewrite fold_fix_context_rho_ctx. auto.

          * eapply pred_proj_congr; eauto.

        + eapply decompose_app_inv in Heq. subst c.
          destruct t; noconf d; econstructor; eauto.

      - simpl.
        rewrite - fold_fix_context_rho_ctx.
        constructor; eauto.
        now eapply All2_local_env_pred_fix_ctx. red. red in X3.
        eapply All2_sym, All2_map_left, All2_impl; eauto.
        simpl. unfold on_Trel_eq, on_Trel; intuition pcuic.
        rewrite rho_ctx_app in b. now rewrite fix_context_map_fix.

      - simpl.
        rewrite - fold_fix_context_rho_ctx.
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

  Ltac apply_hyp :=
    match reverse goal with
    | [ H : forall _ r, pred1 _ _ _ ?s _ -> _, H' : pred1 _ _ _ ?s _ |- _ ] =>
      let target := fresh "v" in specialize (H _ _ H') as [target [? ?]]
    end.

  (* The confluence theorem in terms of the triangle operator. *)

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