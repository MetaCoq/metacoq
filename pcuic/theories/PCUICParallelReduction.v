(* Distributed under the terms of the MIT license.   *)
Require Import ssreflect ssrbool.
From MetaCoq Require Import LibHypsNaming.
From Equations Require Import Equations.
From Coq Require Import Bool String List Program BinPos Compare_dec Omega String Lia.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICSize
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICReduction PCUICWeakening PCUICSubstitution.

(* Type-valued relations. *)
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Local Set Keyed Unification.
Set Asymmetric Patterns.

Derive NoConfusion for term.
Derive Subterm for term.
Derive Signature NoConfusion for All All2.

Lemma size_lift n k t : size (lift n k t) = size t.
Proof.
  revert n k t.
  fix size_list 3.
  destruct t; simpl; rewrite ?list_size_map_hom; try lia.
  elim leb_spec_Set; simpl; auto. intros. auto.
  now rewrite !size_list.
  now rewrite !size_list.
  now rewrite !size_list.
  now rewrite !size_list.
  intros.
  destruct x. simpl. now rewrite size_list.
  now rewrite !size_list.
  now rewrite !size_list.
  unfold mfixpoint_size.
  rewrite list_size_map_hom. intros.
  simpl. destruct x. simpl. unfold def_size. simpl.
  now rewrite !size_list.
  reflexivity.
  unfold mfixpoint_size.
  rewrite list_size_map_hom. intros.
  simpl. destruct x. unfold def_size; simpl.
  now rewrite !size_list.
  reflexivity.
Qed.

Require Import RelationClasses Arith.

Arguments All {A} P%type _.

Lemma All_pair {A} (P Q : A -> Type) l :
  All (fun x => P x * Q x)%type l <~> (All P l * All Q l).
Proof.
  split. induction 1; intuition auto.
  move=> [] Hl Hl'. induction Hl; depelim Hl'; intuition auto.
Qed.

Definition on_local_decl (P : context -> term -> Type)
           (Γ : context) (t : term) (T : option term) :=
  match T with
  | Some T => (P Γ t * P Γ T)%type
  | None => P Γ t
  end.

Lemma term_forall_ctx_list_ind :
  forall (P : context -> term -> Type),

    (forall Γ (n : nat), P Γ (tRel n)) ->
    (forall Γ (i : ident), P Γ (tVar i)) ->
    (forall Γ (n : nat) (l : list term), All (P Γ) l -> P Γ (tEvar n l)) ->
    (forall Γ s, P Γ (tSort s)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tProd n t t0)) ->
    (forall Γ (n : name) (t : term), P Γ t -> forall t0 : term, P (vass n t :: Γ) t0 -> P Γ (tLambda n t t0)) ->
    (forall Γ (n : name) (t : term),
        P Γ t -> forall t0 : term, P Γ t0 -> forall t1 : term, P (vdef n t t0 :: Γ) t1 -> P Γ (tLetIn n t t0 t1)) ->
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
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tFix m n)) ->
    (forall Γ (m : mfixpoint term) (n : nat),
        All_local_env (on_local_decl (fun Γ' t => P (Γ ,,, Γ') t)) (fix_context m) ->
        tFixProp (P Γ) (P (Γ ,,, fix_context m)) m -> P Γ (tCoFix m n)) ->
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
      + simpl. apply aux. red. lia.
      + simpl. split.
        * apply aux. red. lia.
        * apply aux; red; lia.
      + apply IHfix_context; unfold context_size; lia.
      + apply aux. red. lia. }
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
  apply auxl'. simpl. lia.
  red. apply All_pair. split; apply auxl; simpl; auto.
Defined.

Lemma simpl_subst' :
  forall N M n p k, k = List.length N -> p <= n -> subst N p (lift0 (k + n) M) = lift0 n M.
Proof. intros. subst k. rewrite simpl_subst_rec; auto. now rewrite Nat.add_0_r. lia. Qed.

(** All2 lemmas *)

(* Duplicate *)
Lemma All2_app {A} {P : A -> A -> Type} {l l' r r'} :
  All2 P l l' -> All2 P r r' ->
  All2 P (l ++ r) (l' ++ r').
Proof. induction 1; simpl; auto. Qed.

Definition All2_prop_eq Γ Γ' {A B} (f : A -> term) (g : A -> B) (rel : forall (Γ Γ' : context) (t t' : term), Type) :=
  All2 (on_Trel_eq (rel Γ Γ') f g).

Definition All2_prop Γ (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (rel Γ).

(* Scheme pred1_ind_all_first := Minimality for pred1 Sort Type. *)

Lemma All2_All2_prop {P Q : context -> context -> term -> term -> Type} {par par'} {l l' : list term} :
  All2 (P par par') l l' ->
  (forall x y, P par par' x y -> Q par par' x y) ->
  All2 (Q par par') l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel in *.
  apply aux; apply r. apply IHAll2.
Defined.

Lemma All2_All2_prop_eq {A B} {P Q : context -> context -> term -> term -> Type} {par par'}
      {f : A -> term} {g : A -> B} {l l' : list A} :
  All2 (on_Trel_eq (P par par') f g) l l' ->
  (forall x y, P par par' x y -> Q par par' x y) ->
  All2_prop_eq par par' f g Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel in *.
  split. apply aux; apply r. apply r. apply IHAll2.
Defined.

Definition All2_prop2_eq Γ Γ' Γ2 Γ2' {A B} (f g : A -> term) (h : A -> B)
           (rel : forall (Γ Γ' : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ Γ') f x y * on_Trel_eq (rel Γ2 Γ2') g h x y)%type.

Definition All2_prop2 Γ Γ' {A} (f g : A -> term)
           (rel : forall (Γ : context) (t t' : term), Type) :=
  All2 (fun x y => on_Trel (rel Γ) f x y * on_Trel (rel Γ') g x y)%type.

Lemma All2_All2_prop2_eq {A B} {P Q : context -> context -> term -> term -> Type} {par par' par2 par2'}
      {f g : A -> term} {h : A -> B} {l l' : list A} :
  All2_prop2_eq par par' par2 par2' f g h P l l' ->
  (forall par par' x y, P par par' x y -> Q par par' x y) ->
  All2_prop2_eq par par' par2 par2' f g h Q l l'.
Proof.
  intros H aux.
  induction H; constructor. unfold on_Trel in *. split.
  apply aux. destruct r. apply p. split. apply aux. apply r. apply r. apply IHAll2.
Defined.

(* Lemma All2_All2_prop2 {A} {P Q : context -> term -> term -> Type} {par par'} *)
(*       {f g : A -> term} {l l' : list A} : *)
(*   All2_prop2 par par' f g P l l' -> *)
(*   (forall par x y, P par x y -> Q par x y) -> *)
(*   All2_prop2 par par' f g Q l l'. *)
(* Proof. *)
(*   intros H aux. *)
(*   induction H; constructor. unfold on_Trel in *. split. *)
(*   apply aux. destruct r. apply p. apply aux. apply r. apply IHAll2. *)
(* Defined. *)

Section All2_local_env.

  Definition on_decl (P : context -> context -> term -> term -> Type)
             (Γ Γ' : context) (b : option (term * term)) (t t' : term) :=
    match b with
    | Some (b, b') => (P Γ Γ' b b' * P Γ Γ' t t')%type
    | None => P Γ Γ' t t'
    end.

  Definition on_decls (P : term -> term -> Type) (d d' : context_decl) :=
    match d.(decl_body), d'.(decl_body) with
    | Some b, Some b' => (P b b' * P d.(decl_type) d'.(decl_type))%type
    | None, None => P d.(decl_type) d'.(decl_type)
    | _, _ => False
    end.

  Section All_local_2.
    Context (P : forall (Γ Γ' : context), option (term * term) -> term -> term -> Type).

    Inductive All2_local_env : context -> context -> Type :=
    | localenv2_nil : All2_local_env [] []
    | localenv2_cons_abs Γ Γ' na na' t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' None t t' ->
        All2_local_env (Γ ,, vass na t) (Γ' ,, vass na' t')
    | localenv2_cons_def Γ Γ' na na' b b' t t' :
        All2_local_env Γ Γ' ->
        P Γ Γ' (Some (b, b')) t t' ->
        All2_local_env (Γ ,, vdef na b t) (Γ' ,, vdef na' b' t').
  End All_local_2.

  Definition on_decl_over (P : context -> context -> term -> term -> Type) Γ Γ' :=
    fun Δ Δ' => P (Γ ,,, Δ) (Γ' ,,, Δ').

  Definition All2_local_env_over P Γ Γ' := All2_local_env (on_decl (on_decl_over P Γ Γ')).

  Lemma All2_local_env_impl {P Q : context -> context -> term -> term -> Type} {par par'} :
    All2_local_env (on_decl P) par par' ->
    (forall par par' x y, P par par' x y -> Q par par' x y) ->
    All2_local_env (on_decl Q) par par'.
  Proof.
    intros H aux.
    induction H; constructor. auto. red in p. apply aux, p.
    apply IHAll2_local_env. red. split.
    apply aux. apply p. apply aux. apply p.
  Defined.

  Lemma All2_local_env_app_inv :
    forall P (Γ Γ' Γl Γr : context),
      All2_local_env (on_decl P) Γ Γl ->
      All2_local_env (on_decl (on_decl_over P Γ Γl)) Γ' Γr ->
      All2_local_env (on_decl P) (Γ ,,, Γ') (Γl ,,, Γr).
  Proof.
    induction 2; auto.
    - simpl. constructor; auto.
    - simpl. constructor; auto.
  Qed.

  Lemma All2_local_env_length {P l l'} : @All2_local_env P l l' -> #|l| = #|l'|.
  Proof. induction 1; simpl; auto. Qed.

  Hint Extern 20 (#|?X| = #|?Y|) =>
    match goal with
      [ H : All2_local_env _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
    | [ H : All2_local_env _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
    | [ H : All2_local_env_over _ _ _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
    | [ H : All2_local_env_over _ _ _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
    end : pcuic.

  Ltac pcuic := eauto with pcuic.

  Lemma All2_local_env_app':
    forall P (Γ Γ' Γ'' : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') Γ'' ->
      ∑ Γl Γr, (Γ'' = Γl ,,, Γr) /\ #|Γ'| = #|Γr| /\ #|Γ| = #|Γl|.
  Proof.
    intros *.
    revert Γ''. induction Γ'. simpl. intros.
    exists Γ'', []. intuition auto. eapply (All2_local_env_length X).
    intros. unfold app_context in X. depelim X.
    destruct (IHΓ' _ X) as [Γl [Γr [Heq HeqΓ]]]. subst Γ'0.
    eexists Γl, (Γr,, vass _ t'). simpl. intuition eauto.
    destruct (IHΓ' _ X) as [Γl [Γr [Heq HeqΓ]]]. subst Γ'0.
    eexists Γl, (Γr,, vdef _ b' t'). simpl. intuition eauto.
  Qed.

  Lemma app_inj_length_r {A} (l l' r r' : list A) :
    app l r = app l' r' -> #|r| = #|r'| -> l = l' /\ r = r'.
  Proof.
    induction r in l, l', r' |- *. destruct r'; intros; simpl in *; intuition auto; try discriminate.
    now rewrite !app_nil_r in H.
    intros. destruct r'; try discriminate.
    simpl in H.
    change (l ++ a :: r) with (l ++ [a] ++ r) in H.
    change (l' ++ a0 :: r') with (l' ++ [a0] ++ r') in H.
    rewrite !app_assoc in H. destruct (IHr _ _ _ H). now noconf H0.
    subst. now apply app_inj_tail in H1 as [-> ->].
  Qed.

  Lemma app_inj_length_l {A} (l l' r r' : list A) :
    app l r = app l' r' -> #|l| = #|l'| -> l = l' /\ r = r'.
  Proof.
    induction l in r, r', l' |- *. destruct l'; intros; simpl in *; intuition auto; try discriminate.
    intros. destruct l'; try discriminate. simpl in *. noconf H.
    specialize (IHl _ _ _ H). forward IHl; intuition congruence.
  Qed.

  Lemma All2_local_env_app_ex:
    forall P (Γ Γ' Γ'' : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') Γ'' ->
      ∑ Γl Γr, (Γ'' = Γl ,,, Γr) *
      All2_local_env
        (on_decl P)
        Γ Γl * All2_local_env (on_decl (fun Δ Δ' => P (Γ ,,, Δ) (Γl ,,, Δ'))) Γ' Γr.
  Proof.
    intros *.
    revert Γ''. induction Γ'. simpl. intros.
    exists Γ'', []. intuition auto. constructor.
    intros. unfold app_context in X. depelim X.
    destruct (IHΓ' _ X) as [Γl [Γr [[HeqΓ H2] H3]]]. subst.
    eexists _, _. intuition eauto. unfold snoc, app_context.
    now rewrite app_comm_cons. constructor. auto. auto.
    destruct (IHΓ' _ X) as [Γl [Γr [[HeqΓ H2] H3]]]. subst.
    eexists _, _. intuition eauto. unfold snoc, app_context.
    now rewrite app_comm_cons. constructor. auto. auto.
  Qed.

  Lemma All2_local_env_app :
    forall P (Γ Γ' Γl Γr : context),
      All2_local_env (on_decl P) (Γ ,,, Γ') (Γl ,,, Γr) ->
      #|Γ| = #|Γl| ->
      All2_local_env (on_decl P) Γ Γl * All2_local_env (on_decl (fun Δ Δ' => P (Γ ,,, Δ) (Γl ,,, Δ'))) Γ' Γr.
  Proof.
    intros *.
    intros. pose proof X as X'.
    apply All2_local_env_app' in X as [Γl' [Γr' ?]].
    destruct a as [? [? ?]].
    apply All2_local_env_app_ex in X' as [Γl2' [Γr2' [[? ?] ?]]].
    subst; rename_all_hyps.
    unfold app_context in heq_app_context.
    eapply app_inj_length_r in heq_app_context; try lia. destruct heq_app_context. subst.
    unfold app_context in heq_app_context0.
    eapply app_inj_length_r in heq_app_context0; try lia. intuition subst; auto.
    pose proof (All2_local_env_length a). lia.
  Qed.

  Lemma nth_error_pred1_ctx {P} {Γ Δ} i body' :
    All2_local_env (on_decl P) Γ Δ ->
    option_map decl_body (nth_error Δ i) = Some (Some body') ->
    { body & (option_map decl_body (nth_error Γ i) = Some (Some body)) *
             P (skipn (S i) Γ) (skipn (S i) Δ) body body' }%type.
  Proof.
    intros Hpred. revert i body'.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body [Heq Hpred']].
    intuition eauto.
    noconf heq_option_map. exists b. intuition eauto. cbv. apply p.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body [Heq Hpred']].
    intuition eauto.
  Qed.

  Lemma nth_error_pred1_ctx_l {P} {Γ Δ} i body :
    All2_local_env (on_decl P) Γ Δ ->
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    { body' & (option_map decl_body (nth_error Δ i) = Some (Some body')) *
             P (skipn (S i) Γ) (skipn (S i) Δ) body body' }%type.
  Proof.
    intros Hpred. revert i body.
    induction Hpred; destruct i; try discriminate; auto; !intros.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body' [Heq Hpred']].
    intuition eauto.
    noconf heq_option_map. exists b'. intuition eauto. cbv. apply p.
    simpl in heq_option_map. specialize (IHHpred _ _ heq_option_map) as [body' [Heq Hpred']].
    intuition eauto.
  Qed.

  Lemma All2_local_env_over_app P {Γ0 Δ Γ'' Δ''} :
    All2_local_env (on_decl P) Γ0 Δ ->
    All2_local_env_over P Γ0 Δ Γ'' Δ'' ->
    All2_local_env (on_decl P) (Γ0 ,,, Γ'') (Δ ,,, Δ'').
  Proof.
    intros. induction X0; pcuic; constructor; pcuic.
  Qed.

  Lemma All2_local_env_app_left {P Γ Γ' Δ Δ'} :
    All2_local_env (on_decl P) (Γ ,,, Δ) (Γ' ,,, Δ') -> #|Γ| = #|Γ'| ->
    All2_local_env (on_decl P) Γ Γ'.
  Proof.
    intros. eapply All2_local_env_app in X; intuition auto.
  Qed.

End All2_local_env.

Section ParallelReduction.
  Context (Σ : global_env).

  Definition pred_atom t :=
    match t with
    | tVar _
    | tSort _
    | tInd _ _
    | tConstruct _ _ _ => true
    | _ => false
    end.

  Inductive pred1 (Γ Γ' : context) : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | pred_beta na t0 t1 b0 b1 a0 a1 :
      pred1 Γ Γ' t0 t1 ->
      pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> pred1 Γ Γ' a0 a1 ->
      pred1 Γ Γ' (tApp (tLambda na t0 b0) a0) (subst10 a1 b1)

  (** Let *)
  | pred_zeta na d0 d1 t0 t1 b0 b1 :
      pred1 Γ Γ' t0 t1 ->
      pred1 Γ Γ' d0 d1 -> pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1 Γ Γ' (tLetIn na d0 t0 b0) (subst10 d1 b1)

  (** Local variables *)
  | pred_rel_def_unfold i body :
      All2_local_env (on_decl pred1) Γ Γ' ->
      option_map decl_body (nth_error Γ' i) = Some (Some body) ->
      pred1 Γ Γ' (tRel i) (lift0 (S i) body)

  | pred_rel_refl i :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred1 Γ Γ' (tRel i)  (tRel i)

  (** Case *)
  | pred_iota ind pars c u args0 args1 p brs0 brs1 :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2 (pred1 Γ Γ') args0 args1 ->
      All2 (on_Trel_eq (pred1 Γ Γ') snd fst) brs0 brs1 ->
      pred1 Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0)
            (iota_red pars c args1 brs1)

  (** Fix unfolding, with guard *)
  | pred_fix mfix0 mfix1 idx args0 args1 narg fn :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      unfold_fix mfix1 idx = Some (narg, fn) ->
      is_constructor narg args1 = true ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)

  (** CoFix-case unfolding *)
  | pred_cofix_case ip p0 p1 mfix0 mfix1 idx args0 args1 narg fn brs0 brs1 :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' p0 p1 ->
      All2 (on_Trel_eq (pred1 Γ Γ') snd fst) brs0 brs1 ->
      pred1 Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix0 idx) args0) brs0)
            (tCase ip p1 (mkApps fn args1) brs1)

  (** CoFix-proj unfolding *)
  | pred_cofix_proj p mfix0 mfix1 idx args0 args1 narg fn :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      unfold_cofix mfix1 idx = Some (narg, fn) ->
      All2 (pred1 Γ Γ') args0 args1 ->
      pred1 Γ Γ' (tProj p (mkApps (tCoFix mfix0 idx) args0))
            (tProj p (mkApps fn args1))

  (** Constant unfolding *)

  | pred_delta c decl body (isdecl : declared_constant Σ c decl) u :
      All2_local_env (on_decl pred1) Γ Γ' ->
      decl.(cst_body) = Some body ->
      pred1 Γ Γ' (tConst c u) (subst_instance_constr u body)

  | pred_const c u :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred1 Γ Γ' (tConst c u) (tConst c u)

  (** Proj *)
  | pred_proj i pars narg k u args0 args1 arg1 :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2 (pred1 Γ Γ') args0 args1 ->
      nth_error args1 (pars + narg) = Some arg1 ->
      pred1 Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1

  (** Congruences *)
  | pred_abs na M M' N N' : pred1 Γ Γ' M M' -> pred1 (Γ ,, vass na M) (Γ' ,, vass na M') N N' ->
                            pred1 Γ Γ' (tLambda na M N) (tLambda na M' N')
  | pred_app M0 M1 N0 N1 :
      pred1 Γ Γ' M0 M1 ->
      pred1 Γ Γ' N0 N1 ->
      pred1 Γ Γ' (tApp M0 N0) (tApp M1 N1)
            (* do not handle mkApps yet *)

  | pred_letin na d0 d1 t0 t1 b0 b1 :
      pred1 Γ Γ' d0 d1 -> pred1 Γ Γ' t0 t1 -> pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
      pred1 Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)

  | pred_case ind p0 p1 c0 c1 brs0 brs1 :
      pred1 Γ Γ' p0 p1 ->
      pred1 Γ Γ' c0 c1 ->
      All2 (on_Trel_eq (pred1 Γ Γ') snd fst) brs0 brs1 ->
      pred1 Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)

  | pred_proj_congr p c c' :
      pred1 Γ Γ' c c' -> pred1 Γ Γ' (tProj p c) (tProj p c')

  | pred_fix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)

  | pred_cofix_congr mfix0 mfix1 idx :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
      All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                    dtype dbody (fun x => (dname x, rarg x)) pred1 mfix0 mfix1 ->
      pred1 Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)

  | pred_prod na M0 M1 N0 N1 : pred1 Γ Γ' M0 M1 -> pred1 (Γ ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
                               pred1 Γ Γ' (tProd na M0 N0) (tProd na M1 N1)

  | evar_pred ev l l' :
      All2_local_env (on_decl pred1) Γ Γ' ->
      All2 (pred1 Γ Γ') l l' -> pred1 Γ Γ' (tEvar ev l) (tEvar ev l')

  | pred_atom_refl t :
      All2_local_env (on_decl pred1) Γ Γ' ->
      pred_atom t -> pred1 Γ Γ' t t.

  Notation pred1_ctx Γ Γ' := (All2_local_env (on_decl pred1) Γ Γ').

  Ltac my_rename_hyp h th :=
    match th with
    | pred1_ctx _ _ ?G => fresh "pred" G
    | _ => PCUICWeakeningEnv.my_rename_hyp h th
    end.

  Ltac rename_hyp h ht ::= my_rename_hyp h ht.

  Definition extendP {P Q: context -> context -> term -> term -> Type}
             (aux : forall Γ Γ' t t', P Γ Γ' t t' -> Q Γ Γ' t t') :
    (forall Γ Γ' t t', P Γ Γ' t t' -> (P Γ Γ' t t' * Q Γ Γ' t t')).
  Proof.
    intros. split. apply X. apply aux. apply X.
  Defined.

  (* Lemma pred1_ind_all : *)
  (*   forall P : forall (Γ Γ' : context) (t t0 : term), Type, *)
  (*     let P' Γ Γ' x y := ((pred1 Γ Γ' x y) * P Γ Γ' x y)%type in *)
  (*     (forall (Γ Γ' : context) (na : name) (t0 t1 b0 b1 a0 a1 : term), *)
  (*         pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> P (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> *)
  (*         pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 -> *)
  (*         pred1 Γ Γ' a0 a1 -> P Γ Γ' a0 a1 -> P Γ Γ' (tApp (tLambda na t0 b0) a0) (b1 {0 := a1})) -> *)
  (*     (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term), *)
  (*         pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 -> *)
  (*         pred1 Γ Γ' d0 d1 -> P Γ Γ' d0 d1 -> *)
  (*         pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> *)
  (*         P (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (b1 {0 := d1})) -> *)
  (*     (forall (Γ Γ' : context) (i : nat) (body : term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         option_map decl_body (nth_error Γ' i) = Some (Some body) -> *)
  (*         P Γ Γ' (tRel i) (lift0 (S i) body)) -> *)
  (*     (forall (Γ Γ' : context) (i : nat), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         P Γ Γ' (tRel i) (tRel i)) -> *)
  (*     (forall (Γ Γ' : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args0 args1 : list term) *)
  (*             (p : term) (brs0 brs1 : list (nat * term)), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2 (P' Γ Γ') args0 args1 -> *)
  (*         All2_prop_eq Γ Γ' snd fst P' brs0 brs1 -> *)
  (*         P Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0) (iota_red pars c args1 brs1)) -> *)
  (*     (forall (Γ Γ' : context) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn0 fn1 : term), *)
  (*         unfold_fix mfix idx = Some (narg, fn0) -> *)
  (*         is_constructor narg args1 = true -> *)
  (*         All2 (P' Γ Γ') args0 args1 -> *)
  (*         pred1 Γ Γ' fn0 fn1 -> P Γ Γ' fn0 fn1 -> P Γ Γ' (mkApps (tFix mfix idx) args0) (mkApps fn1 args1)) -> *)
  (*     (forall (Γ Γ' : context) (ip : inductive * nat) (p0 p1 : term) (mfix : mfixpoint term) (idx : nat) *)
  (*             (args0 args1 : list term) (narg : nat) (fn0 fn1 : term) (brs0 brs1 : list (nat * term)), *)
  (*         unfold_cofix mfix idx = Some (narg, fn0) -> *)
  (*         All2 (P' Γ Γ') args0 args1 -> *)
  (*         pred1 Γ Γ' fn0 fn1 -> *)
  (*         P Γ Γ' fn0 fn1 -> *)
  (*         pred1 Γ Γ' p0 p1 -> *)
  (*         P Γ Γ' p0 p1 -> *)
  (*         All2_prop_eq Γ Γ' snd fst P' brs0 brs1 -> *)
  (*         P Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix idx) args0) brs0) (tCase ip p1 (mkApps fn1 args1) brs1)) -> *)
  (*     (forall (Γ Γ' : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args0 args1 : list term) *)
  (*             (narg : nat) (fn0 fn1 : term), *)
  (*         unfold_cofix mfix idx = Some (narg, fn0) -> *)
  (*         All2 (P' Γ Γ') args0 args1 -> *)
  (*         pred1 Γ Γ' fn0 fn1 -> P Γ Γ' fn0 fn1 -> *)
  (*         P Γ Γ' (tProj p (mkApps (tCoFix mfix idx) args0)) (tProj p (mkApps fn1 args1))) -> *)
  (*     (forall (Γ Γ' : context) (c : ident) (decl : constant_body) (body : term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         declared_constant Σ c decl -> *)
  (*         forall u : universe_instance, cst_body decl = Some body -> *)
  (*                                       P Γ Γ' (tConst c u) (subst_instance_constr u body)) -> *)
  (*     (forall (Γ Γ' : context) (c : ident) (u : universe_instance), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         P Γ Γ' (tConst c u) (tConst c u)) -> *)
  (*     (forall (Γ Γ' : context) (i : inductive) (pars narg : nat) (k : nat) (u : universe_instance) *)
  (*             (args0 args1 : list term) (arg1 : term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2 (pred1 Γ Γ') args0 args1 -> *)
  (*         All2 (P Γ Γ') args0 args1 -> *)
  (*         nth_error args1 (pars + narg) = Some arg1 -> *)
  (*         P Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1) -> *)
  (*     (forall (Γ Γ' : context) (na : name) (M M' N N' : term), *)
  (*         pred1 Γ Γ' M M' -> *)
  (*         P Γ Γ' M M' -> pred1 (Γ,, vass na M) (Γ' ,, vass na M') N N' -> *)
  (*         P (Γ,, vass na M) (Γ' ,, vass na M') N N' -> P Γ Γ' (tLambda na M N) (tLambda na M' N')) -> *)
  (*     (forall (Γ Γ' : context) (M0 M1 N0 N1 : term), *)
  (*         pred1 Γ Γ' M0 M1 -> P Γ Γ' M0 M1 -> pred1 Γ Γ' N0 N1 -> P Γ Γ' N0 N1 -> P Γ Γ' (tApp M0 N0) (tApp M1 N1)) -> *)
  (*     (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term), *)
  (*         pred1 Γ Γ' d0 d1 -> *)
  (*         P Γ Γ' d0 d1 -> *)
  (*         pred1 Γ Γ' t0 t1 -> *)
  (*         P Γ Γ' t0 t1 -> *)
  (*         pred1 (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> *)
  (*         P (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) -> *)
  (*     (forall (Γ Γ' : context) (ind : inductive * nat) (p0 p1 c0 c1 : term) (brs0 brs1 : list (nat * term)), *)
  (*         pred1 Γ Γ' p0 p1 -> *)
  (*         P Γ Γ' p0 p1 -> *)
  (*         pred1 Γ Γ' c0 c1 -> *)
  (*         P Γ Γ' c0 c1 -> All2_prop_eq Γ Γ' snd fst P' brs0 brs1 -> *)
  (*         P Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)) -> *)
  (*     (forall (Γ Γ' : context) (p : projection) (c c' : term), *)
  (*         pred1 Γ Γ' c c' -> P Γ Γ' c c' -> P Γ Γ' (tProj p c) (tProj p c')) -> *)

  (*     (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) -> *)
  (*         All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) -> *)
  (*         All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) *)
  (*                       dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 -> *)
  (*         P Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)) -> *)

  (*     (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) -> *)
  (*         All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) -> *)
  (*         All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 -> *)
  (*         P Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)) -> *)
  (*     (forall (Γ Γ' : context) (na : name) (M0 M1 N0 N1 : term), *)
  (*         pred1 Γ Γ' M0 M1 -> *)
  (*         P Γ Γ' M0 M1 -> pred1 (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> *)
  (*         P (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> P Γ Γ' (tProd na M0 N0) (tProd na M1 N1)) -> *)
  (*     (forall (Γ Γ' : context) (ev : nat) (l l' : list term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         All2 (P' Γ Γ') l l' -> P Γ Γ' (tEvar ev l) (tEvar ev l')) -> *)
  (*     (forall (Γ Γ' : context) (t : term), *)
  (*         All2_local_env (on_decl pred1) Γ Γ' -> *)
  (*         All2_local_env (on_decl P) Γ Γ' -> *)
  (*         pred_atom t -> P Γ Γ' t t) -> *)
  (*     forall (Γ Γ' : context) (t t0 : term), pred1 Γ Γ' t t0 -> P Γ Γ' t t0. *)
  (* Proof. *)
  (*   intros. revert Γ Γ' t t0 X20. *)
  (*   fix aux 5. intros Γ Γ' t t'. *)
  (*   move aux at top. *)
  (*   destruct 1; match goal with *)
  (*               | |- P _ _ (tFix _ _) (tFix _ _) => idtac *)
  (*               | |- P _ _ (tCoFix _ _) (tCoFix _ _) => idtac *)
  (*               | |- P _ _ (mkApps (tFix _ _) _) _ => idtac *)
  (*               | |- P _ _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac *)
  (*               | |- P _ _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac *)
  (*               | |- P _ _ (tRel _) _ => idtac *)
  (*               | |- P _ _ (tConst _ _) _ => idtac *)
  (*               | H : _ |- _ => eapply H; eauto *)
  (*               end. *)
  (*   - simpl. apply X1; auto. *)
  (*     apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - simpl. apply X2; auto. *)
  (*     apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 ((extendP aux) Γ Γ')). *)
  (*   - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) (g:=fst) a1 (extendP aux Γ Γ')). *)
  (*   - eapply X4; eauto. *)
  (*     eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')). *)
  (*   - eapply X5; eauto. *)
  (*     eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')). *)
  (*     eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a0 (extendP aux Γ Γ')). *)
  (*   - eapply X6; eauto. *)
  (*     eapply (All2_All2_prop (P:=pred1) (Q:=P') a (extendP aux Γ Γ')). *)
  (*   - eapply X7; eauto. *)
  (*     apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply X8; eauto. *)
  (*     apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - apply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply (All2_All2_prop (P:=pred1) (Q:=P) a0). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a (extendP aux Γ Γ')). *)
  (*   - eapply X15. *)
  (*     eapply (All2_local_env_impl a). intros. apply X20. *)
  (*     eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*     eapply (All2_local_env_impl a0). intros. red. exact X20. *)
  (*     eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20). *)
  (*     eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)). *)
  (*   - eapply X16. *)
  (*     eapply (All2_local_env_impl a). intros. apply X20. *)
  (*     eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*     eapply (All2_local_env_impl a0). intros. red. exact X20. *)
  (*     eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20). *)
  (*     eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)). *)
  (*   - eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (*   - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 (extendP aux Γ Γ')). *)
  (*   - eapply (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20). *)
  (* Defined. *)

  Lemma pred1_ind_all_ctx :
    forall (P : forall (Γ Γ' : context) (t t0 : term), Type)
           (Pctx : forall (Γ Γ' : context), Type),
           (* (Plist : forall {A} (f : A -> term), context -> context -> list A -> list A -> Type), *)
      let P' Γ Γ' x y := ((pred1 Γ Γ' x y) * P Γ Γ' x y)%type in
      (forall Γ Γ', All2_local_env (on_decl pred1) Γ Γ' -> All2_local_env (on_decl P) Γ Γ' -> Pctx Γ Γ') ->
      (* (forall (f : A -> term) (l l' : list A) (g : A -> B), *)
      (*     All2 (on_Trel pred1 f) l l' -> *)
      (*     All2 (on_Trel P f) l l' -> *)
      (*     All2 (on_Trel eq g) l l' -> *)
      (*     Plist f Γ Γ' l l') -> *)
      (forall (Γ Γ' : context) (na : name) (t0 t1 b0 b1 a0 a1 : term),
          pred1 (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 -> P (Γ ,, vass na t0) (Γ' ,, vass na t1) b0 b1 ->
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' a0 a1 -> P Γ Γ' a0 a1 -> P Γ Γ' (tApp (tLambda na t0 b0) a0) (b1 {0 := a1})) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' t0 t1 -> P Γ Γ' t0 t1 ->
          pred1 Γ Γ' d0 d1 -> P Γ Γ' d0 d1 ->
          pred1 (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 ->
          P (Γ ,, vdef na d0 t0) (Γ' ,, vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (b1 {0 := d1})) ->
      (forall (Γ Γ' : context) (i : nat) (body : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          option_map decl_body (nth_error Γ' i) = Some (Some body) ->
          P Γ Γ' (tRel i) (lift0 (S i) body)) ->
      (forall (Γ Γ' : context) (i : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tRel i) (tRel i)) ->
      (forall (Γ Γ' : context) (ind : inductive) (pars c : nat) (u : universe_instance) (args0 args1 : list term)
              (p : term) (brs0 brs1 : list (nat * term)),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') args0 args1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase (ind, pars) p (mkApps (tConstruct ind c u) args0) brs0) (iota_red pars c args1 brs1)) ->
      (forall (Γ Γ' : context) (mfix0 mfix1 : mfixpoint term) (idx : nat) (args0 args1 : list term) (narg : nat) (fn : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_fix mfix1 idx = Some (narg, fn) ->
          is_constructor narg args1 = true ->
          All2 (P' Γ Γ') args0 args1 ->
          P Γ Γ' (mkApps (tFix mfix0 idx) args0) (mkApps fn args1)) ->
      (forall (Γ Γ' : context) (ip : inductive * nat) (p0 p1 : term) (mfix0 mfix1 : mfixpoint term) (idx : nat)
              (args0 args1 : list term) (narg : nat) (fn : term) (brs0 brs1 : list (nat * term)),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ Γ') args0 args1 ->
          pred1 Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ip p0 (mkApps (tCoFix mfix0 idx) args0) brs0) (tCase ip p1 (mkApps fn args1) brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (mfix0 mfix1 : mfixpoint term)
         (idx : nat) (args0 args1 : list term)
         (narg : nat) (fn : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody
                        (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          unfold_cofix mfix1 idx = Some (narg, fn) ->
          All2 (P' Γ Γ') args0 args1 ->
          P Γ Γ' (tProj p (mkApps (tCoFix mfix0 idx) args0)) (tProj p (mkApps fn args1))) ->
      (forall (Γ Γ' : context) (c : ident) (decl : constant_body) (body : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          declared_constant Σ c decl ->
          forall u : universe_instance, cst_body decl = Some body ->
                                        P Γ Γ' (tConst c u) (subst_instance_constr u body)) ->
      (forall (Γ Γ' : context) (c : ident) (u : universe_instance),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          P Γ Γ' (tConst c u) (tConst c u)) ->
      (forall (Γ Γ' : context) (i : inductive) (pars narg : nat) (k : nat) (u : universe_instance)
              (args0 args1 : list term) (arg1 : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (pred1 Γ Γ') args0 args1 ->
          All2 (P Γ Γ') args0 args1 ->
          nth_error args1 (pars + narg) = Some arg1 ->
          P Γ Γ' (tProj (i, pars, narg) (mkApps (tConstruct i k u) args0)) arg1) ->
      (forall (Γ Γ' : context) (na : name) (M M' N N' : term),
          pred1 Γ Γ' M M' ->
          P Γ Γ' M M' -> pred1 (Γ,, vass na M) (Γ' ,, vass na M') N N' ->
          P (Γ,, vass na M) (Γ' ,, vass na M') N N' -> P Γ Γ' (tLambda na M N) (tLambda na M' N')) ->
      (forall (Γ Γ' : context) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 -> P Γ Γ' M0 M1 -> pred1 Γ Γ' N0 N1 ->
          P Γ Γ' N0 N1 -> P Γ Γ' (tApp M0 N0) (tApp M1 N1)) ->
      (forall (Γ Γ' : context) (na : name) (d0 d1 t0 t1 b0 b1 : term),
          pred1 Γ Γ' d0 d1 ->
          P Γ Γ' d0 d1 ->
          pred1 Γ Γ' t0 t1 ->
          P Γ Γ' t0 t1 ->
          pred1 (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 ->
          P (Γ,, vdef na d0 t0) (Γ',,vdef na d1 t1) b0 b1 -> P Γ Γ' (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1)) ->
      (forall (Γ Γ' : context) (ind : inductive * nat) (p0 p1 c0 c1 : term) (brs0 brs1 : list (nat * term)),
          pred1 Γ Γ' p0 p1 ->
          P Γ Γ' p0 p1 ->
          pred1 Γ Γ' c0 c1 ->
          P Γ Γ' c0 c1 -> All2_prop_eq Γ Γ' snd fst P' brs0 brs1 ->
          P Γ Γ' (tCase ind p0 c0 brs0) (tCase ind p1 c1 brs1)) ->
      (forall (Γ Γ' : context) (p : projection) (c c' : term), pred1 Γ Γ' c c' -> P Γ Γ' c c' -> P Γ Γ' (tProj p c) (tProj p c')) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1)
                        dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tFix mfix0 idx) (tFix mfix1 idx)) ->

      (forall (Γ Γ' : context) (mfix0 : mfixpoint term) (mfix1 : list (def term)) (idx : nat),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2_local_env (on_decl (on_decl_over pred1 Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context mfix0) (fix_context mfix1) ->
          All2_prop2_eq Γ Γ' (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix1) dtype dbody (fun x => (dname x, rarg x)) P' mfix0 mfix1 ->
          P Γ Γ' (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
      (forall (Γ Γ' : context) (na : name) (M0 M1 N0 N1 : term),
          pred1 Γ Γ' M0 M1 ->
          P Γ Γ' M0 M1 -> pred1 (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 ->
          P (Γ,, vass na M0) (Γ' ,, vass na M1) N0 N1 -> P Γ Γ' (tProd na M0 N0) (tProd na M1 N1)) ->
      (forall (Γ Γ' : context) (ev : nat) (l l' : list term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          All2 (P' Γ Γ') l l' -> P Γ Γ' (tEvar ev l) (tEvar ev l')) ->
      (forall (Γ Γ' : context) (t : term),
          All2_local_env (on_decl pred1) Γ Γ' ->
          Pctx Γ Γ' ->
          pred_atom t -> P Γ Γ' t t) ->
      forall (Γ Γ' : context) (t t0 : term), pred1 Γ Γ' t t0 -> P Γ Γ' t t0.
  Proof.
    intros P Pctx P' Hctx. intros. revert Γ Γ' t t0 X20.
    fix aux 5. intros Γ Γ' t t'.
    move aux at top.
    destruct 1; match goal with
                | |- P _ _ (tFix _ _) (tFix _ _) => idtac
                | |- P _ _ (tCoFix _ _) (tCoFix _ _) => idtac
                | |- P _ _ (mkApps (tFix _ _) _) _ => idtac
                | |- P _ _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ => idtac
                | |- P _ _ (tProj _ (mkApps (tCoFix _ _) _)) _ => idtac
                | |- P _ _ (tRel _) _ => idtac
                | |- P _ _ (tConst _ _) _ => idtac
                | H : _ |- _ => eapply H; eauto
                end.
    - simpl. apply X1; auto. apply Hctx.
      apply (All2_local_env_impl a). intros. eapply X20.
      apply (All2_local_env_impl a). intros. eapply (aux _ _ _ _ X20).
    - simpl. apply X2; auto.
      apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X20).
    - apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 ((extendP aux) Γ Γ')).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) (g:=fst) a1 (extendP aux Γ Γ')).
    - eapply X4; eauto.
      apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X20).
      eapply (All2_local_env_impl a0). intros. red. red in X20. apply (aux _ _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a2 (extendP aux Γ Γ')).
    - eapply X5; eauto.
      apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X21).
      eapply (All2_local_env_impl a0). intros. red. red in X21. apply (aux _ _ _ _ X21).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a2 (extendP aux Γ Γ')).
      eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a3 (extendP aux Γ Γ')).
    - eapply X6; eauto.
      apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X20).
      eapply (All2_local_env_impl a0). intros. red. red in X20. apply (aux _ _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
      eapply (All2_All2_prop (P:=pred1) (Q:=P') a2 (extendP aux Γ Γ')).
    - eapply X7; eauto.
      apply Hctx, (All2_local_env_impl a). intros. exact a. intros. apply (aux _ _ _ _ X20).
    - eapply X8; eauto.
      apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X20).
    - apply Hctx, (All2_local_env_impl a). exact a. intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P) a0). intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop_eq (P:=pred1) (Q:=P') (f:=snd) a (extendP aux Γ Γ')).
    - eapply X15.
      eapply (All2_local_env_impl a). intros. apply X20.
      eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
      eapply (All2_local_env_impl a0). intros. red. exact X20.
      eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply X16.
      eapply (All2_local_env_impl a). intros. apply X20.
      eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
      eapply (All2_local_env_impl a0). intros. red. exact X20.
      eapply (All2_local_env_impl a0). intros. red. apply (aux _ _ _ _ X20).
      eapply (All2_All2_prop2_eq (Q:=P') (f:=dtype) (g:=dbody) a1 (extendP aux)).
    - eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
    - eapply (All2_All2_prop (P:=pred1) (Q:=P') a0 (extendP aux Γ Γ')).
    - eapply (Hctx _ _ a), (All2_local_env_impl a). intros. apply (aux _ _ _ _ X20).
  Defined.

  Lemma pred1_refl_gen Γ Γ' t : pred1_ctx Γ Γ' -> pred1 Γ Γ' t t.
  Proof.
    revert Γ'.
    unshelve einduction Γ, t using term_forall_ctx_list_ind;
    intros;
      try solve [(apply pred_atom; reflexivity) || constructor; auto];
      try solve [try red in X; constructor; unfold All2_prop2_eq, All2_prop2, on_Trel in *; solve_all];
      intros.
    - constructor; eauto. eapply IHt0_2.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply IHt0_2.
      constructor; try red; eauto with pcuic.
    - constructor; eauto. eapply IHt0_3.
      constructor; try red; eauto with pcuic.
    - assert (All2_local_env (on_decl (fun Δ Δ' : context => pred1 (Γ0 ,,, Δ) (Γ' ,,, Δ')))
                             (fix_context m) (fix_context m)).
      { revert X. clear -X1. generalize (fix_context m).
        intros c H1. induction H1; constructor; auto.
        - red in t0. red. eapply t0. eapply All2_local_env_app_inv; auto.
        - red in t1. red. split.
          + eapply t1. eapply All2_local_env_app_inv; auto.
          + eapply t1. eapply All2_local_env_app_inv; auto.
      }
      constructor; auto. red.
      unfold All2_prop_eq, on_Trel in *.
      eapply All_All2; eauto. simpl; intros.
      split; eauto. eapply X3; auto.
      split. eapply X3. eapply All2_local_env_app_inv; auto. auto.
    - assert (All2_local_env (on_decl (fun Δ Δ' : context => pred1 (Γ0 ,,, Δ) (Γ' ,,, Δ')))
                             (fix_context m) (fix_context m)).
      { revert X. clear -X1. generalize (fix_context m).
        intros c H1. induction H1; constructor; auto.
        - red in t0. red. eapply t0. eapply All2_local_env_app_inv; auto.
        - red in t1. red. split.
          + eapply t1. eapply All2_local_env_app_inv; auto.
          + eapply t1. eapply All2_local_env_app_inv; auto.
      }
      constructor; auto. red.
      eapply All_All2; eauto. simpl; intros.
      split; eauto. eapply X3; auto.
      split. eapply X3. eapply All2_local_env_app_inv; auto. auto.
  Qed.

  Lemma pred1_ctx_refl Γ : pred1_ctx Γ Γ.
  Proof.
    induction Γ. constructor.
    destruct a as [na [b|] ty]; constructor; try red; simpl; auto with pcuic.
    split; now apply pred1_refl_gen. apply pred1_refl_gen, IHΓ.
  Qed.
  Hint Resolve pred1_ctx_refl : pcuic.

  Lemma pred1_refl Γ t : pred1 Γ Γ t t.
  Proof. apply pred1_refl_gen, pred1_ctx_refl. Qed.

  Lemma pred1_pred1_ctx {Γ Δ t u} : pred1 Γ Δ t u -> pred1_ctx Γ Δ.
  Proof.
    intros H; revert Γ Δ t u H.
    refine (pred1_ind_all_ctx _ (fun Γ Γ' => pred1_ctx Γ Γ') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *.
    all:try intros **; rename_all_hyps;
      try solve [specialize (forall_Γ _ X3); eauto]; eauto;
        try solve [eexists; split; constructor; eauto].
  Qed.

  Lemma pred1_ctx_over_refl Γ Δ : All2_local_env (on_decl (on_decl_over pred1 Γ Γ)) Δ Δ.
  Proof.
    induction Δ as [|[na [b|] ty] Δ]; constructor; auto.
    red. split; red; apply pred1_refl.
    red. apply pred1_refl.
  Qed.

End ParallelReduction.

Hint Constructors pred1 : pcuic.
Hint Unfold All2_prop2_eq All2_prop2 on_decl on_decl_over on_rel on_Trel snd on_snd : pcuic.
Hint Resolve All2_same: pcuic.
Hint Constructors All2_local_env : pcuic.

Hint Resolve pred1_ctx_refl : pcuic.

Ltac pcuic_simplify :=
  simpl || split || destruct_conjs || red.

Hint Extern 10 => progress pcuic_simplify : pcuic.

Notation pred1_ctx Σ Γ Γ' := (All2_local_env (on_decl (pred1 Σ)) Γ Γ').

Hint Extern 4 (pred1 _ _ _ ?t _) => tryif is_evar t then fail 1 else eapply pred1_refl_gen : pcuic.
Hint Extern 4 (pred1 _ _ _ ?t _) => tryif is_evar t then fail 1 else eapply pred1_refl : pcuic.

Hint Extern 20 (#|?X| = #|?Y|) =>
match goal with
  [ H : All2_local_env _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
| [ H : All2_local_env _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
| [ H : All2_local_env_over _ _ _ ?X ?Y |- _ ] => apply (All2_local_env_length H)
| [ H : All2_local_env_over _ _ _ ?Y ?X |- _ ] => symmetry; apply (All2_local_env_length H)
end : pcuic.

Hint Extern 4 (pred1_ctx ?Σ ?Γ ?Γ') =>
  match goal with
  | [ H : pred1_ctx Σ (Γ ,,, _) (Γ' ,,, _) |- _ ] => apply (All2_local_env_app_left H)
  | [ H : pred1 Σ Γ Γ' _ _ |- _ ] => apply (pred1_pred1_ctx _ H)
  end : pcuic.

Ltac pcuic := try repeat red; cbn in *; try solve [intuition auto; eauto with pcuic || ltac:(try (lia || congruence))].

Ltac my_rename_hyp h th :=
  match th with
  | pred1_ctx _ _ ?G => fresh "pred" G
  | _ => PCUICWeakeningEnv.my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Lemma All2_local_env_over_refl {Σ Γ Δ Γ'} :
  pred1_ctx Σ Γ Δ -> All2_local_env_over (pred1 Σ) Γ Δ Γ' Γ'.
Proof.
  intros X0.
  red. induction Γ'. constructor.
  pose proof IHΓ'. apply All2_local_env_over_app in IHΓ'; auto.
  destruct a as [na [b|] ty]; constructor; pcuic.
Qed.

Hint Extern 4 (All2_local_env_over _ _ _ ?X) =>
  tryif is_evar X then fail 1 else eapply All2_local_env_over_refl : pcuic.

Section ParallelWeakening.
  Context {cf : checker_flags}.
  (* Lemma All2_local_env_over_app_inv {Σ Γ0 Δ Γ'' Δ''} : *)
  (*   pred1_ctx Σ (Γ0 ,,, Γ'') (Δ ,,, Δ'') -> *)
  (*   pred1_ctx Σ Γ0 Δ -> *)
  (*   All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' -> *)

  (* Proof. *)
  (*   intros. induction X0; pcuic; constructor; pcuic. *)
  (* Qed. *)

  Lemma All2_local_env_weaken_pred_ctx {Σ Γ0 Γ'0 Δ Δ' Γ'' Δ''} :
      #|Γ0| = #|Δ| ->
  pred1_ctx Σ Γ0 Δ ->
  All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' ->
  All2_local_env
    (on_decl
       (fun (Γ Γ' : context) (t t0 : term) =>
        forall Γ1 Γ'1 : context,
        Γ = Γ1 ,,, Γ'1 ->
        forall Δ0 Δ'0 : context,
        Γ' = Δ0 ,,, Δ'0 ->
        #|Γ1| = #|Δ0| ->
        forall Γ''0 Δ''0 : context,
        All2_local_env_over (pred1 Σ) Γ1 Δ0 Γ''0 Δ''0 ->
        pred1 Σ (Γ1 ,,, Γ''0 ,,, lift_context #|Γ''0| 0 Γ'1) (Δ0 ,,, Δ''0 ,,, lift_context #|Δ''0| 0 Δ'0)
          (lift #|Γ''0| #|Γ'1| t) (lift #|Δ''0| #|Δ'0| t0))) (Γ0 ,,, Γ'0) (Δ ,,, Δ') ->

  pred1_ctx Σ (Γ0 ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'0) (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ').
  Proof.
    intros.
    pose proof (All2_local_env_length X0).
    eapply All2_local_env_app in X1 as [Xl Xr]; auto.
    induction Xr; simpl; auto. apply All2_local_env_over_app; pcuic.
    rewrite !lift_context_snoc. simpl. constructor. auto. red in p.
    specialize (p _ _ eq_refl _ _ eq_refl). forward p by auto.
    red. rewrite !Nat.add_0_r. simpl. specialize (p Γ'' Δ'').
    forward p. auto. pose proof (All2_local_env_length X0).
    rewrite H0 in p. congruence.

    destruct p.
    specialize (p _ _ eq_refl _ _ eq_refl H _ _ X0).
    specialize (p0 _ _ eq_refl _ _ eq_refl H _ _ X0).
    rewrite !lift_context_snoc. simpl. constructor; auto.
    red. split; auto.
    rewrite !Nat.add_0_r. rewrite H0 in p. simpl. congruence.
    rewrite !Nat.add_0_r. rewrite H0 in p0. simpl. congruence.
  Qed.

  Lemma All2_local_env_weaken_pred_ctx' {Σ Γ0 Γ'0 Δ Δ' Γ'' Δ''} ctx ctx' :
      #|Γ0| = #|Δ| -> #|Γ0 ,,, Γ'0| = #|Δ ,,, Δ'| ->
  pred1_ctx Σ Γ0 Δ ->
  All2_local_env_over (pred1 Σ) Γ0 Δ Γ'' Δ'' ->
  All2_local_env
    (on_decl
       (on_decl_over
          (fun (Γ Γ' : context) (t t0 : term) =>
           forall Γ1 Γ'1 : context,
           Γ = Γ1 ,,, Γ'1 ->
           forall Δ0 Δ'0 : context,
           Γ' = Δ0 ,,, Δ'0 ->
           #|Γ1| = #|Δ0| ->
           forall Γ''0 Δ''0 : context,
           All2_local_env_over (pred1 Σ) Γ1 Δ0 Γ''0 Δ''0 ->
           pred1 Σ (Γ1 ,,, Γ''0 ,,, lift_context #|Γ''0| 0 Γ'1) (Δ0 ,,, Δ''0 ,,, lift_context #|Δ''0| 0 Δ'0)
             (lift #|Γ''0| #|Γ'1| t) (lift #|Δ''0| #|Δ'0| t0)) (Γ0 ,,, Γ'0) (Δ ,,, Δ')))
    ctx ctx' ->
  All2_local_env
    (on_decl
       (on_decl_over (pred1 Σ) (Γ0 ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'0) (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')))
    (lift_context #|Γ''| #|Γ'0| ctx) (lift_context #|Δ''| #|Δ'| ctx').
  Proof.
    intros.
    pose proof (All2_local_env_length X0).
    induction X1; simpl; rewrite ?lift_context_snoc0; constructor; auto.
    - red in p. red in p. red. red. simpl.
      specialize (p Γ0 (Γ'0,,, Γ)).
      rewrite app_context_assoc in p. forward p by auto.
      specialize (p Δ (Δ',,, Γ')).
      rewrite app_context_assoc in p. forward p by auto.
      specialize (p H _ _ X0).
      rewrite !app_context_length !lift_context_app !app_context_assoc !Nat.add_0_r in p.
      congruence.
    - destruct p.
      specialize (o Γ0 (Γ'0,,, Γ) ltac:(now rewrite app_context_assoc) Δ (Δ',,, Γ')
                                  ltac:(now rewrite app_context_assoc) H _ _ X0).
      rewrite !app_context_length !lift_context_app !app_context_assoc !Nat.add_0_r in o.
      specialize (o0 Γ0 (Γ'0,,, Γ) ltac:(now rewrite app_context_assoc) Δ (Δ',,, Γ')
                                  ltac:(now rewrite app_context_assoc) H _ _ X0).
      rewrite !app_context_length !lift_context_app !app_context_assoc !Nat.add_0_r in o0.
      red. split; auto.
  Qed.

  Lemma map_cofix_subst f mfix :
    (forall n, tCoFix (map (map_def (f 0) (f #|mfix|)) mfix) n = f 0 (tCoFix mfix n)) ->
    cofix_subst (map (map_def (f 0) (f #|mfix|)) mfix) =
    map (f 0) (cofix_subst mfix).
  Proof.
    unfold cofix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 2 3. induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma map_fix_subst f mfix :
    (forall n, tFix (map (map_def (f 0) (f #|mfix|)) mfix) n = f 0 (tFix mfix n)) ->
    fix_subst (map (map_def (f 0) (f #|mfix|)) mfix) =
    map (f 0) (fix_subst mfix).
  Proof.
    unfold fix_subst. intros.
    rewrite map_length. generalize (#|mfix|) at 2 3. induction n. simpl. reflexivity.
    simpl. rewrite - IHn. f_equal. apply H.
  Qed.

  Lemma weakening_pred1 Σ Γ Γ' Γ'' Δ Δ' Δ'' M N : wf Σ ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') M N ->
    #|Γ| = #|Δ| ->
    All2_local_env_over (pred1 Σ) Γ Δ Γ'' Δ'' ->
    pred1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
          (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')
          (lift #|Γ''| #|Γ'| M) (lift #|Δ''| #|Δ'| N).
  Proof.
    intros wfΣ H.

    remember (Γ ,,, Γ') as Γ0.
    remember (Δ ,,, Δ') as Δ0.
    intros HΓ.
    revert Γ Γ' HeqΓ0 Δ Δ' HeqΔ0 HΓ Γ'' Δ''.
    revert Γ0 Δ0 M N H.

    set (Pctx :=
           fun (Γ0 Δ0 : context) =>
             forall Γ Γ' : context,
               Γ0 = Γ ,,, Γ' ->
               forall Δ Δ' : context,
                 Δ0 = Δ ,,, Δ' ->
                 #|Γ| = #|Δ| ->
           forall Γ'' Δ'' : context,
             All2_local_env_over (pred1 Σ) Γ Δ Γ'' Δ'' ->
             pred1_ctx Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (Δ ,,, Δ'' ,,, lift_context #|Δ''| 0 Δ')).

    refine (pred1_ind_all_ctx Σ _ Pctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; intros; subst Pctx;
      rename_all_hyps; try subst Γ Γ'; simplify_IH_hyps; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try specialize (forall_Γ _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try specialize (forall_Γ0 _ _ Γ'' eq_refl _ _ Δ'' eq_refl heq_length);
      try pose proof (All2_local_env_length X0);
      try specialize (X0 _ _ eq_refl _ _ eq_refl heq_length _ _ ltac:(eauto));
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel, id in *.

    - (* Contexts *)
      intros. subst.
      eapply All2_local_env_over_app. auto.
      eapply All2_local_env_over_app; pcuic.
      eapply All2_local_env_app in X0; auto.
      destruct X0.
      induction a0; rewrite ?lift_context_snoc0; cbn; constructor; pcuic.
      apply IHa0. now depelim predΓ'.
      rewrite !app_context_length in H |- *. lia.
      now rewrite !Nat.add_0_r.
      apply IHa0; auto. now depelim predΓ'.
      split; red; now rewrite !Nat.add_0_r.

    - (* Beta *)
      specialize (forall_Γ _ (Γ'0,, vass na t0) eq_refl _ (Δ' ,, vass na t1) eq_refl heq_length _ _ X5).
      specialize (forall_Γ1 _ _ eq_refl _ _ eq_refl heq_length _ _ X5).
      econstructor; now rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ1 _ (Γ'0,, vdef na d0 t0) eq_refl _ (Δ',, vdef na d1 t1)
                            eq_refl heq_length _ _ X5).
      simpl. econstructor; eauto.
      now rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ1.

    - (* Rel unfold *)
      assert(#|Γ''| = #|Δ''|). red in X1. pcuic.
      elim (leb_spec_Set); intros Hn.
      + destruct nth_error eqn:Heq; noconf heq_option_map.
        pose proof (nth_error_Some_length Heq).
        rewrite !app_context_length in H1.
        assert (#|Γ'0| = #|Δ'|). pcuic. eapply All2_local_env_app in X0 as [? ?].
        eapply All2_local_env_length in a0. now rewrite !lift_context_length in a0.
        rewrite !app_context_length; eauto.
        rewrite simpl_lift; try lia.
        rewrite - {2}H0.
        assert (#|Γ''| + S i = S (#|Γ''| + i)) as -> by lia.
        econstructor; auto.
        rewrite H0. rewrite <- weaken_nth_error_ge; auto. rewrite Heq.
        simpl in H. simpl. congruence.
        lia.

      + (* Local variable *)
        pose proof (All2_local_env_length predΓ'). rewrite !app_context_length in H0.
        rewrite <- lift_simpl; pcuic.
        econstructor; auto.
        rewrite (weaken_nth_error_lt); try lia.
        now rewrite option_map_decl_body_map_decl heq_option_map.

    - (* Rel refl *)
      pose proof (All2_local_env_length X0).
      assert(#|Γ''| = #|Δ''|). red in X1. pcuic.
      rewrite !app_context_length !lift_context_length in H.
      assert (#|Γ'0| = #|Δ'|) by lia. rewrite H1.
      elim (leb_spec_Set); intros Hn. rewrite H0. now econstructor.
      now constructor.

    - assert(#|Γ''| = #|Δ''|). red in X3; pcuic.
      pose proof (All2_local_env_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      rewrite lift_iota_red.
      autorewrite with lift.
      constructor; auto.
      apply All2_map. solve_all.
      apply All2_map. solve_all.

    - assert(#|Γ''| = #|Δ''|) by pcuic.
      pose proof (All2_local_env_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      unfold unfold_fix in heq_unfold_fix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_fix. simpl.
      econstructor; pcuic.
      rewrite !lift_fix_context.
      erewrite lift_fix_context.
      eapply All2_local_env_weaken_pred_ctx'; pcuic.
      apply All2_map. clear X4. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ ltac:(eauto)).
      rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
      now rewrite !lift_fix_context.
      unfold unfold_fix. rewrite nth_error_map. rewrite Hnth. simpl.
      destruct (isLambda (dbody d)) eqn:isl; noconf heq_unfold_fix.
      rewrite isLambda_lift //.
      f_equal. f_equal.
      rewrite distr_lift_subst. rewrite fix_subst_length. f_equal.
      now rewrite (map_fix_subst (fun k => lift #|Δ''| (k + #|Δ'|))).
      eapply All2_map. solve_all.

    - assert(#|Γ''| = #|Δ''|) by pcuic.
      pose proof (All2_local_env_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor; pcuic.
      rewrite !lift_fix_context.
      erewrite lift_fix_context.
      eapply All2_local_env_weaken_pred_ctx'; pcuic.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ1 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ1 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ ltac:(eauto)).
      rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ1.
      now rewrite !lift_fix_context.
      unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
      f_equal. f_equal.
      rewrite distr_lift_subst. rewrite cofix_subst_length. f_equal.
      now rewrite (map_cofix_subst (fun k => lift #|Δ''| (k + #|Δ'|))).
      eapply All2_map. solve_all.
      eapply All2_map. solve_all.

    - assert(#|Γ''| = #|Δ''|) by pcuic.
      pose proof (All2_local_env_length predΓ').
      rewrite !app_context_length in H0.
      assert (#|Γ'0| = #|Δ'|) by lia.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor; pcuic.
      rewrite !lift_fix_context.
      erewrite lift_fix_context.
      eapply All2_local_env_weaken_pred_ctx'; pcuic.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ ltac:(eauto)).
      rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
      now rewrite !lift_fix_context.
      unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
      f_equal. f_equal.
      rewrite distr_lift_subst. rewrite cofix_subst_length. f_equal.
      now rewrite (map_cofix_subst (fun k => lift #|Δ''| (k + #|Δ'|))).
      eapply All2_map. solve_all.

    - assert(Hlen:#|Γ''| = #|Δ''|). eapply All2_local_env_length in X1; pcuic.
      pose proof (lift_declared_constant _ _ _ #|Δ''| #|Δ'| wfΣ H).
      econstructor; eauto.
      rewrite H0.
      now rewrite - !map_cst_body heq_cst_body.

    - simpl. eapply pred_proj with (map (lift #|Δ''| #|Δ'|) args1). auto.
      eapply All2_map; solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 Γ0 (_ ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X3).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 Γ0 (_ ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X5).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ1.
      econstructor; eauto.

    - econstructor; pcuic.
      rewrite !lift_fix_context. revert X2.
      eapply All2_local_env_weaken_pred_ctx'; pcuic.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ _ _ eq_refl _ _ eq_refl heq_length _ _ X4).
      specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ X4).
      rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
      now rewrite !lift_fix_context.

    - econstructor; pcuic.
      rewrite !lift_fix_context. revert X2.
      eapply All2_local_env_weaken_pred_ctx'; pcuic.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ _ _ eq_refl _ _ eq_refl heq_length _ _ X4).
      specialize (forall_Γ0 Γ0 (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 Δ (Δ' ,,, fix_context mfix1)
                            ltac:(now rewrite app_context_assoc) heq_length _ _ X4).
      rewrite !lift_context_app !Nat.add_0_r !app_context_length !fix_context_length
              !app_context_assoc in forall_Γ0.
      now rewrite !lift_fix_context.

    - specialize (forall_Γ0 Γ0 (Γ'0 ,, _) eq_refl _ (_ ,, _) eq_refl heq_length _ _ X3).
      rewrite !lift_context_snoc0 !Nat.add_0_r in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Lemma weakening_pred1_pred1 Σ Γ Δ Γ' Δ' M N : wf Σ ->
    All2_local_env_over (pred1 Σ) Γ Δ Γ' Δ' ->
    pred1 Σ Γ Δ M N ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Δ') (lift0 #|Γ'| M) (lift0 #|Δ'| N).
  Proof.
    intros; apply (weakening_pred1 Σ Γ [] Γ' Δ [] Δ' M N); eauto.
    eapply pred1_pred1_ctx in X1. pcuic.
  Qed.

  Lemma weakening_pred1_0 Σ Γ Δ Γ' M N : wf Σ ->
    pred1 Σ Γ Δ M N ->
    pred1 Σ (Γ ,,, Γ') (Δ ,,, Γ') (lift0 #|Γ'| M) (lift0 #|Γ'| N).
  Proof.
    intros; apply (weakening_pred1 Σ Γ [] Γ' Δ [] Γ' M N); eauto.
    eapply pred1_pred1_ctx in X0. pcuic.
    eapply pred1_pred1_ctx in X0.
    apply All2_local_env_over_refl; auto.
  Qed.

  Lemma All2_local_env_over_pred1_ctx Σ Γ Γ' Δ Δ' :
    #|Δ| = #|Δ'| ->
    pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ') ->
    All2_local_env
      (on_decl (on_decl_over (pred1 Σ) Γ Γ')) Δ Δ'.
  Proof.
    intros. pose proof (All2_local_env_length X).
    apply All2_local_env_app in X.
    intuition. auto. rewrite !app_context_length in H0. pcuic.
  Qed.
  Hint Resolve All2_local_env_over_pred1_ctx : pcuic.

  Lemma nth_error_pred1_ctx_all_defs {P} {Γ Δ} :
    All2_local_env (on_decl P) Γ Δ ->
    forall i body body', option_map decl_body (nth_error Γ i) = Some (Some body) ->
              option_map decl_body (nth_error Δ i) = Some (Some body') ->
              P (skipn (S i) Γ) (skipn (S i) Δ) body body'.
  Proof.
    induction 1; destruct i; simpl; try discriminate.
    intros. apply IHX; auto.
    intros ? ? [= ->] [= ->]. apply p.
    intros ? ? ? ?. apply IHX; auto.
  Qed.

  Lemma All2_local_env_over_firstn_skipn:
    forall (Σ : global_env) (i : nat) (Δ' R : context),
      pred1_ctx Σ Δ' R ->
      All2_local_env_over (pred1 Σ) (skipn i Δ') (skipn i R) (firstn i Δ') (firstn i R).
  Proof.
    intros Σ i Δ' R redr.
    induction redr in i |- *; simpl.
    destruct i; constructor; pcuic.
    destruct i; simpl; constructor; pcuic. apply IHredr.
    repeat red. now rewrite /app_context !firstn_skipn.
    repeat red. red in p.
    destruct i; simpl; constructor; pcuic. apply IHredr.
    repeat red. destruct p.
    split; red; now rewrite /app_context !firstn_skipn.
  Qed.

End ParallelWeakening.

Hint Resolve pred1_pred1_ctx : pcuic.

Section ParallelSubstitution.
  Context {cf : checker_flags}.

  Inductive psubst Σ (Γ Γ' : context) : list term -> list term -> context -> context -> Type :=
  | psubst_empty : psubst Σ Γ Γ' [] [] [] []
  | psubst_vass Δ Δ' s s' na na' t t' T T' :
      psubst Σ Γ Γ' s s' Δ Δ' ->
      pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') T T' ->
      pred1 Σ Γ Γ' t t' ->
      psubst Σ Γ Γ' (t :: s) (t' :: s') (Δ ,, vass na T) (Δ' ,, vass na' T')
  | psubst_vdef Δ Δ' s s' na na' t t' T T' :
      psubst Σ Γ Γ' s s' Δ Δ' ->
      pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') T T' ->
      pred1 Σ Γ Γ' (subst0 s t) (subst0 s' t') ->
      psubst Σ Γ Γ' (subst0 s t :: s) (subst0 s' t' :: s') (Δ ,, vdef na t T) (Δ' ,, vdef na' t' T').

  Lemma psubst_length {Σ Γ Δ Γ' Δ' s s'} : psubst Σ Γ Δ s s' Γ' Δ' ->
                                           #|s| = #|Γ'| /\ #|s'| = #|Δ'| /\ #|s| = #|s'|.
  Proof.
    induction 1; simpl; intuition auto with arith.
  Qed.

  Lemma psubst_length' {Σ Γ Δ Γ' Δ' s s'} : psubst Σ Γ Δ s s' Γ' Δ' -> #|s'| = #|Γ'|.
  Proof.
    induction 1; simpl; auto with arith.
  Qed.

  Lemma psubst_nth_error Σ Γ Δ Γ' Δ' s s' n t :
    psubst Σ Γ Δ s s' Γ' Δ' ->
    nth_error s n = Some t ->
    ∑ decl decl' t',
      (nth_error Γ' n = Some decl) *
      (nth_error Δ' n = Some decl') *
      (nth_error s' n = Some t') *
    match decl_body decl, decl_body decl' with
    | Some d, Some d' =>
        let s2 := (skipn (S n) s) in
        let s2' := (skipn (S n) s') in
      let b := subst0 s2 d in
      let b' := subst0 s2' d' in
      psubst Σ Γ Δ s2 s2' (skipn (S n) Γ') (skipn (S n) Δ') *
      (t = b) * (t' = b') * pred1 Σ Γ Δ t t'
    | None, None => pred1 Σ Γ Δ t t'
    | _, _ => False
    end.
  Proof.
    induction 1 in n, t |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists (vass na T), (vass na' T'), t'. intuition auto.
    - intros.
      specialize (IHX _ _ H). intuition eauto.
    - intros [= <-]. exists (vdef na t0 T), (vdef na' t' T'), (subst0 s' t'). intuition auto.
      simpl. intuition simpl; auto.
    - apply IHX.
  Qed.

  Lemma psubst_nth_error' Σ Γ Δ Γ' Δ' s s' n t :
    psubst Σ Γ Δ s s' Γ' Δ' ->
    nth_error s n = Some t ->
    ∑ t',
      (nth_error s' n = Some t') *
      pred1 Σ Γ Δ t t'.
  Proof.
    induction 1 in n, t |- *; simpl; auto; destruct n; simpl; try congruence.
    - intros [= <-]. exists t'; intuition auto.
    - intros.
      specialize (IHX _ _ H). intuition eauto.
    - intros [= <-]. exists (subst0 s' t'). intuition auto.
    - apply IHX.
  Qed.

  Lemma psubst_nth_error_None Σ Γ Δ Γ' Δ' s s' n :
    psubst Σ Γ Δ s s' Γ' Δ' ->
    nth_error s n = None ->
    (nth_error Γ' n = None) * (nth_error Δ' n = None)* (nth_error s' n = None).
  Proof.
    induction 1 in n |- *; simpl; auto; destruct n; simpl; intros; intuition try congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
    - specialize (IHX _ H). intuition congruence.
  Qed.

  Lemma subst_skipn' n s k t : k < n -> (n - k) <= #|s| ->
    lift0 k (subst0 (skipn (n - k) s) t) = subst s k (lift0 n t).
  Proof.
    intros Hk Hn.
    assert (#|firstn (n - k) s| = n - k) by (rewrite firstn_length_le; lia).
    assert (k + (n - k) = n) by lia.
    assert (n - k + k = n) by lia.
    rewrite <- (firstn_skipn (n - k) s) at 2.
    rewrite subst_app_simpl. rewrite H H0.
    rewrite <- (commut_lift_subst_rec t _ n 0 0); try lia.
    generalize (subst0 (skipn (n - k) s) t). intros.
    erewrite <- (simpl_subst_rec _ (firstn (n - k) s) _ k); try lia.
    now rewrite H H1.
  Qed.

  Lemma split_app3 {A} (l l' l'' : list A) (l1 l1' l1'' : list A) :
    #|l| = #|l1| -> #|l'| = #|l1'| ->
        l ++ l' ++ l'' = l1 ++ l1' ++ l1'' ->
        l = l1 /\ l' = l1' /\ l'' = l1''.
  Proof.
    intros.
    eapply app_inj_length_l in H1 as [Hl Hr]; auto.
    eapply app_inj_length_l in Hr as [Hl' Hr]; auto.
  Qed.

  Lemma All2_local_env_subst_ctx :
    forall (Σ : global_env) c c0 (Γ0 Δ : context)
    (Γ'0 : list context_decl) (Γ1 Δ1 : context) (Γ'1 : list context_decl) (s s' : list term),
      psubst Σ Γ0 Γ1 s s' Δ Δ1 ->
      #|Γ'0| = #|Γ'1| ->
      #|Γ0| = #|Γ1| ->
      All2_local_env_over (pred1 Σ) Γ0 Γ1 Δ Δ1 ->
     All2_local_env
      (on_decl
       (on_decl_over
          (fun (Γ Γ' : context) (t t0 : term) =>
           forall (Γ2 Δ0 : context) (Γ'2 : list context_decl),
           Γ = Γ2 ,,, Δ0 ,,, Γ'2 ->
           forall (Γ3 Δ2 : context) (Γ'3 : list context_decl) (s0 s'0 : list term),
           psubst Σ Γ2 Γ3 s0 s'0 Δ0 Δ2 ->
           Γ' = Γ3 ,,, Δ2 ,,, Γ'3 ->
           #|Γ2| = #|Γ3| ->
           #|Γ'2| = #|Γ'3| ->
           All2_local_env_over (pred1 Σ) Γ2 Γ3 Δ0 Δ2 ->
           pred1 Σ (Γ2 ,,, subst_context s0 0 Γ'2) (Γ3 ,,, subst_context s'0 0 Γ'3) (subst s0 #|Γ'2| t)
             (subst s'0 #|Γ'3| t0)) (Γ0 ,,, Δ ,,, Γ'0) (Γ1 ,,, Δ1 ,,, Γ'1))) c c0 ->
  All2_local_env (on_decl (on_decl_over (pred1 Σ) (Γ0 ,,, subst_context s 0 Γ'0) (Γ1 ,,, subst_context s' 0 Γ'1)))
    (subst_context s #|Γ'0| c) (subst_context s' #|Γ'1| c0).
  Proof.
    intros.
    pose proof (All2_local_env_length X1).
    induction X1; simpl; rewrite ?subst_context_snoc; constructor; auto; rename_all_hyps.
    - red in p. red in p. rename_all_hyps.
      specialize (forall_Γ2 _ _ (Γ'0 ,,, Γ)
                 ltac:(now rewrite app_context_assoc) _ _ (Γ'1,,, Γ') _ _ X
                 ltac:(now rewrite app_context_assoc) heq_length0
                 ltac:(now rewrite !app_context_length; auto) X0).
      simpl in *.
      rewrite !subst_context_app !app_context_length !app_context_assoc !Nat.add_0_r in forall_Γ2.
      simpl. red.
      congruence.
    - destruct p. red in o, o0.
      specialize (o _ _ (Γ'0 ,,, Γ)
                 ltac:(now rewrite app_context_assoc) _ _ (Γ'1,,, Γ') _ _ X
                 ltac:(now rewrite app_context_assoc) heq_length0
                 ltac:(now rewrite !app_context_length; auto) X0).
      specialize (o0 _ _ (Γ'0 ,,, Γ)
                 ltac:(now rewrite app_context_assoc) _ _ (Γ'1,,, Γ') _ _ X
                 ltac:(now rewrite app_context_assoc) heq_length0
                 ltac:(now rewrite !app_context_length; auto) X0).
      simpl in *.
      unfold on_decl_over.
      rewrite !subst_context_app !app_context_length !app_context_assoc !Nat.add_0_r in o, o0.
      simpl in *. split; congruence.
  Qed.

  (** Parallel reduction is substitutive. *)
  Lemma substitution_let_pred1 Σ Γ Δ Γ' Γ1 Δ1 Γ'1 s s' M N : wf Σ ->
    psubst Σ Γ Γ1 s s' Δ Δ1 ->
    #|Γ| = #|Γ1| -> #|Γ'| = #|Γ'1| ->
    All2_local_env_over (pred1 Σ) Γ Γ1 Δ Δ1 ->
    pred1 Σ (Γ ,,, Δ ,,, Γ') (Γ1 ,,, Δ1 ,,, Γ'1) M N ->
    pred1 Σ (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1) (subst s #|Γ'| M) (subst s' #|Γ'1| N).
  Proof.
    intros wfΣ Hs.
    remember (Γ ,,, Δ ,,, Γ') as Γl.
    remember (Γ1 ,,, Δ1 ,,, Γ'1) as Γr.
    intros Hlen Hlen' HΔ HΓ.
    revert HeqΓl Γ1 Δ1 Γ'1 s s' Hs HeqΓr Hlen Hlen' HΔ.
    revert Γ Δ Γ'.
    revert Γl Γr M N HΓ.
    set(P' :=
          fun (Γl Γr : context) =>
            forall (Γ Δ : context) (Γ' : list context_decl),
              Γl = Γ ,,, Δ ,,, Γ' ->
              forall (Γ1 : list context_decl) (Δ1 : context) (Γ'1 : list context_decl) (s s' : list term),
                psubst Σ Γ Γ1 s s' Δ Δ1 ->
                Γr = Γ1 ,,, Δ1 ,,, Γ'1 ->
                #|Γ| = #|Γ1| ->
               All2_local_env_over (pred1 Σ) Γ Γ1 Δ Δ1 ->
               pred1_ctx Σ (Γ ,,, subst_context s 0 Γ') (Γ1 ,,, subst_context s' 0 Γ'1)).
    refine (pred1_ind_all_ctx Σ _ P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros *; !intros;
      try subst Γ Γ'; simplify_IH_hyps; cbn -[iota_red];
      match goal with
        |- context [iota_red _ _ _ _] => idtac
      | |- _ => autorewrite with lift
      end;
      try specialize (forall_Γ _ _ _ eq_refl _ _ _
                               _ _ Hs eq_refl heq_length heq_length0 HΔ);
    try specialize (forall_Γ0 _ _ _ eq_refl _ _ _
                              _ _ Hs eq_refl heq_length heq_length0 HΔ);
    try specialize (forall_Γ1 _ _ _ eq_refl _ _ _
                           _ _ Hs eq_refl heq_length heq_length0 HΔ);
      try pose proof (All2_local_env_length X0);
      simpl; try solve [ econstructor; eauto; try apply All2_map;
                         unfold All2_prop_eq, All2_prop, on_Trel, id in *; solve_all];
        unfold All2_prop_eq, All2_prop, on_Trel, id in *.

    - (* Contexts *)
      red. intros. subst.
      pose proof (All2_local_env_length X1).
      rewrite !app_context_length in H |- *.
      assert (#|Γ'0| = #|Γ'1|) by lia.
      eapply All2_local_env_over_app. eapply All2_local_env_app in predΓ'.
      subst P'. intuition auto. typeclasses eauto with pcuic.
      now rewrite !app_context_length.
      eapply All2_local_env_app in X0 as [Xl Xr].
      2:{ rewrite !app_context_length. lia. }
      induction Xr; rewrite ?subst_context_snoc; constructor; pcuic. apply IHXr.
      + depelim predΓ'. auto.
      + depelim predΓ'. auto.
      + simpl in *. lia.
      + simpl in *.
        repeat red. rewrite !Nat.add_0_r. eapply p; eauto.
      + depelim predΓ'. auto.
        simpl in *.
        repeat red. apply IHXr. simpl in *. pcuic. lia. lia.
      + depelim predΓ'. auto.
        simpl in *. destruct p.
        split; repeat red.
        rewrite !Nat.add_0_r. simpl. eapply p; eauto.
        rewrite !Nat.add_0_r. simpl. eapply p0; eauto.

    - (* Beta *)
      specialize (forall_Γ _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                           _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite distr_subst. simpl.
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ.

    - (* Zeta *)
      specialize (forall_Γ1 _ _  (_ ,, _) eq_refl _ _ (_ ,, _)
                            _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      simpl. rewrite distr_subst.
      econstructor; now rewrite !subst_context_snoc0 in forall_Γ1.

    - (* Rel *)
      pose proof (psubst_length Hs) as Hlens.
      elim (leb_spec_Set); intros Hn.
      red in X0. specialize (X0 _ _ _ eq_refl _ _ _ _ _ Hs eq_refl heq_length HΔ).
      destruct (nth_error s) eqn:Heq.
      ++ (* Let-bound variable in the substitution *)
         pose proof (nth_error_Some_length Heq).
         pose proof predΓ' as X.
         eapply psubst_nth_error in Heq as [decl [decl' [t' ?]]]; eauto.
         intuition; rename_all_hyps.
         destruct decl as [? [?|] ?]; destruct decl' as [? [?|] ?]; simpl in b; try contradiction.
         intuition subst.
         revert heq_option_map.
         rewrite -> nth_error_app_context_ge by lia.
         pose proof (nth_error_Some_length heq_nth_error1).
         rewrite -> nth_error_app_context_lt by lia.
         rewrite - heq_length0 heq_nth_error1 => [= <-].
         eapply weakening_pred1_pred1 in b0. 2:eauto. 2:eapply All2_local_env_app. 2:eapply X0.
         rewrite !subst_context_length in b0.
         rewrite <- subst_skipn'; try lia.
         now replace (S i - #|Γ'0|) with (S (i - #|Γ'0|)) by lia. lia.
         revert heq_option_map.
         rewrite -> nth_error_app_context_ge by lia.
         pose proof (nth_error_Some_length heq_nth_error1).
         rewrite -> nth_error_app_context_lt by lia.
         rewrite - heq_length0 heq_nth_error1. simpl. congruence.

      ++ pose proof (psubst_length Hs).
         assert (#|Δ1| = #|s|).
         eapply psubst_nth_error_None in Hs; eauto. lia.
         eapply nth_error_None in Heq.
         subst P'.
         intuition; rename_all_hyps.
         (* Rel is a let-bound variable in Γ0, only weakening needed *)
         assert(eq:S i = #|s| + (S (i - #|s|))) by (lia). rewrite eq.
         rewrite simpl_subst'; try lia.
         econstructor. eauto.
         rewrite nth_error_app_context_ge !subst_context_length /=; try lia.
         rewrite <- heq_option_map. f_equal.
         rewrite nth_error_app_context_ge /=; try lia.
         rewrite nth_error_app_context_ge /=; try lia.
         f_equal. lia.

      ++ (* Local variable from Γ'0 *)
         assert(eq: #|Γ'1| = #|Γ'1| - S i + S i) by lia. rewrite eq.
         rewrite <- (commut_lift_subst_rec body s' (S i) (#|Γ'1| - S i) 0); try lia.
         econstructor. eauto.
         rewrite nth_error_app_context_lt /= in heq_option_map. autorewrite with wf; lia.
         rewrite nth_error_app_context_lt; try (autorewrite with wf; lia).
         rewrite nth_error_subst_context. rewrite option_map_decl_body_map_decl heq_option_map.
         simpl. do 3 f_equal. lia.

    - specialize (X0 _ _ _ eq_refl _ _ _ _ _ Hs eq_refl heq_length HΔ).
      rewrite {1}heq_length0. elim (leb_spec_Set); intros Hn.
      + subst P'. intuition; subst; rename_all_hyps.
        pose proof (psubst_length Hs).
        destruct nth_error eqn:Heq.
        ++ eapply psubst_nth_error' in Heq as [t' [? ?]]; eauto.
           rewrite - heq_length0 e.
           rewrite - {1}(subst_context_length s 0 Γ'0).
           rewrite {1}heq_length0 -(subst_context_length s' 0 Γ'1).
           eapply weakening_pred1_pred1; auto. eapply All2_local_env_over_pred1_ctx.
           now rewrite !subst_context_length. auto.
        ++ eapply psubst_nth_error_None in Heq; eauto.
           intuition; rename_all_hyps.
           rewrite - heq_length0 heq_nth_error.
           eapply psubst_length' in Hs.
           assert(#|s| = #|s'|) as -> by lia.
           eauto with pcuic.
      + constructor. auto.

    - rewrite subst_iota_red.
      autorewrite with subst.
      econstructor. eauto.
      apply All2_map. solve_all. unfold on_Trel. solve_all.

    - autorewrite with subst. simpl.
      unfold unfold_fix in heq_unfold_fix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_fix.
      destruct (isLambda (dbody d)) eqn:isl; noconf heq_unfold_fix.
      econstructor; auto with pcuic. eapply X0; eauto with pcuic.
      rewrite !subst_fix_context.
      erewrite subst_fix_context.
      eapply All2_local_env_subst_ctx; pcuic.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ0 _ _ (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 _ _ (Γ'1 ,,, fix_context mfix1) _ _ Hs
                            ltac:(now rewrite app_context_assoc) heq_length).
      rewrite !app_context_length
        in forall_Γ0. pose proof (All2_local_env_length X1).
      forward forall_Γ0. lia. specialize (forall_Γ0 HΔ).
      rewrite !subst_fix_context.
      now rewrite !fix_context_length !subst_context_app
          !Nat.add_0_r !app_context_assoc in forall_Γ0.
      unfold unfold_fix. rewrite nth_error_map. rewrite Hnth. simpl.
      rewrite isLambda_subst //.
      f_equal. f_equal.
      rewrite (map_fix_subst (fun k => subst s' (k + #|Γ'1|))).
      intros. reflexivity. simpl.
      now rewrite (distr_subst_rec _ _ _ _ 0) fix_subst_length.
      apply subst_is_constructor; auto.
      eapply All2_map. solve_all.

    - autorewrite with subst. simpl.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor; pcuic.
      rewrite !subst_fix_context.
      erewrite subst_fix_context.
      eapply All2_local_env_subst_ctx; pcuic.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ1 _ _ (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ1 _ _ (Γ'1 ,,, fix_context mfix1) _ _ Hs
                            ltac:(now rewrite app_context_assoc) heq_length).
      rewrite !app_context_length
        in forall_Γ1. pose proof (All2_local_env_length X1).
      forward forall_Γ1. lia. specialize (forall_Γ1 HΔ).
      rewrite !subst_fix_context.
      now rewrite !fix_context_length !subst_context_app
          !Nat.add_0_r !app_context_assoc in forall_Γ1.
      unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
      f_equal. f_equal.
      rewrite (map_cofix_subst (fun k => subst s' (k + #|Γ'1|))).
      intros. reflexivity. simpl.
      now rewrite (distr_subst_rec _ _ _ _ 0) cofix_subst_length.

      eapply All2_map. solve_all.
      eapply All2_map. solve_all.

    - autorewrite with subst. simpl.
      unfold unfold_cofix in heq_unfold_cofix.
      destruct (nth_error mfix1 idx) eqn:Hnth; noconf heq_unfold_cofix. simpl.
      econstructor. red in X0. eauto 1 with pcuic. unshelve eapply X0.
      shelve. shelve. eauto. eauto. eauto.
      eauto. eauto.
      pcuic.
      rewrite !subst_fix_context.
      erewrite subst_fix_context.
      eapply All2_local_env_subst_ctx. eapply Hs. auto. auto. auto.
      eapply X2.
      apply All2_map. clear X2. red in X3.
      unfold on_Trel, id in *.
      solve_all. rename_all_hyps.
      specialize (forall_Γ0 _ _ (Γ'0 ,,, fix_context mfix0)
                            ltac:(now rewrite app_context_assoc)).
      specialize (forall_Γ0 _ _ (Γ'1 ,,, fix_context mfix1) _ _ Hs
                            ltac:(now rewrite app_context_assoc) heq_length).
      rewrite !app_context_length in forall_Γ0. pose proof (All2_local_env_length X1).
      forward forall_Γ0. lia. specialize (forall_Γ0 HΔ).
      rewrite !subst_fix_context.
      now rewrite !fix_context_length !subst_context_app
          !Nat.add_0_r !app_context_assoc in forall_Γ0.
      unfold unfold_cofix. rewrite nth_error_map. rewrite Hnth. simpl.
      f_equal. f_equal.
      rewrite (map_cofix_subst (fun k => subst s' (k + #|Γ'1|))).
      intros. reflexivity. simpl.
      now rewrite (distr_subst_rec _ _ _ _ 0) cofix_subst_length.
      eapply All2_map. solve_all.

    - pose proof (subst_declared_constant _ _ _ s' #|Γ'0| u wfΣ H).
      apply (f_equal cst_body) in H0.
      rewrite <- !map_cst_body in H0. rewrite heq_cst_body in H0. simpl in H0.
      noconf H0. simpl in H0. rewrite heq_length0 in H0. rewrite H0.
      econstructor; eauto.

    - autorewrite with subst. simpl.
      econstructor; eauto.
      eapply All2_map. solve_all.
      now rewrite nth_error_map heq_nth_error.

    - specialize (forall_Γ0 _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                           _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite !subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - specialize (forall_Γ1 _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                           _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite !subst_context_snoc0 in forall_Γ1.
      econstructor; eauto.

    - econstructor; eauto.
      { rewrite !subst_fix_context. eapply All2_local_env_subst_ctx; eauto. }
      apply All2_map. red in X0. unfold on_Trel, id in *.
      pose proof (All2_length _ _ X3).
      eapply All2_impl; eauto. simpl. intros.
      destruct X. destruct o, p. destruct p. rename_all_hyps.
      specialize (forall_Γ1 _ _ (_ ,,, fix_context mfix0) ltac:(now rewrite - app_context_assoc)
      _ _ (_ ,,, fix_context mfix1) _ _ Hs ltac:(now rewrite - app_context_assoc) heq_length).
      rewrite !app_context_length !fix_context_length in forall_Γ1. forward forall_Γ1 by lia.
      specialize (forall_Γ1 HΔ).
      specialize (forall_Γ0 _ _ _ eq_refl _ _ _
                            _ _ Hs eq_refl heq_length heq_length0 HΔ).
      rewrite subst_context_app Nat.add_0_r ?app_context_length ?fix_context_length
              ?app_context_assoc in forall_Γ1. auto.
      split; eauto.
      rewrite !subst_fix_context. split; eauto.
      rewrite subst_context_app Nat.add_0_r
              app_context_assoc in forall_Γ1. auto.

    - econstructor; eauto.
      { rewrite !subst_fix_context. eapply All2_local_env_subst_ctx; eauto. }
      apply All2_map. red in X0. unfold on_Trel, id in *.
      pose proof (All2_length _ _ X3).
      eapply All2_impl; eauto. simpl. intros.
      destruct X. destruct o, p. destruct p. rename_all_hyps.
      specialize (forall_Γ1 _ _ (_ ,,, fix_context mfix0) ltac:(now rewrite - app_context_assoc)
      _ _ (_ ,,, fix_context mfix1) _ _ Hs ltac:(now rewrite - app_context_assoc) heq_length).
      rewrite !app_context_length !fix_context_length in forall_Γ1. forward forall_Γ1 by lia.
      specialize (forall_Γ1 HΔ).
      specialize (forall_Γ0 _ _ _ eq_refl _ _ _
                            _ _ Hs eq_refl heq_length heq_length0 HΔ).
      rewrite subst_context_app Nat.add_0_r ?app_context_length ?fix_context_length
              ?app_context_assoc in forall_Γ1. auto.
      split; eauto.
      rewrite !subst_fix_context. split; eauto.
      rewrite subst_context_app Nat.add_0_r
              app_context_assoc in forall_Γ1. auto.

    - specialize (forall_Γ0 _ _ (_ ,, _) eq_refl _ _ (_ ,, _)
                              _ _ Hs eq_refl heq_length (f_equal S heq_length0) HΔ).
      rewrite !subst_context_snoc0 in forall_Γ0.
      econstructor; eauto.

    - revert H. induction t; intros; try discriminate; try solve [ constructor; simpl; eauto ];
                  try solve [ apply (pred_atom); auto ].
  Qed.

  Hint Constructors psubst : pcuic.
  Hint Transparent vass vdef : pcuic.

  Lemma substitution0_pred1 {Σ : global_env} {Γ Δ M M' na na' A A' N N'} :
    wf Σ ->
    pred1 Σ Γ Δ M M' ->
    pred1 Σ (Γ ,, vass na A) (Δ ,, vass na' A') N N' ->
    pred1 Σ Γ Δ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redM redN.
    pose proof (substitution_let_pred1 Σ Γ [vass na A] [] Δ [vass na' A'] [] [M] [M'] N N' wfΣ) as H.
    forward H. constructor; auto with pcuic.
    forward H by pcuic. constructor; pcuic. apply pred1_pred1_ctx in redN. depelim redN; pcuic.
    simpl in H |- *. apply pred1_pred1_ctx in redN; pcuic. depelim redN; pcuic.
    pose proof (pred1_pred1_ctx _ redN). depelim X.
    apply H; pcuic. auto. constructor; pcuic.
  Qed.

  Lemma substitution0_let_pred1 {Σ Γ Δ na na' M M' A A' N N'} : wf Σ ->
    pred1 Σ Γ Δ M M' ->
    pred1 Σ (Γ ,, vdef na M A) (Δ ,, vdef na' M' A') N N' ->
    pred1 Σ Γ Δ (subst1 M 0 N) (subst1 M' 0 N').
  Proof.
    intros wfΣ redM redN.
    pose proof (substitution_let_pred1 Σ Γ [vdef na M A] [] Δ [vdef na' M' A'] [] [M] [M'] N N' wfΣ) as H.
    pose proof (pred1_pred1_ctx _ redN). depelim X. simpl in o.
    forward H. pose proof (psubst_vdef Σ Γ Δ [] [] [] [] na na' M M' A A').
    rewrite !subst_empty in X0. apply X0; pcuic. apply H; pcuic.
    econstructor; auto with pcuic.
  Qed.

End ParallelSubstitution.
